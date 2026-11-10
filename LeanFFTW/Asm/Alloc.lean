/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.VIR

/-!
# Register allocation and instruction selection for straight-line vector code

`allocBlock` turns a `VBlock` into instructions over the 32 vector registers.

* Loads and constants are *lazy*: a load used at most `foldLimit` times becomes the memory
  operand of the instructions that use it (one fused micro-operation each), and is never
  copied into a register. Loads are forced into registers before the next store of the
  block, so a load is never moved across a store.
* Fused multiply-adds overwrite one operand; the encoding (`132`, `213`, `231`) is chosen so
  that the operand overwritten is one that is used for the last time, and a register copy is
  made only when no operand dies.
* When no register is free, the value whose next use is furthest away is evicted (Belady's
  rule, which is optimal for straight-line code); values that can be reread from memory
  or the constant pool are dropped without a store.

Nothing here is trusted: the instructions produced are checked against the block by
symbolic execution (`LeanFFTW/Asm/Check.lean`).
-/

namespace LeanFFTW.Asm

open Std

structure ACfg where
  w : W
  /-- allocatable registers, most preferred first -/
  regs : Array VReg
  /-- values held in fixed registers for the whole function (not in `regs`) -/
  pinned : HashMap VId VReg := {}
  /-- a load with at most this many uses is used as a memory operand -/
  foldLimit : Nat := 2
  /-- byte offset from `rsp` of the first spill slot -/
  slotBase : Nat := 0
  /-- instruction order: `0` as written; `1` the shortest of the written order and the four
  reorderings of `VBlock.schedule`; `2 + k` reordering `k` -/
  sched : Nat := 1

structure AState where
  out : Array Instr := #[]
  regOf : HashMap VId VReg := {}
  holder : HashMap Nat VId := {}
  slotOf : HashMap VId Nat := {}
  freeSlots : List Nat := []
  /-- slots of values that died in the statement being translated: the statement may still
  read them (a memory operand), so they are reused only from the next statement on -/
  dyingSlots : List Nat := []
  nSlots : Nat := 0
  pool : Pool := {}
  /-- values that can be reread: loads (until the next store) and constants -/
  remat : HashMap VId VOp := {}
  /-- remaining use positions, ascending -/
  usesLeft : HashMap VId (List Nat) := {}
  /-- bit `n` set: register `n` was written -/
  touched : Nat := 0
  /-- values with a use that cannot take a memory operand -/
  noFold : HashMap VId Unit := {}

abbrev AM := ReaderT ACfg (StateT AState (Except String))

namespace AM

def emit (i : Instr) : AM Unit := modify fun s => { s with out := s.out.push i }

def regOf? (v : VId) : AM (Option VReg) := do
  match (← read).pinned[v]? with
  | some r => return some r
  | none => return (← get).regOf[v]?

def isPinned (v : VId) : AM Bool := return (← read).pinned.contains v

def remaining (v : VId) : AM Nat := return (((← get).usesLeft[v]?).getD []).length

def nextUse (v : VId) : AM Nat := do
  match (← get).usesLeft[v]? with
  | some (p :: _) => return p
  | _ => return 1000000000

/-- Spill slot `i` (64 bytes each, above the integer slots of the frame). -/
def slotMem (i : Nat) : AM Mem := return Mem.b .rsp ((← read).slotBase + 64 * i)

def bind (v : VId) (r : VReg) : AM Unit :=
  modify fun s => { s with regOf := s.regOf.insert v r, holder := s.holder.insert r.n v,
                           touched := s.touched ||| (1 <<< r.n) }

/-- Remove the value held by `r`, saving it to a spill slot if it cannot be reread. -/
def evict (r : VReg) : AM Unit := do
  let s ← get
  let some v := s.holder[r.n]? | return
  if !s.remat.contains v && !s.slotOf.contains v then
    let (slot, s) := match s.freeSlots with
      | i :: rest => (i, { s with freeSlots := rest })
      | [] => (s.nSlots, { s with nSlots := s.nSlots + 1 })
    set { s with out := s.out.push (.vstore (← read).w (← slotMem slot) r),
                 slotOf := s.slotOf.insert v slot }
  modify fun s => { s with holder := s.holder.erase r.n, regOf := s.regOf.erase v }

/-- A register not in `avoid`: a free one, or the one whose value is needed last. -/
def pickReg (avoid : List VReg) : AM VReg := do
  let c ← read
  let s ← get
  for r in c.regs do
    if !s.holder.contains r.n && !avoid.contains r then
      modify fun s => { s with touched := s.touched ||| (1 <<< r.n) }
      return r
  let mut best : Option (VReg × Nat × Bool) := none
  for r in c.regs do
    if avoid.contains r then continue
    let some v := s.holder[r.n]? | continue
    let nu ← nextUse v
    let cheap := s.remat.contains v || s.slotOf.contains v
    let better := match best with
      | none => true
      | some (_, bn, bc) => nu > bn || (nu == bn && cheap && !bc)
    if better then best := some (r, nu, cheap)
  match best with
  | some (r, _, _) => evict r; return r
  | none => throw "register allocation: no register available"

def quadLabel (bits : UInt64) : AM String := do
  let s ← get
  let (l, p) := s.pool.quad bits
  set { s with pool := p }
  return l

def vecLabel (bits : Array UInt64) : AM String := do
  let s ← get
  let (l, p) := s.pool.vec bits
  set { s with pool := p }
  return l

/-- Memory operand of a broadcast constant: embedded broadcast for `zmm`, a full-width
constant otherwise (VEX encodings have no broadcast). -/
def bcastSrc (bits : UInt64) : AM VSrc := do
  let w := (← read).w
  if w == .z then return .bcst (Mem.rip (← quadLabel bits))
  else return .mem (Mem.rip (← vecLabel (Array.replicate w.lanes bits)))

/-- Bring a value into a register. -/
def materialize (v : VId) (avoid : List VReg) : AM VReg := do
  if let some r ← regOf? v then return r
  let r ← pickReg avoid
  let c ← read
  let s ← get
  match s.slotOf[v]? with
  | some i => emit (.vmov c.w r (.mem (← slotMem i)))
  | none =>
    match s.remat[v]? with
    | some (.load m) => emit (.vmov c.w r (.mem m))
    | some (.loadz k m) => emit (.vloadz c.w r k m)
    | some (.bcast bits) => emit (.vmov c.w r (.bcst (Mem.rip (← quadLabel bits))))
    | some (.cvec bits) => emit (.vmov c.w r (.mem (Mem.rip (← vecLabel bits))))
    | some .zero => emit (.vzero r)
    | _ => throw s!"register allocation: value {v} used before its definition"
  bind v r
  return r

/-- The value as a memory operand, if it is not in a register and can be read from memory. -/
def memSrc? (v : VId) : AM (Option VSrc) := do
  if (← regOf? v).isSome then return none
  let c ← read
  let s ← get
  if let some i := s.slotOf[v]? then return some (.mem (← slotMem i))
  match s.remat[v]? with
  | some (.load m) =>
      if (← remaining v) ≤ c.foldLimit && !s.noFold.contains v then return some (.mem m)
      else return none
  | some (.bcast bits) => return some (← bcastSrc bits)
  | some (.cvec bits) => return some (.mem (Mem.rip (← vecLabel bits)))
  | _ => return none

/-- A source operand: memory if possible, else a register. -/
def src (v : VId) (avoid : List VReg) : AM VSrc := do
  match ← memSrc? v with
  | some m => return m
  | none => return .reg (← materialize v avoid)

def srcRegs : VSrc → List VReg
  | .reg r => [r]
  | _ => []

/-- Mark position `pos` of the values `vs` as used. -/
def consume (vs : List VId) (pos : Nat) : AM Unit :=
  modify fun s =>
    let step (m : HashMap VId (List Nat)) (v : VId) : HashMap VId (List Nat) :=
      match m[v]? with
      | some (p :: rest) => if p == pos then m.insert v rest else m
      | _ => m
    { s with usesLeft := vs.foldl step s.usesLeft }

def isDead (v : VId) : AM Bool := do
  if ← isPinned v then return false
  return (← remaining v) == 0

/-- Free the register and slot of a value with no remaining use. -/
def release (v : VId) : AM Unit := do
  if !(← isDead v) then return
  modify fun s =>
    let s := match s.regOf[v]? with
      | some r => { s with regOf := s.regOf.erase v, holder := s.holder.erase r.n }
      | none => s
    let s := match s.slotOf[v]? with
      | some i => { s with slotOf := s.slotOf.erase v, dyingSlots := i :: s.dyingSlots }
      | none => s
    { s with remat := s.remat.erase v }

/-- Registers of operands that stay live after this instruction. -/
def liveRegs (vs : List VId) : AM (List VReg) := do
  let mut out := []
  for v in vs do
    if !(← isDead v) then
      if let some r ← regOf? v then out := r :: out
  return out

/-- Before a store: loads may no longer be reread, so pending ones go to registers. -/
def flushLoads : AM Unit := do
  let s ← get
  let isLoad : VOp → Bool
    | .load _ | .loadz _ _ => true
    | _ => false
  let ids := ((s.remat.toList.filter fun (_, op) => isLoad op).map (·.1)).toArray.qsort (· < ·)
  -- loads already in registers become ordinary values
  for v in ids do
    if (← regOf? v).isSome then modify fun s => { s with remat := s.remat.erase v }
  for v in ids do
    if (← regOf? v).isNone then
      if (← remaining v) > 0 then discard <| materialize v []
      modify fun s => { s with remat := s.remat.erase v }

def stmt (pos : Nat) : VStmt → AM Unit
  | .df id op => do
    let w := (← read).w
    match op with
    | .load _ | .loadz _ _ | .bcast _ | .cvec _ | .zero =>
        modify fun s => { s with remat := s.remat.insert id op }
    | .bin bop a b =>
        let (a, b) ← (if bop.comm then do
            if (← memSrc? b).isNone && (← memSrc? a).isSome then pure (b, a) else pure (a, b)
          else pure (a, b))
        let ra ← materialize a []
        let sb ← src b [ra]
        consume [a, b] pos
        let live ← liveRegs [a, b]
        release a; release b
        let rd ← pickReg live
        emit (.vbin bop w rd ra sb)
        bind id rd
    | .xorc a bits =>
        let ra ← materialize a []
        let sb ← (if bits.all (· == bits[0]!) then bcastSrc bits[0]!
                  else do pure (VSrc.mem (Mem.rip (← vecLabel bits))))
        consume [a] pos
        let live ← liveRegs [a]
        release a
        let rd ← pickReg live
        emit (.vbin .xor w rd ra sb)
        bind id rd
    | .shufpd a b imm | .shuff a b imm =>
        let ra ← materialize a []
        let sb ← src b [ra]
        consume [a, b] pos
        let live ← liveRegs [a, b]
        release a; release b
        let rd ← pickReg live
        match op with
        | .shufpd .. => emit (.vshufpd w rd ra sb imm)
        | _ => emit (.vshuff64x2 w rd ra sb imm)
        bind id rd
    | .addsub _ _ | .subadd _ _ => throw "register allocation: addsub must be lowered first"
    | .permt2 a idx b =>
        let ra ← materialize a []
        let ri ← materialize idx [ra]
        let sb ← src b [ra, ri]
        consume [a, idx, b] pos
        if ← isDead a then
          release a; release idx; release b
          emit (.vpermt2pd w ra ri sb)
          bind id ra
        else if ← isDead idx then
          release idx; release b
          emit (.vpermi2pd w ri ra sb)
          bind id ri
        else
          let live ← liveRegs [a, idx, b]
          release b
          let rd ← pickReg live
          emit (.vmov w rd (.reg ri))
          emit (.vpermi2pd w rd ra sb)
          bind id rd
    | .fma fop a b c =>
        let ops := #[a, b, c]
        -- at most one memory operand
        let mut memRole : Option (Nat × VSrc) := none
        for i in [1, 0, 2] do
          if memRole.isNone then
            if let some m ← memSrc? ops[i]! then memRole := some (i, m)
        let mut rs : Array VReg := #[default, default, default]
        let mut avoid : List VReg := []
        for i in [0, 1, 2] do
          if memRole.map (·.1) != some i then
            let r ← materialize ops[i]! avoid
            rs := rs.set! i r
            avoid := r :: avoid
        consume [a, b, c] pos
        let isReg (i : Nat) : Bool := memRole.map (·.1) != some i
        -- the operand to overwrite: one that dies here
        let mut d : Option Nat := none
        for i in [2, 0, 1] do
          if d.isNone && isReg i then
            if ← isDead ops[i]! then d := some i
        let live ← liveRegs [a, b, c]
        match d with
        | some _ => pure ()
        | none =>
            -- no operand dies: overwrite a copy
            let i := if isReg 2 then 2 else 0
            let r ← pickReg live
            emit (.vmov w r (.reg rs[i]!))
            rs := rs.set! i r
            d := some i
        release a; release b; release c
        let dI := d.getD 0
        let ms : Option VSrc := memRole.map (·.2)
        let mi : Option Nat := memRole.map (·.1)
        let rsrc (i : Nat) : VSrc := if mi == some i then ms.getD default else .reg rs[i]!
        -- (form, s2, s3)
        let (form, s2, s3) : FmaForm × Nat × Nat :=
          match dI with
          | 0 => if mi == some 2 then (.f213, 1, 2) else (.f132, 2, 1)
          | 1 => if mi == some 2 then (.f213, 0, 2) else (.f132, 2, 0)
          | _ => if mi == some 0 then (.f231, 1, 0) else (.f231, 0, 1)
        emit (.vfma fop form w rs[dI]! rs[s2]! (rsrc s3))
        bind id rs[dI]!
  | .store m v => do
    flushLoads
    let r ← materialize v []
    emit (.vstore (← read).w m r)
    consume [v] pos
    release v
  | .storek m k v => do
    flushLoads
    let r ← materialize v []
    emit (.vstorek (← read).w m k r)
    consume [v] pos
    release v

end AM

/-- Remove definitions whose value is never used. -/
def VBlock.dce (b : VBlock) (keep : VId → Bool := fun _ => false) : VBlock := Id.run do
  let mut used : HashMap VId Unit := {}
  let mut out : Array VStmt := #[]
  for i in [0:b.stmts.size] do
    let st := b.stmts[b.stmts.size - 1 - i]!
    match st with
    | .df id op =>
        if used.contains id || keep id then
          for a in op.args do used := used.insert a ()
          out := out.push st
    | .store _ v | .storek _ _ v =>
        used := used.insert v ()
        out := out.push st
  return { b with stmts := out.reverse }

/-- Write the mixed add/subtract operations with instructions that exist at every width:
`a ∓ b = a·1 ∓ b` as one fused operation (the product by one is exact, so the result is the
correctly rounded sum or difference, as `vaddpd`/`vsubpd` give). -/
def VBlock.lower (b : VBlock) : VBlock := Id.run do
  let mut top := 0
  let mut has := false
  for st in b.stmts do
    match st with
    | .df id op =>
        top := max top (id + 1)
        match op with
        | .addsub .. | .subadd .. => has := true
        | _ => pure ()
    | _ => pure ()
  if !has then return b
  let one := top
  let mut out : Array VStmt := #[.df one (.bcast (1.0 : Float).toBits)]
  for st in b.stmts do
    match st with
    | .df id (.addsub x y) => out := out.push (.df id (.fma .fmaddsub x one y))
    | .df id (.subadd x y) => out := out.push (.df id (.fma .fmsubadd x one y))
    | _ => out := out.push st
  return { b with stmts := out }

/-- Evaluate the shuffles and sign flips of constants (twiddle factors written as constants
are rearranged at generation time, not at run time). Only operations that move or flip bits
are evaluated, so the values are exactly those the instructions would produce. -/
def VBlock.fold (b : VBlock) : VBlock := Id.run do
  let n := b.w.lanes
  let mut cst : HashMap VId (Array UInt64) := {}
  let mut out : Array VStmt := #[]
  for st in b.stmts do
    match st with
    | .df id op =>
        let val : Option (Array UInt64) :=
          match op with
          | .bcast x => some (Array.replicate n x)
          | .cvec v => if v.size == n then some v else none
          | .zero => some (Array.replicate n 0)
          | .xorc a m =>
              if m.size == 0 then none else
              (cst[a]?).map fun v => (Array.range n).map fun i => v[i]! ^^^ m[i % m.size]!
          | .shufpd a c imm =>
              match cst[a]?, cst[c]? with
              | some va, some vc => some ((Array.range n).map fun i =>
                  let src := if i % 2 == 0 then va else vc
                  src[i - i % 2 + (imm >>> i) % 2]!)
              | _, _ => none
          | _ => none
        match val with
        | some v =>
            cst := cst.insert id v
            let op' : VOp :=
              match op with
              | .xorc .. | .shufpd .. =>
                  if v.all (· == 0) then .zero
                  else if v.all (· == v[0]!) then .bcast v[0]!
                  else .cvec v
              | _ => op
            out := out.push (.df id op')
        | none => out := out.push st
    | _ => out := out.push st
  return { b with stmts := out }

/-- How `VBlock.schedule` orders the operands of an operation. -/
inductive OpOrder where
  /-- as written -/
  | listed
  /-- the operand defined first in the block first -/
  | early
  /-- the operand defined last in the block first -/
  | late
  /-- the operand that needs more registers first (Sethi–Ullman numbers) -/
  | deep
  deriving DecidableEq, Repr, Inhabited

/-- Reorder a block so that every value is computed just before its first use: the stores
keep their order, and each store is preceded by the not yet computed part of the expression
it stores, operands first (in the order `ord`). Loads are not moved across stores. Values
are then live for shorter spans, which saves spills. -/
partial def VBlock.schedule (b : VBlock) (ord : OpOrder) : VBlock := Id.run do
  let mut defs : HashMap VId (Nat × VOp) := {}
  let mut su : HashMap VId Nat := {}
  for i in [0:b.stmts.size] do
    if let .df id op := b.stmts[i]! then
      defs := defs.insert id (i, op)
      -- Sethi–Ullman number: registers needed to compute the value as a tree
      let ls := (op.args.map fun a => su.getD a 0).toArray.qsort (· > ·)
      let mut n := if op.args.isEmpty then 0 else 1
      for j in [0:ls.size] do n := max n (ls[j]! + j)
      su := su.insert id n
  let isLoad : VOp → Bool
    | .load _ | .loadz _ _ => true
    | _ => false
  let idx (v : VId) : Nat := (defs[v]?.map (·.1)).getD 0
  let args (op : VOp) : List VId :=
    match ord with
    | .listed => op.args
    | .early => (op.args.toArray.qsort fun x y => idx x < idx y).toList
    | .late => (op.args.toArray.qsort fun x y => idx x > idx y).toList
    | .deep => (op.args.toArray.qsort fun x y => su.getD x 0 > su.getD y 0).toList
  let rec need (v : VId) (st : HashMap VId Unit × Array VStmt) :
      HashMap VId Unit × Array VStmt :=
    if st.1.contains v then st else
    match defs[v]? with
    | none => st
    | some (_, op) =>
        let st := (args op).foldl (fun st a => need a st) st
        (st.1.insert v (), st.2.push (.df v op))
  let mut st : HashMap VId Unit × Array VStmt := ({}, #[])
  let mut pendingLoads : Array VId := #[]
  for stm in b.stmts do
    match stm with
    | .df id op => if isLoad op then pendingLoads := pendingLoads.push id
    | .store _ v | .storek _ _ v =>
        st := need v st
        -- loads written before this store stay before it
        for l in pendingLoads do st := need l st
        pendingLoads := #[]
        st := (st.1, st.2.push stm)
  return { b with stmts := st.2 }

structure Alloc where
  instrs : Array Instr
  nSlots : Nat
  pool : Pool
  touched : Nat

/-- Allocate registers for a block, in the order it is written. -/
def allocBlock1 (cfg : ACfg) (blk : VBlock) (pool : Pool) : Except String Alloc := do
  -- use positions
  let mut uses : HashMap VId (Array Nat) := {}
  for pos in [0:blk.stmts.size] do
    let vs : List VId := (match blk.stmts[pos]! with
      | .df _ op => op.args
      | .store _ v | .storek _ _ v => [v])
    for v in vs.eraseDups do
      uses := uses.insert v ((uses.getD v #[]).push pos)
  -- operands in positions that need a register
  let mut noFold : HashMap VId Unit := {}
  for st in blk.stmts do
    let vs : List VId := (match st with
      | .df _ (.bin op a _) => if op.comm then [] else [a]
      | .df _ (.xorc a _) | .df _ (.shufpd a _ _) | .df _ (.shuff a _ _) => [a]
      | .df _ (.permt2 a idx _) => [a, idx]
      | .store _ v | .storek _ _ v => [v]
      | _ => [])
    for v in vs do noFold := noFold.insert v ()
  let st : AState := { pool, noFold, usesLeft := uses.fold (fun m v a => m.insert v a.toList) {} }
  let run : AM Unit := do
    for pos in [0:blk.stmts.size] do
      AM.stmt pos blk.stmts[pos]!
      -- the slots of the values that died are free from here on
      modify fun s => { s with freeSlots := s.dyingSlots ++ s.freeSlots, dyingSlots := [] }
  let ((), s) ← (run.run cfg).run st
  return ⟨s.out, s.nSlots, s.pool, s.touched⟩

/-- Allocate registers for a block: the block as written and its reorderings
(`VBlock.schedule`) are all allocated, and the shortest result is kept. -/
def allocBlock (cfg : ACfg) (blk : VBlock) (pool : Pool) : Except String Alloc := do
  let blk := blk.fold.lower.dce
  let ords := [OpOrder.listed, .early, .late, .deep]
  if cfg.sched ≥ 2 then
    return ← allocBlock1 cfg (blk.schedule (ords.getD (cfg.sched - 2) .listed)) pool
  let mut best ← allocBlock1 cfg blk pool
  if cfg.sched == 1 then
    for ord in ords do
      let a ← allocBlock1 cfg (blk.schedule ord) pool
      if a.instrs.size < best.instrs.size then best := a
  return best

end LeanFFTW.Asm
