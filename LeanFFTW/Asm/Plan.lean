/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Kernels
import LeanFFTW.Gen.InPlace
import LeanFFTW.Core.Trig

/-!
# Plans of the assembly engine

A plan is a tree: kernels (the generated passes) at the leaves, and loops that run their
children while advancing the `in` pointer, the `out` pointer and the column. `PlanSrc.fill`
writes the tree as records in one `FloatArray`, together with the tables the records use
(twiddles, offsets) and, for in-place transforms, a buffer. Pointers in records are byte
offsets from the record, so the memory of a plan does not depend on where it is.

Lean builds plans and keeps them (a plan is an ordinary Lean object, freed by reference
counting); the assembly functions of `LeanFFTW/Asm/Kernels.lean` execute them. There is no C
in between: Lean calls `lfa_run` directly.
-/

namespace LeanFFTW.Asm

open LeanFFTW.Gen

/-- A parameter of a record. -/
inductive PArg where
  | imm (v : Int)
  /-- the address of table `i` (stored as a byte offset from the record) -/
  | blob (i : Nat)
  deriving Inhabited

/-- A plan. -/
inductive PNode where
  /-- a generated function with its parameters -/
  | kern (fn : String) (args : Array PArg)
  /-- run the children `count` times; iteration `i` runs them on `in + i·dIn`,
  `out + i·dOut + tab[i]` and `col + i·dCol`. `par`: the iterations are shared among the
  threads of the pool; they must write disjoint memory and not read what another writes -/
  | loop (count : Nat) (dIn dOut dCol : Int) (tab : Option Nat) (ch : Array PNode)
      (par : Bool := false)
  /-- when `in == out`, first copy `bytes` bytes of the input to the buffer and read it there -/
  | copyIn (bytes : Nat) (buf : Nat) (ch : PNode)
  deriving Inhabited

/-- Run the children once, in order. -/
def PNode.seq (ch : Array PNode) : PNode := .loop 1 0 0 0 none ch

/-- Data a plan refers to. -/
inductive Blob where
  | floats (a : FloatArray)
  | words (a : Array UInt64)
  /-- uninitialized working memory -/
  | space (bytes : Nat)
  deriving Inhabited

def Blob.words? : Blob → Nat
  | .floats a => a.size
  | .words a => a.size
  | .space b => (b + 7) / 8

structure PlanSrc where
  root : PNode
  blobs : Array Blob := #[]
  deriving Inhabited

/-- Number of words of the records of a tree (a node, then its children in order). -/
partial def PNode.size : PNode → Nat
  | .kern _ args => 1 + args.size
  | .loop _ _ _ _ tab ch _ => 8 + ch.size + (if tab.isSome then 0 else 1) + ch.foldl (fun n c => n + c.size) 0
  | .copyIn _ _ ch => 4 + ch.size

def wordOfInt (v : Int) : UInt64 := UInt64.ofNat (v % (2 ^ 64 : Int)).toNat

/-- The records of a tree whose root is at word `pos`; `blobPos i` is the word at which
table `i` starts. Unknown function names give `none`. -/
partial def PNode.emit (blobPos : Nat → Nat) (pos : Nat) : PNode → Option (Array UInt64)
  | .kern fn args => do
      let idx ← fnIndex[fn]?
      let ws := args.map fun
        | .imm v => wordOfInt v
        | .blob i => wordOfInt (8 * ((blobPos i : Int) - pos))
      return #[UInt64.ofNat idx] ++ ws
  | .loop count dIn dOut dCol tab ch par => do
      let idx ← fnIndex[if par then "lfa_ploop" else "lfa_loop"]?
      let hdr := 8 + ch.size + (if tab.isSome then 0 else 1)
      -- without a table, the table pointer stays on a zero word of the record
      let (tabOff, tabStep) : Int × Int := match tab with
        | some i => (8 * ((blobPos i : Int) - pos), 8)
        | none => (8 * (8 + ch.size), 0)
      let mut offs : Array UInt64 := #[]
      let mut body : Array UInt64 := #[]
      let mut cpos := pos + hdr
      for c in ch do
        offs := offs.push (UInt64.ofNat (8 * (cpos - pos)))
        body := body ++ (← c.emit blobPos cpos)
        cpos := cpos + c.size
      return #[UInt64.ofNat idx, UInt64.ofNat count, wordOfInt dIn, wordOfInt dOut, wordOfInt dCol,
               wordOfInt tabOff, wordOfInt tabStep, UInt64.ofNat ch.size] ++ offs ++
             (if tab.isSome then #[] else #[0]) ++ body
  | .copyIn bytes buf ch => do
      let idx ← fnIndex["lfa_copyin"]?
      return #[UInt64.ofNat idx, UInt64.ofNat bytes, wordOfInt (8 * ((blobPos buf : Int) - pos)), 32] ++
             (← ch.emit blobPos (pos + 4))

/-- Word positions of the tables: after the records, each on a 64-byte boundary when the
memory starts at an address `≡ 8·phase (mod 64)`. Returns the positions and the total. -/
def PlanSrc.layout (p : PlanSrc) (phase : Nat) : Array Nat × Nat := Id.run do
  let up (n : Nat) : Nat := n + (8 - (n + phase) % 8) % 8
  let mut pos := up p.root.size
  let mut out : Array Nat := #[]
  for b in p.blobs do
    out := out.push pos
    pos := up (pos + b.words?)
  return (out, pos)

/-- Words a plan needs, for any phase. -/
def PlanSrc.capacity (p : PlanSrc) : Nat := (p.layout 0).2 + 8 * (p.blobs.size + 2)

/-- Write the plan into `mem` (empty, with enough capacity). The root record is at word 0. -/
def PlanSrc.fill (p : PlanSrc) (phase : Nat) (mem : FloatArray) : Option FloatArray := do
  let (bpos, _) := p.layout phase
  let recs ← p.root.emit (bpos.getD · 0) 0
  let mut mem := mem
  for w in recs do mem := mem.push (Float.ofBits w)
  for i in [0:p.blobs.size] do
    while mem.size < bpos[i]! do mem := mem.push 0.0
    match p.blobs[i]! with
    | .floats a => for j in [0:a.size] do mem := mem.push a[j]!
    | .words a => for w in a do mem := mem.push (Float.ofBits w)
    | .space _ => pure ()
  return mem

/-! ## Calling the engine -/

/-- Address of the data of a `FloatArray`. The address is valid while the array is alive and
not modified by Lean code. -/
@[extern "lfa_addr"]
opaque addr (a : @& FloatArray) : USize

/-- Run the record at word `root` of `mem` on the arrays at addresses `inp`, `out`, `reps`
times. -/
@[extern "lfa_run"]
opaque runRaw (mem : @& FloatArray) (root inp out reps : USize) : IO Unit

/-- Store `n` zero words at address `p`. -/
@[extern "lfa_zero"]
opaque zeroRaw (p n : USize) : IO Unit

/-- The assembly returns to Lean through this function, which builds the `IO` result. -/
@[export lfa_ok_unit]
def okUnit (_ : USize) : IO Unit := pure ()

/-! ## Threads -/

@[extern "lfa_worker"]
opaque workerRaw (w : USize) : IO Unit

/-- The word at byte `d` of the state of the thread pool (`lfa_pool`). -/
@[extern "lfa_pool_load"]
opaque poolLoad (d : USize) : IO USize

@[extern "lfa_pool_store"]
opaque poolStore (d v : USize) : IO Unit

@[extern "lfa_pool_wake"]
opaque poolWake (dummy : USize) : IO Unit

@[export lfa_ok_usize]
def okUsize (v : USize) : IO USize := pure v

namespace Pool

/-- Threads that execute plans: the caller and the workers. -/
def threads : IO Nat := do return (← poolLoad 40).toNat + 1

/-- Stop the workers. -/
def stop : IO Unit := do
  if (← poolLoad 136) == 0 then return
  poolStore 40 0
  poolStore 192 1
  poolWake 0
  while (← poolLoad 136) != 0 do IO.sleep 1
  poolStore 192 0

/-- Run plans on `n` threads: start `n − 1` workers (Lean tasks on dedicated threads that
run the assembly loop `lfa_worker`). Plans made for another number of threads stay correct. -/
def start (n : Nat) : IO Unit := do
  if (← threads) == max n 1 then return
  stop
  if n ≤ 1 then return
  for w in [1:n] do
    discard <| IO.asTask (prio := .dedicated) (workerRaw w.toUSize)
  while (← poolLoad 136).toNat < n - 1 do IO.sleep 1
  poolStore 40 (n - 1).toUSize

end Pool

/-- A plan in memory, ready to run. -/
structure Plan where
  mem : FloatArray
  /-- the plan supports `in == out` -/
  inplace : Bool
  deriving Inhabited

/-- Place a plan in memory. The tables are put on 64-byte boundaries of the actual address. -/
def PlanSrc.build (p : PlanSrc) (inplace : Bool) : IO Plan := do
  let mem := FloatArray.emptyWithCapacity p.capacity
  let a := addr mem
  let some mem := p.fill ((a.toNat / 8) % 8) mem | throw (IO.userError "plan: unknown kernel")
  if addr mem != a then throw (IO.userError "plan: memory moved")
  return { mem, inplace }

def Plan.run (p : Plan) (inp out : USize) (reps : USize := 1) : IO Unit :=
  runRaw p.mem 0 inp out reps

/-! ## The in-place schedule -/

/-- The base twiddle table `ω_N^m`, `m < N`, interleaved. -/
def baseTable (N : Nat) (fwd : Bool) : FloatArray := Id.run do
  let tab := Trig.cosSin2PiTable N
  let mut out := FloatArray.emptyWithCapacity (2 * N)
  for (c, s) in tab do
    out := (out.push c).push (if fwd then Trig.negZ s else s)
  return out

/-- Twiddles of a pass `(R, ns)` in the order the loop reads them: for each vector `v` of 8
columns, for `r = 1 … R-1`: 8 real parts, 8 imaginary parts, lane `p` being column
`8v + σ p`. Entry `(r, k)` is `ω_N^(r·k·N/(ns·R))`, as in `passTwiddles`. -/
def ditTwiddles (base : FloatArray) (N R ns : Nat) : FloatArray := Id.run do
  let step := N / (ns * R)
  let mut t := FloatArray.emptyWithCapacity (2 * (R - 1) * ns)
  for v in [0:ns / 8] do
    for r in [1:R] do
      for part in [0:2] do
        for p in [0:8] do
          t := t.push base[2 * (r * (8 * v + sigma[p]!) * step) + part]!
  return t

/-- The plan of the in-place schedule for the radices `rs` (`s ≥ 2` passes; powers of two,
the first at least 8), with the passes below `T` run per group of blocks and
the others in chunks of `Q` columns (`T = 0`: pass by pass), as in `docs/ITERATIONS.md`.
`none` when the schedule does not apply. -/
def inplacePlan (N : Nat) (fwd : Bool) (rs : Array Nat) (T Q : Nat) (inplace : Bool)
    (base : FloatArray) (par : Bool := false) (pf : Nat := 0) : Option PlanSrc := do
  let s := rs.size
  guard (s ≥ 2 && T < s)
  let R0 := rs[0]!
  guard (leafRadices.contains R0 && rs.all fun R => ditRadices.contains R)
  let nst : Array Nat := (Array.range (s + 1)).map fun t => passNs rs t
  guard (nst[s]! == N)
  let ofs := leafOffsets N rs
  guard (ofs.size ≥ 8)
  -- leaf `4h + m` of an iteration is written at `h·ofs 4 + ofs m`
  guard ((List.range 4).all fun m => ofs[4 + m]! == ofs[4]! + ofs[m]!)
  let mut blobs : Array Blob := #[]
  -- twiddles
  let mut tw : Array Nat := #[0]
  for t in [1:s] do
    tw := tw.push blobs.size
    blobs := blobs.push (.floats (ditTwiddles base N rs[t]! nst[t]!))
  let dit (t nb nq : Nat) : PNode :=
    .kern (ditName rs[t]! fwd (t == s - 1))
      #[.imm 0, .blob tw[t]!, .imm (16 * nst[t]!), .imm nb, .imm nq,
        .imm (16 * nst[t]! * rs[t]! - 128 * nq)]
  let leaf (count inStep gtab : Nat) : PNode :=
    .kern (leafName R0 fwd pf) #[.imm (16 * (N / R0)), .imm count, .imm inStep, .blob gtab,
      .imm (16 * ofs[4]!), .imm (16 * ofs[1]!), .imm (16 * ofs[2]!), .imm (16 * ofs[3]!)]
  let mut root : PNode := default
  if T == 0 then
    guard (Q == 0 && !par)
    let gtab := blobs.size
    blobs := blobs.push (.words (((Array.range (N / R0 / 8)).map fun i => UInt64.ofNat (16 * ofs[8 * i]!)) ++ Array.replicate leafPad 0))
    root := .seq (#[leaf (N / R0 / 8) 128 gtab] ++
      (Array.range (s - 1)).map fun i => dit (i + 1) (N / nst[i + 2]!) (nst[i + 1]! / 8))
  else
    let D := N / nst[T]!
    let gn := nst[T]! / R0
    guard (D ≥ 8 && D % 8 == 0)
    let Qe := if Q == 0 then nst[T]! else Q
    guard (Qe % 8 == 0 && nst[T]! % Qe == 0)
    -- leaf `dl + i·D` is written at `ofs dl + ofs (i·D)`
    guard ((List.range (D / 8)).all fun g => (List.range gn).all fun i =>
      ofs[8 * g + i * D]! == ofs[8 * g]! + ofs[i * D]!)
    let gA := blobs.size
    blobs := blobs.push (.words ((Array.range (D / 8)).map fun g => UInt64.ofNat (16 * ofs[8 * g]!)))
    let gB := blobs.size
    blobs := blobs.push (.words (((Array.range gn).map fun i => UInt64.ofNat (16 * ofs[i * D]!)) ++ Array.replicate leafPad 0))
    let gL := blobs.size
    blobs := blobs.push (.words ((Array.range 8).map fun l => UInt64.ofNat (16 * ofs[l]!)))
    let inner : Array PNode := if T ≥ 2 then
        #[.loop 8 0 0 0 (some gL) ((Array.range (T - 1)).map fun i =>
          dit (i + 1) (nst[T]! / nst[i + 2]!) (nst[i + 1]! / 8))]
      else #[]
    -- With `par`, the iterations of both loops are shared among threads: an iteration of
    -- the first writes its own 8 blocks of `out`; one of the second, its own columns
    -- (the columns `≡ c (mod nst T)` with `c` in its chunk, in every later pass).
    let phaseA : PNode := .loop (D / 8) 128 0 0 (some gA) (#[leaf gn (16 * D) gB] ++ inner) par
    let phaseB : PNode := .loop (nst[T]! / Qe) 0 0 (Qe / 8) none
      ((Array.range (s - T)).map fun i =>
        let t := T + i
        .loop (nst[t]! / nst[T]!) 0 0 (nst[T]! / 8) none #[dit t (N / nst[t + 1]!) (Qe / 8)]) par
    root := .seq #[phaseA, phaseB]
  if inplace then
    let buf := blobs.size
    blobs := blobs.push (.space (16 * N))
    root := .copyIn (16 * N) buf root
  return { root, blobs }

/-! ## Small transforms -/

/-- Schedules of the engine. -/
inductive Mode where
  /-- one butterfly, in registers -/
  | csmall
  /-- two passes in registers, interleaved data -/
  | cfused
  /-- two passes through a work array, interleaved data -/
  | ctwo
  /-- the in-place schedule -/
  | inplace
  /-- Stockham passes on interleaved data (any radices) -/
  | stockham
  deriving DecidableEq, Repr, Inhabited

/-- Plans of the whole-transform kernels. -/
def smallPlan (N : Nat) (fwd : Bool) (rs : Array Nat) (mode : Mode) (inplace : Bool) :
    Option PlanSrc := do
  match mode with
  | .csmall =>
      guard (rs == #[N] && csmallSizes.contains N)
      return { root := .kern (csmallName N fwd) #[] }
  | .cfused =>
      guard (rs.size == 2 && rs[0]! * rs[1]! == N)
      let vlc ← [4, 2].find? fun vlc => cfusedSet.contains (rs[0]!, rs[1]!, vlc)
      return { root := .kern (cfusedName rs[0]! rs[1]! vlc fwd) #[] }
  | .ctwo =>
      guard (rs.size == 2 && rs[0]! * rs[1]! == N)
      let vlc ← [4, 2].find? fun vlc => ctwoSet.contains (rs[0]!, rs[1]!, vlc)
      if inplace then
        return { root := .kern (ctwoName rs[0]! rs[1]! vlc fwd) #[.blob 0], blobs := #[.space (16 * N)] }
      else
        return { root := .kern (ctwoName rs[0]! rs[1]! vlc fwd) #[.imm 0] }
  | .inplace | .stockham => none

/-! ## The Stockham schedule -/

/-- Twiddles of a Stockham pass `(R, ns)` in the order the loop reads them: for each vector
`v` of 8 columns, for `r = 1 … R-1`: 8 real parts, 8 imaginary parts, lane `p` being column
`8v + σ p` (zero beyond `ns`). Entry `(r, k)` is `ω_N^(r·k·N/(ns·R))`. -/
def stkTwiddles (base : FloatArray) (N R ns : Nat) : FloatArray := Id.run do
  let step := N / (ns * R)
  let nv := (ns + 7) / 8
  let mut t := FloatArray.emptyWithCapacity (16 * (R - 1) * nv)
  for v in [0:nv] do
    for r in [1:R] do
      for part in [0:2] do
        for p in [0:8] do
          let kk := 8 * v + sigma[p]!
          t := t.push (if kk < ns then base[2 * (r * kk * step) + part]! else 0.0)
  return t

/-- Masks of the two vectors of a row holding `tl < 8` complex numbers. -/
def tailMask (tl : Nat) : Int × Int :=
  ((2 ^ (min (2 * tl) 8) - 1 : Nat), (2 ^ (max (2 * tl) 8 - 8) - 1 : Nat))

/-- The plan of the Stockham schedule for the radices `rs` (any product). The passes
alternate between two buffers; the first reads `in` and the last writes `out`, so
`in == out` is allowed. -/
def stockhamPlan (N : Nat) (fwd : Bool) (rs : Array Nat) (base : FloatArray) : Option PlanSrc := do
  let s := rs.size
  guard (s ≥ 1 && rs.all stkRadices.contains)
  let nst : Array Nat := (Array.range (s + 1)).map fun t => passNs rs t
  guard (nst[s]! == N)
  let mut blobs : Array Blob := #[]
  -- work arrays (the first pass writes whole vectors of butterflies only into the frame)
  let bufs := (Array.range (min (s - 1) 2)).map fun i => i
  for _ in bufs do blobs := blobs.push (.space (16 * N + 64))
  let mut nodes : Array PNode := #[]
  for t in [0:s] do
    let R := rs[t]!
    let ns := nst[t]!
    let NR := N / R
    let src : PArg := if t == 0 then .imm 0 else .blob ((t - 1) % 2)
    let dst : PArg := if t == s - 1 then .imm 0 else .blob (t % 2)
    if t == 0 then
      let (m0, m1) := tailMask (NR % 8)
      nodes := nodes.push (.kern (stk0Name R fwd)
        #[src, dst, .imm (16 * NR), .imm (NR / 8), .imm (NR % 8), .imm m0, .imm m1])
    else
      let tw := blobs.size
      blobs := blobs.push (.floats (stkTwiddles base N R ns))
      let (m0, m1) := tailMask (ns % 8)
      nodes := nodes.push (.kern (stkName R fwd)
        #[src, dst, .blob tw, .imm (16 * NR), .imm (16 * ns), .imm (NR / ns), .imm (ns / 8),
          .imm (16 * (ns % 8)), .imm (16 * ns * (R - 1)), .imm m0, .imm m1])
  return { root := .seq nodes, blobs }

/-- The plan of a schedule. -/
def mkPlan (N : Nat) (fwd : Bool) (rs : Array Nat) (mode : Mode) (T Q : Nat) (inplace : Bool)
    (base : FloatArray) (par : Bool := false) (pf : Nat := 0) : Option PlanSrc :=
  if mode == .inplace then
    (if leafPrefetch.contains pf then inplacePlan N fwd rs T Q inplace base par pf else none)
  else if pf != 0 then none
  else if mode == .stockham then (if T == 0 && Q == 0 && !par then stockhamPlan N fwd rs base else none)
  else if T == 0 && Q == 0 && !par then smallPlan N fwd rs mode inplace else none

end LeanFFTW.Asm
