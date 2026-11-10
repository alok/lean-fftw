/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Sem
import Std.Data.HashMap

/-!
# Checking emitted blocks against their specification

The vectorizer, the scheduler and the register allocator are not proved correct. Instead,
every block of vector code they emit is *checked* (translation validation): the generator
states what the block must compute as a `Spec`, and `check` runs the emitted instructions
symbolically and accepts only if every stored lane is the required value. `check` is proved
sound against the model of the instructions (`LeanFFTW/Asm/Sound.lean`): an accepted block
computes its specification on every machine state.

## Specifications

A `Spec` is a list of *nodes* (a straight-line program over scalars: words of the initial
memory, constants, and the kernel operations applied to earlier nodes) and, for each memory
operand the block stores, the node each lane must hold. Specifications of the engine's
blocks are kernels instantiated lane by lane (`SpecB.kernel`).

## The symbolic run

The checker tracks, for every lane of every register and spill slot, what it knows about
the scalar there (`SVal`): a node of the specification, the negation of a node, a constant,
or nothing. An instruction's result lane is found by *looking up* the operation applied to
the nodes of its operands among the nodes of the specification, after rewriting with the
laws of `Machine.Lawful` (commutativity, `fma x 1 c = x + c`, sign flips). The checker never
builds terms, so a check takes time linear in the block.

## Memory

Reads of the initial memory are only accepted before the first store to data memory, so the
input may overlap the output (in-place transforms). Spill slots (operands on `rsp`) are read
back only after a store to the same operand. The soundness theorem assumes that distinct
operands written by the block do not overlap, and that spill slots and constants do not
overlap the data.
-/

namespace LeanFFTW.Asm

open Std LeanFFTW.Gen

/-- A scalar of a specification; operands are earlier nodes. -/
inductive SNode where
  /-- word `lane` of the operand `m` in the initial memory -/
  | inp (m : Mem) (lane : Nat)
  | bits (b : UInt64)
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  | fma (a b c : Nat)
  | fms (a b c : Nat)
  | fnma (a b c : Nat)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Every operand is an earlier node. -/
def SNode.below (i : Nat) : SNode → Bool
  | .inp .. | .bits _ => true
  | .add a b | .sub a b | .mul a b => a < i && b < i
  | .neg a => a < i
  | .fma a b c | .fms a b c | .fnma a b c => a < i && b < i && c < i

/-- What a block must compute. -/
structure Spec where
  nodes : Array SNode
  /-- for each stored operand, the node of each lane -/
  outs : List (Mem × Array Nat)
  deriving Inhabited

variable {α : Type}

/-- The value of a node, given the values `g` of the earlier nodes. -/
def SNode.eval (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) (g : Nat → α) : SNode → α
  | .inp m l => mem0 (ad m + l)
  | .bits b => M.ofBits b
  | .add a b => M.A.add (g a) (g b)
  | .sub a b => M.A.sub (g a) (g b)
  | .mul a b => M.A.mul (g a) (g b)
  | .neg a => M.A.neg (g a)
  | .fma a b c => M.A.fma (g a) (g b) (g c)
  | .fms a b c => M.A.fms (g a) (g b) (g c)
  | .fnma a b c => M.A.fnma (g a) (g b) (g c)

/-- Values of nodes, appended to `acc`. -/
def valsL (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) : List SNode → Array α → Array α
  | [], acc => acc
  | nd :: rest, acc =>
      valsL M ad mem0 rest (acc.push (nd.eval M ad mem0 fun i => acc.getD i (M.ofBits 0)))

/-- The values of the nodes of a specification on the initial memory `mem0`. -/
def Spec.vals (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) (sp : Spec) : Array α :=
  valsL M ad mem0 sp.nodes.toList #[]

/-- The value of node `i`. -/
def Spec.val (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) (sp : Spec) (i : Nat) : α :=
  (sp.vals M ad mem0).getD i (M.ofBits 0)

/-! ## Symbolic values -/

/-- What the checker knows about a scalar. -/
inductive SVal where
  /-- the value of a node -/
  | node (i : Nat)
  /-- the negation of the value of a node -/
  | negNode (i : Nat)
  /-- a constant -/
  | bits (b : UInt64)
  /-- nothing -/
  | junk
  deriving DecidableEq, Repr, Inhabited

/-- Kinds of memory operands. -/
inductive MKind where
  /-- `[rip + label]`: a constant of the pool -/
  | const (label : String)
  /-- `[rsp + d]`: a spill slot -/
  | frame
  | data
  deriving DecidableEq, Repr

def Mem.kind (m : Mem) : MKind :=
  match m.label with
  | some l => .const l
  | none => if m.base = some .rsp then .frame else .data

/-- What the checker is given. -/
structure Ctx where
  w : W
  nodes : Array SNode
  /-- an index of the nodes; its answers are verified, so it need not be trusted -/
  find : SNode → Option Nat
  /-- the constants of the pool, by label -/
  consts : String → Option (Array UInt64)
  /-- the nodes a stored operand must hold -/
  outOf : Mem → Option (Array Nat)

/-- The node equal to `nd`, when the specification has one. -/
def Ctx.look (cx : Ctx) (nd : SNode) : SVal :=
  match cx.find nd with
  | some i => if cx.nodes[i]? = some nd ∧ nd.below i = true then .node i else .junk
  | none => .junk

/-- A node holding the value. -/
def Ctx.toId (cx : Ctx) : SVal → Option Nat
  | .node i => some i
  | .bits b => (match cx.look (.bits b) with | .node i => some i | _ => none)
  | .negNode i => (match cx.look (.neg i) with | .node j => some j | _ => none)
  | .junk => none

/-- The first operation the specification has. -/
def Ctx.look2 (cx : Ctx) (n₁ n₂ : SNode) : SVal :=
  match cx.look n₁ with
  | .junk => cx.look n₂
  | v => v

def Ctx.sAdd (cx : Ctx) (x y : SVal) : SVal :=
  match cx.toId x, cx.toId y with
  | some a, some b => cx.look2 (.add a b) (.add b a)
  | _, _ => .junk

def Ctx.sSub (cx : Ctx) (x y : SVal) : SVal :=
  match cx.toId x, cx.toId y with
  | some a, some b => cx.look (.sub a b)
  | _, _ => .junk

def Ctx.sMul (cx : Ctx) (x y : SVal) : SVal :=
  match cx.toId x, cx.toId y with
  | some a, some b => cx.look2 (.mul a b) (.mul b a)
  | _, _ => .junk

def Ctx.sNeg (cx : Ctx) : SVal → SVal
  | .node i => (match cx.look (.neg i) with | .node j => SVal.node j | _ => SVal.negNode i)
  | .negNode i => .node i
  | _ => .junk

def Ctx.sXor (cx : Ctx) (x y : SVal) : SVal :=
  match y with
  | .bits b => if b = 0 then x else if b = 0x8000000000000000 then cx.sNeg x else .junk
  | _ => .junk

/-- The node whose negation the value is, when it is known to be one: a negated node, or a
constant whose sign-flipped bits are a node. -/
def Ctx.asNeg (cx : Ctx) : SVal → Option Nat
  | .negNode i => some i
  | .bits b =>
      (match cx.look (.bits (b ^^^ 0x8000000000000000)) with
       | .node i => some i
       | _ => none)
  | _ => none

/-- The first value that is known. -/
def SVal.orElse (v : SVal) (w : SVal) : SVal :=
  match v with
  | .junk => w
  | v => v

/-- The fused operation `f` of the specification on the factors `x`, `y` (either order). -/
def Ctx.look3 (cx : Ctx) (f : Nat → Nat → Nat → SNode) (x y c : Option Nat) : SVal :=
  match x, y, c with
  | some a, some b, some d => cx.look2 (f a b d) (f b a d)
  | _, _, _ => .junk

/-- `x·y + c`, as an operation of the specification: `fma`, or `fnma` with a factor negated. -/
def Ctx.sFma0 (cx : Ctx) (x y c : SVal) : SVal :=
  ((cx.look3 .fma (cx.toId x) (cx.toId y) (cx.toId c)).orElse
    (cx.look3 .fnma (cx.asNeg x) (cx.toId y) (cx.toId c))).orElse
    (cx.look3 .fnma (cx.toId x) (cx.asNeg y) (cx.toId c))

/-- `x·y + c`; when a factor is `1`, also as the sum. -/
def Ctx.sFma (cx : Ctx) (x y c : SVal) : SVal :=
  match cx.sFma0 x y c with
  | .junk =>
      if x = .bits oneBits then cx.sAdd y c
      else if y = .bits oneBits then cx.sAdd x c
      else .junk
  | v => v

/-- `x·y − c`; when a factor is `1`, also as the difference. -/
def Ctx.sFms (cx : Ctx) (x y c : SVal) : SVal :=
  match cx.look3 .fms (cx.toId x) (cx.toId y) (cx.toId c) with
  | .junk =>
      if x = .bits oneBits then cx.sSub y c
      else if y = .bits oneBits then cx.sSub x c
      else .junk
  | v => v

/-- `c − x·y`: `fnma`, or `fma` with a factor negated. -/
def Ctx.sFnma (cx : Ctx) (x y c : SVal) : SVal :=
  ((cx.look3 .fnma (cx.toId x) (cx.toId y) (cx.toId c)).orElse
    (cx.look3 .fma (cx.asNeg x) (cx.toId y) (cx.toId c))).orElse
    (cx.look3 .fma (cx.toId x) (cx.asNeg y) (cx.toId c))

def Ctx.sFmaLane (cx : Ctx) (op : VFma) (l : Nat) (a b c : SVal) : SVal :=
  match op with
  | .fmadd => cx.sFma a b c
  | .fmsub => cx.sFms a b c
  | .fnmadd => cx.sFnma a b c
  | .fmaddsub => if l % 2 = 0 then cx.sFms a b c else cx.sFma a b c
  | .fmsubadd => if l % 2 = 0 then cx.sFma a b c else cx.sFms a b c

def Ctx.sBinLane (cx : Ctx) (op : VBin) (x y : Nat → SVal) (l : Nat) : SVal :=
  match op with
  | .add => cx.sAdd (x l) (y l)
  | .sub => cx.sSub (x l) (y l)
  | .mul => cx.sMul (x l) (y l)
  | .xor => cx.sXor (x l) (y l)
  | .unpcklo => if l % 2 = 0 then x l else y (l - 1)
  | .unpckhi => if l % 2 = 0 then x (l + 1) else y l

/-! ## The symbolic state -/

/-- The lanes of a register or slot: 8 values. -/
abbrev Lanes := Array SVal

def Lanes.get (a : Lanes) (l : Nat) : SVal := a.getD l .junk

/-- Lanes `l < 8` from a function. -/
def Lanes.ofFn (f : Nat → SVal) : Lanes := (Array.range 8).map f

structure CState where
  /-- registers by number; absent: nothing known -/
  reg : HashMap Nat Lanes := {}
  /-- spill slots, the latest store first -/
  slot : List (Mem × Lanes) := []
  /-- a store to data memory has happened -/
  stored : Bool := false
  /-- the data operands stored so far -/
  done : List Mem := []

def CState.regLane (cs : CState) (n l : Nat) : SVal := (cs.reg.getD n #[]).get l

/-- Write a register at the width of the block; the upper lanes become zero. -/
def CState.setReg (cs : CState) (w : W) (r : VReg) (f : Nat → SVal) : CState :=
  { cs with reg := cs.reg.insert r.n (Lanes.ofFn fun l => if l < w.lanes then f l else .bits 0) }

def lookupSlot : List (Mem × Lanes) → Mem → Option Lanes
  | [], _ => none
  | (m', v) :: rest, m => if m' = m then some v else lookupSlot rest m

/-- The lanes of a source operand, when it may be read. Of a memory operand only the lanes
below the width of the block are known. -/
def CState.rd (cx : Ctx) (cs : CState) : VSrc → Option (Nat → SVal)
  | .reg r => some (cs.regLane r.n)
  | .mem m =>
      (match m.kind with
       | .const lab =>
           if m = Mem.rip lab then
             (cx.consts lab).map fun bs => fun l =>
               if l < cx.w.lanes then (match bs[l]? with | some b => SVal.bits b | none => .junk)
               else .junk
           else none
       | .frame =>
           (lookupSlot cs.slot m).map fun v => fun l => if l < cx.w.lanes then v.get l else .junk
       | .data =>
           if cs.stored then none
           else some fun l => if l < cx.w.lanes then cx.look (.inp m l) else .junk)
  | .bcst m =>
      (match m.kind with
       | .const lab =>
           if m = Mem.rip lab then
             (cx.consts lab).map fun bs => fun _ =>
               (match bs[0]? with | some b => SVal.bits b | none => .junk)
           else none
       | _ => none)

/-- Run one instruction symbolically; `none` rejects the block. -/
def cstep (cx : Ctx) (cs : CState) : Instr → Option CState
  | .vmov w d src =>
      if w = cx.w then (cs.rd cx src).map fun f => cs.setReg w d f else none
  | .vstore w m r =>
      if w = cx.w then
        (match m.kind with
         | .const _ => none
         | .frame => some { cs with slot := (m, Lanes.ofFn (cs.regLane r.n)) :: cs.slot }
         | .data =>
             (match cx.outOf m with
              | some ids =>
                  if (List.range w.lanes).all fun l =>
                      (match ids[l]? with
                       | some i => cs.regLane r.n l = .node i
                       | none => false)
                  then some { cs with stored := true, done := m :: cs.done }
                  else none
              | none => none))
      else none
  | .vbin op w d s1 s2 =>
      if w = cx.w then
        (cs.rd cx s2).map fun f => cs.setReg w d (cx.sBinLane op (cs.regLane s1.n) f)
      else none
  | .vfma op form w d s2 s3 =>
      if w = cx.w then
        (cs.rd cx s3).map fun z =>
          let x := cs.regLane d.n
          let y := cs.regLane s2.n
          cs.setReg w d fun l =>
            match form with
            | .f132 => cx.sFmaLane op l (x l) (z l) (y l)
            | .f213 => cx.sFmaLane op l (y l) (x l) (z l)
            | .f231 => cx.sFmaLane op l (y l) (z l) (x l)
      else none
  | .vshufpd w d s1 s2 imm =>
      if w = cx.w then
        (cs.rd cx s2).map fun f => cs.setReg w d (shufpdLane imm (cs.regLane s1.n) f)
      else none
  | .vshuff64x2 w d s1 s2 imm =>
      if w = cx.w ∧ w ≠ .x then
        (cs.rd cx s2).map fun f => cs.setReg w d (shuffLane w imm (cs.regLane s1.n) f)
      else none
  | .vzero d => some (cs.setReg cx.w d fun _ => .bits 0)
  | _ => none

/-- Run a block symbolically. -/
def crun (cx : Ctx) : List Instr → CState → Option CState
  | [], cs => some cs
  | i :: rest, cs =>
      match cstep cx cs i with
      | some cs' => crun cx rest cs'
      | none => none

/-- The context of a specification. -/
def Spec.ctx (sp : Spec) (w : W) (consts : String → Option (Array UInt64)) : Ctx :=
  let idx : HashMap SNode Nat :=
    (List.range sp.nodes.size).foldl (fun m i => m.insert sp.nodes[i]! i) {}
  let outs : HashMap Mem (Array Nat) := sp.outs.foldl (fun m (c, ids) => m.insert c ids) {}
  { w, nodes := sp.nodes, find := fun nd => idx[nd]?, consts, outOf := fun m => outs[m]? }

/-- Accept a block: the symbolic run succeeds, every stored operand holds the nodes the
specification names, and every operand of the specification is stored. -/
def check (consts : String → Option (Array UInt64)) (sp : Spec) (w : W) (is : List Instr) : Bool :=
  let cx := sp.ctx w consts
  match crun cx is {} with
  | some cs => sp.outs.all fun (m, ids) => decide (m ∈ cs.done) && decide (cx.outOf m = some ids)
  | none => false

/-- Where and why a block is rejected (for the generator's error message; not part of the
proved checker). -/
def checkWhy (consts : String → Option (Array UInt64)) (sp : Spec) (w : W) (is : List Instr) :
    String := Id.run do
  let cx := sp.ctx w consts
  let mut cs : CState := {}
  let mut pos := 0
  -- the instruction that last wrote each register, and the state before it
  let mut lastDef : HashMap Nat (Instr × CState) := {}
  let mut firstJunk : String := ""
  let lanes (c : CState) (n : Nat) : String := toString (repr ((List.range w.lanes).map (c.regLane n)))
  let srcLanes (c : CState) (v : VSrc) : String :=
    match c.rd cx v with
    | some f => toString (repr ((List.range w.lanes).map f))
    | none => "unreadable"
  for i in is do
    match cstep cx cs i with
    | some cs' =>
        match i with
        | .vmov _ d _ | .vbin _ _ d _ _ | .vfma _ _ _ d _ _ | .vshufpd _ d _ _ _
        | .vshuff64x2 _ d _ _ _ | .vzero d =>
            lastDef := lastDef.insert d.n (i, cs)
            -- the first instruction whose result is no value of the specification
            if firstJunk == "" && (List.range w.lanes).any (fun l => cs'.regLane d.n l == .junk) then
              let ops : String := match i with
                | .vmov _ _ src => srcLanes cs src
                | .vbin _ _ _ s1 s2 => s!"{lanes cs s1.n} {srcLanes cs s2}"
                | .vfma _ _ _ d s2 s3 => s!"{lanes cs d.n} {lanes cs s2.n} {srcLanes cs s3}"
                | .vshufpd _ _ s1 s2 _ | .vshuff64x2 _ _ s1 s2 _ => s!"{lanes cs s1.n} {srcLanes cs s2}"
                | _ => ""
              firstJunk := s!"; first result outside the specification: instruction {pos} {i.print} with operands {ops}"
        | _ => pure ()
        cs := cs'
    | none =>
        let detail : String := match i with
          | .vstore _ m r =>
              let d : String := match lastDef[r.n]? with
                | some (j, c) =>
                    let ops : String := match j with
                      | .vbin _ _ _ s1 s2 => s!"{lanes c s1.n} {srcLanes c s2}"
                      | .vfma _ _ _ d s2 s3 => s!"{lanes c d.n} {lanes c s2.n} {srcLanes c s3}"
                      | .vshufpd _ _ s1 s2 _ | .vshuff64x2 _ _ s1 s2 _ => s!"{lanes c s1.n} {srcLanes c s2}"
                      | _ => ""
                    s!"; defined by {j.print} with operands {ops}"
                | none => ""
              let want : String := match cx.outOf m with
                | some ids => toString (repr (ids.map fun i => (i, sp.nodes[i]!)))
                | none => "nothing"
              s!"; register lanes {lanes cs r.n}, wanted {want}{d}"
          | _ => ""
        return s!"instruction {pos} rejected: {i.print}{detail}{firstJunk}"
    pos := pos + 1
  for (m, _) in sp.outs do
    unless cs.done.contains m do return s!"{m.addr} is never stored"
  return "outputs differ"

/-! ## Building specifications -/

structure SBState where
  nodes : Array SNode := #[]
  idx : HashMap SNode Nat := {}

abbrev SpecB := StateM SBState

/-- The node `nd` (shared when it exists). -/
def SpecB.node (nd : SNode) : SpecB Nat :=
  modifyGet fun s =>
    match s.idx[nd]? with
    | some i => (i, s)
    | none => (s.nodes.size, { nodes := s.nodes.push nd, idx := s.idx.insert nd s.nodes.size })

/-- The node of an operation of a kernel, given the nodes of the slots. -/
def kopNode (g : Nat → Nat) : KOp → SNode
  | .cst c => .bits c.toFloat.toBits
  | .zero => .bits 0
  | .add a b => .add (g a) (g b)
  | .sub a b => .sub (g a) (g b)
  | .mul a b => .mul (g a) (g b)
  | .neg a => .neg (g a)
  | .fma a b c => .fma (g a) (g b) (g c)
  | .fms a b c => .fms (g a) (g b) (g c)
  | .fnma a b c => .fnma (g a) (g b) (g c)

/-- One instance of a kernel on the nodes `inp`: the nodes of its outputs. -/
def SpecB.kernel (k : Kernel) (inp : Array Nat) : SpecB (Array Nat) := do
  let mut env := inp
  for op in k.ops do
    let e := env
    env := env.push (← SpecB.node (kopNode (fun i => e.getD i 0) op))
  return k.outs.map fun o => env.getD o 0

/-- Finish a specification. -/
def SpecB.spec (b : SpecB (List (Mem × Array Nat))) : Spec :=
  let (outs, s) := b.run {}
  { nodes := s.nodes, outs }

end LeanFFTW.Asm
