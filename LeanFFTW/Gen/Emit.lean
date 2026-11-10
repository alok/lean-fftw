/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Sym
import Std.Data.HashMap

/-!
# Kernels: common-subexpression elimination and evaluation

A kernel is straight-line code over *slots*: slots `0 … nIn-1` hold the inputs and slot
`nIn + i` holds the result of operation `i` (`Kernel`). `cse` turns the symbolic outputs
of a kernel (`SExpr`s) into a `Kernel`, merging structurally identical subexpressions.

Both kernels and expressions are evaluated over any `Arith` (a choice of the eight
operations); `cse_correct` (in `LeanFFTW/Proof/Kernel.lean`) states that evaluating the
kernel gives the values of the expressions for every `Arith` whose `add`, `mul` and fused
products are commutative in their (first two) arguments, in particular for exact real
arithmetic, which the correctness proofs use. (CSE orders the operands of commutative
operations by slot to improve sharing; for binary64 the floating-point error analysis is
done on the kernel itself, so no commutativity of `Float` operations is assumed.)

Kernels are instantiated as vector code by the assembly back end (`LeanFFTW/Asm`), whose
output is checked against `Kernel.eval` block by block (`LeanFFTW/Asm/Check.lean`).
-/

namespace LeanFFTW.Gen

open Std

/-- The eight operations of kernels, over a scalar type `α`. -/
structure Arith (α : Type) where
  cst : Cst → α
  zero : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  neg : α → α
  /-- `a * b + c` -/
  fma : α → α → α → α
  /-- `a * b - c` -/
  fms : α → α → α → α
  /-- `c - a * b` -/
  fnma : α → α → α → α

/-- Binary64: Lean `Float` operations (IEEE, round to nearest even; `fma` rounds once). -/
def floatArith : Arith Float where
  cst c := c.toFloat
  zero := 0.0
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  neg a := -a
  fma a b c := Float.fma a b c
  fms a b c := Float.fma a b (-c)
  fnma a b c := Float.fma (-a) b c

/-- Evaluate an expression over `A`. -/
def SExpr.evalWith {α : Type} (A : Arith α) (env : Nat → α) : SExpr → α
  | .input i => env i
  | .zero => A.zero
  | .cst c => A.cst c
  | .add a b => A.add (a.evalWith A env) (b.evalWith A env)
  | .sub a b => A.sub (a.evalWith A env) (b.evalWith A env)
  | .mul a b => A.mul (a.evalWith A env) (b.evalWith A env)
  | .neg a => A.neg (a.evalWith A env)
  | .fma a b c => A.fma (a.evalWith A env) (b.evalWith A env) (c.evalWith A env)
  | .fms a b c => A.fms (a.evalWith A env) (b.evalWith A env) (c.evalWith A env)
  | .fnma a b c => A.fnma (a.evalWith A env) (b.evalWith A env) (c.evalWith A env)

/-- One kernel operation; operands are slots. -/
inductive KOp where
  | cst (c : Cst)
  | zero
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  | fma (a b c : Nat)
  | fms (a b c : Nat)
  | fnma (a b c : Nat)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Straight-line code: `nIn` inputs, operations, and the slots of the outputs. -/
structure Kernel where
  nIn : Nat
  ops : Array KOp
  outs : Array Nat
  deriving Inhabited

/-- Apply an operation to the values `g` of the slots. -/
def KOp.eval {α : Type} (A : Arith α) (g : Nat → α) : KOp → α
  | .cst c => A.cst c
  | .zero => A.zero
  | .add a b => A.add (g a) (g b)
  | .sub a b => A.sub (g a) (g b)
  | .mul a b => A.mul (g a) (g b)
  | .neg a => A.neg (g a)
  | .fma a b c => A.fma (g a) (g b) (g c)
  | .fms a b c => A.fms (g a) (g b) (g c)
  | .fnma a b c => A.fnma (g a) (g b) (g c)

/-- Values of all slots, given the inputs. -/
def Kernel.slots {α : Type} [Inhabited α] (A : Arith α) (k : Kernel) (inp : Array α) :
    Array α :=
  k.ops.foldl (fun env op => env.push (op.eval A fun i => env.getD i default)) inp

/-- Values of the outputs. -/
def Kernel.eval {α : Type} [Inhabited α] (A : Arith α) (k : Kernel) (inp : Array α) :
    Array α :=
  let env := k.slots A inp
  k.outs.map fun o => env.getD o default

/-! ## Common-subexpression elimination -/

structure CSEState where
  map : HashMap KOp Nat := {}
  ops : Array KOp := #[]

/-- The slot of an operation, reusing an existing slot for an identical operation. -/
def node (nIn : Nat) (op : KOp) (s : CSEState) : Nat × CSEState :=
  match s.map[op]? with
  | some v => (v, s)
  | none => (nIn + s.ops.size, { map := s.map.insert op (nIn + s.ops.size), ops := s.ops.push op })

/-- Commutative operations get their operands in slot order. -/
def ord2 (x y : Nat) (f : Nat → Nat → KOp) : KOp := if x ≤ y then f x y else f y x

/-- Slot of an expression (inputs `i < nIn` are slot `i`), threading the CSE state. -/
def cseExpr (nIn : Nat) : SExpr → CSEState → Nat × CSEState
  | .input i, s => (i, s)
  | .zero, s => node nIn .zero s
  | .cst c, s => node nIn (.cst c) s
  | .add a b, s =>
      let r1 := cseExpr nIn a s
      let r2 := cseExpr nIn b r1.2
      node nIn (ord2 r1.1 r2.1 .add) r2.2
  | .sub a b, s =>
      let r1 := cseExpr nIn a s
      let r2 := cseExpr nIn b r1.2
      node nIn (.sub r1.1 r2.1) r2.2
  | .mul a b, s =>
      let r1 := cseExpr nIn a s
      let r2 := cseExpr nIn b r1.2
      node nIn (ord2 r1.1 r2.1 .mul) r2.2
  | .neg a, s =>
      let r1 := cseExpr nIn a s
      node nIn (.neg r1.1) r1.2
  | .fma a b c, s =>
      let r1 := cseExpr nIn a s
      let r2 := cseExpr nIn b r1.2
      let r3 := cseExpr nIn c r2.2
      node nIn (ord2 r1.1 r2.1 fun x y => .fma x y r3.1) r3.2
  | .fms a b c, s =>
      let r1 := cseExpr nIn a s
      let r2 := cseExpr nIn b r1.2
      let r3 := cseExpr nIn c r2.2
      node nIn (ord2 r1.1 r2.1 fun x y => .fms x y r3.1) r3.2
  | .fnma a b c, s =>
      let r1 := cseExpr nIn a s
      let r2 := cseExpr nIn b r1.2
      let r3 := cseExpr nIn c r2.2
      node nIn (ord2 r1.1 r2.1 fun x y => .fnma x y r3.1) r3.2

/-- Slots of a list of expressions. -/
def cseList (nIn : Nat) : List SExpr → CSEState → List Nat × CSEState
  | [], s => ([], s)
  | e :: es, s =>
      let r1 := cseExpr nIn e s
      let r2 := cseList nIn es r1.2
      (r1.1 :: r2.1, r2.2)

/-- The kernel computing `outs` from `nIn` inputs. -/
def cse (nIn : Nat) (outs : Array SExpr) : Kernel :=
  let r := cseList nIn outs.toList {}
  ⟨nIn, r.2.ops, r.1.toArray⟩

/-- Operation counts `(adds/subs/negs, muls, fmas)`. -/
def Kernel.counts (k : Kernel) : Nat × Nat × Nat :=
  k.ops.foldl (fun (a, m, f) op =>
    match op with
    | .add .. | .sub .. | .neg .. => (a + 1, m, f)
    | .mul .. => (a, m + 1, f)
    | .fma .. | .fms .. | .fnma .. => (a, m, f + 1)
    | _ => (a, m, f)) (0, 0, 0)

end LeanFFTW.Gen
