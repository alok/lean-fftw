/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Sym
import Std.Data.HashMap

/-!
# Kernels: common-subexpression elimination, evaluation, and C printing

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

Printing as C is the **trusted printing step** (docs/TRUST.md): every operation is printed
as the corresponding C operation on `double`s (`+ - * -x fma`) or the corresponding
lane-wise vector intrinsic, so the C code performs exactly the binary64 operations of
`Kernel.eval floatArith`.
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

/-! ## C printing -/

/-- Target instruction sets for printing. -/
inductive Target where
  /-- scalar `double` -/
  | scalar
  /-- AVX2 + FMA, 4 independent lanes per `__m256d` -/
  | avx2
  /-- AVX-512, 8 independent lanes per `__m512d` -/
  | avx512
  deriving BEq, Inhabited

def Target.ty : Target → String
  | .scalar => "double"
  | .avx2 => "__m256d"
  | .avx512 => "__m512d"

/-- Number of lanes. -/
def Target.vl : Target → Nat
  | .scalar => 1
  | .avx2 => 4
  | .avx512 => 8

/-- Intrinsic prefix of a vector target. -/
def Target.pre : Target → String
  | .scalar => ""
  | .avx2 => "_mm256"
  | .avx512 => "_mm512"

/-- Print the operation defining variable `d`, with operand names given by `n`. Vector
targets apply the scalar operation in every lane (`_add_pd`, `_sub_pd`, `_mul_pd`, sign
flip by `xor` with `-0.0`, and the fused `_fmadd_pd` = `a*b+c`, `_fmsub_pd` = `a*b-c`,
`_fnmadd_pd` = `-(a*b)+c`, each with one rounding). -/
def KOp.toC (t : Target) (d : String) (n : Nat → String) (op : KOp) : String :=
  let ty := t.ty
  let p := t.pre
  match t, op with
  | .scalar, .cst c => s!"const double {d} = {c.cLiteral};"
  | .scalar, .zero => s!"const double {d} = 0.0;"
  | .scalar, .add a b => s!"const double {d} = {n a} + {n b};"
  | .scalar, .sub a b => s!"const double {d} = {n a} - {n b};"
  | .scalar, .mul a b => s!"const double {d} = {n a} * {n b};"
  | .scalar, .neg a => s!"const double {d} = -{n a};"
  | .scalar, .fma a b c => s!"const double {d} = fma({n a}, {n b}, {n c});"
  | .scalar, .fms a b c => s!"const double {d} = fma({n a}, {n b}, -{n c});"
  | .scalar, .fnma a b c => s!"const double {d} = fma(-{n a}, {n b}, {n c});"
  | _, .cst c => s!"const {ty} {d} = {p}_set1_pd({c.cLiteral});"
  | _, .zero => s!"const {ty} {d} = {p}_setzero_pd();"
  | _, .add a b => s!"const {ty} {d} = {p}_add_pd({n a}, {n b});"
  | _, .sub a b => s!"const {ty} {d} = {p}_sub_pd({n a}, {n b});"
  | _, .mul a b => s!"const {ty} {d} = {p}_mul_pd({n a}, {n b});"
  | _, .neg a => s!"const {ty} {d} = {p}_xor_pd({n a}, {p}_set1_pd(-0.0));"
  | _, .fma a b c => s!"const {ty} {d} = {p}_fmadd_pd({n a}, {n b}, {n c});"
  | _, .fms a b c => s!"const {ty} {d} = {p}_fmsub_pd({n a}, {n b}, {n c});"
  | _, .fnma a b c => s!"const {ty} {d} = {p}_fnmadd_pd({n a}, {n b}, {n c});"

/-- A kernel placed in a C function: its lines, and the C names of its outputs. -/
structure Inst where
  lines : List String
  outs : Array String

/-- Place a kernel in a C function: inputs are bound to the C expressions `bind i`, and
slot `s ≥ nIn` is the variable `{pfx}t{s}` (distinct prefixes keep instances apart). -/
def Kernel.inst (k : Kernel) (t : Target) (ind pfx : String) (bind : Nat → String) : Inst :=
  let n (s : Nat) : String := if s < k.nIn then bind s else s!"{pfx}t{s}"
  let lines := (List.range k.ops.size).map fun i =>
    ind ++ (k.ops[i]!).toC t (n (k.nIn + i)) n
  ⟨lines, k.outs.map n⟩

end LeanFFTW.Gen
