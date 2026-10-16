/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Sym
import Std.Data.HashMap

/-!
# Kernel emission: common-subexpression elimination and C printing

This is the **trusted printing step** of the pipeline (see docs/TRUST.md): it turns the
symbolic outputs of a kernel into straight-line SSA code and prints it as C. Every SSA
instruction is one of the `SExpr` operations, printed as the corresponding C operation
(`+`, `-`, `*`, unary `-`, `fma`) on `double`s or the corresponding AVX-512 intrinsic on
`__m512d` lanes, so the C code performs exactly the binary64 operations of
`SExpr.evalF`. CSE only merges structurally identical subexpressions, which denote the
same value under any deterministic semantics.
-/

namespace LeanFFTW.Gen

open Std

/-- One SSA instruction. Operands are SSA names. -/
inductive Instr where
  | cst (dst : String) (c : Cst)
  | zero (dst : String)
  | add (dst a b : String)
  | sub (dst a b : String)
  | mul (dst a b : String)
  | neg (dst a : String)
  | fma (dst a b c : String)
  | fms (dst a b c : String)
  | fnma (dst a b c : String)
  deriving Inhabited, Repr

structure CSEState where
  map : HashMap String String := {}
  code : Array Instr := #[]
  next : Nat := 0

abbrev CSEM := StateM CSEState

def fresh (key : String) (mk : String → Instr) : CSEM String := do
  let s ← get
  match s.map.get? key with
  | some v => return v
  | none =>
    let v := s!"t{s.next}"
    set { s with map := s.map.insert key v, code := s.code.push (mk v), next := s.next + 1 }
    return v

/-- Names of inputs are supplied by the caller (`inName i`). -/
partial def cse (inName : Nat → String) : SExpr → CSEM String
  | .input i => return inName i
  | .zero => fresh "0" .zero
  | .cst c => fresh s!"c {repr c}" (fun v => .cst v c)
  | .add a b => do
      let x ← cse inName a; let y ← cse inName b
      -- addition is commutative in binary64: canonical operand order improves sharing
      let (x, y) := if x ≤ y then (x, y) else (y, x)
      fresh s!"+ {x} {y}" (fun v => .add v x y)
  | .sub a b => do
      let x ← cse inName a; let y ← cse inName b
      fresh s!"- {x} {y}" (fun v => .sub v x y)
  | .mul a b => do
      let x ← cse inName a; let y ← cse inName b
      let (x, y) := if x ≤ y then (x, y) else (y, x)
      fresh s!"* {x} {y}" (fun v => .mul v x y)
  | .neg a => do
      let x ← cse inName a
      fresh s!"n {x}" (fun v => .neg v x)
  | .fma a b c => do
      let x ← cse inName a; let y ← cse inName b; let z ← cse inName c
      let (x, y) := if x ≤ y then (x, y) else (y, x)
      fresh s!"fma {x} {y} {z}" (fun v => .fma v x y z)
  | .fms a b c => do
      let x ← cse inName a; let y ← cse inName b; let z ← cse inName c
      let (x, y) := if x ≤ y then (x, y) else (y, x)
      fresh s!"fms {x} {y} {z}" (fun v => .fms v x y z)
  | .fnma a b c => do
      let x ← cse inName a; let y ← cse inName b; let z ← cse inName c
      let (x, y) := if x ≤ y then (x, y) else (y, x)
      fresh s!"fnma {x} {y} {z}" (fun v => .fnma v x y z)

/-- A straight-line kernel: SSA code plus the SSA names of its outputs. -/
structure SSA where
  code : Array Instr
  outs : Array String
  deriving Inhabited

/-- Run CSE over a list of output expressions. -/
def toSSA (inName : Nat → String) (outs : Array SExpr) : SSA :=
  let (names, s) := (outs.mapM (cse inName)).run {}
  ⟨s.code, names⟩

/-- Operation counts `(adds/subs/negs, muls, fmas)`. -/
def SSA.counts (k : SSA) : Nat × Nat × Nat :=
  k.code.foldl (fun (a, m, f) i =>
    match i with
    | .add .. | .sub .. | .neg .. => (a + 1, m, f)
    | .mul .. => (a, m + 1, f)
    | .fma .. | .fms .. | .fnma .. => (a, m, f + 1)
    | _ => (a, m, f)) (0, 0, 0)

/-- Binary64 evaluation of SSA code (inputs by name). Used to cross-check the CSE step
against `SExpr.evalF`. -/
def SSA.evalF (k : SSA) (inp : String → Float) : Array Float := Id.run do
  let mut env : HashMap String Float := {}
  let look (env : HashMap String Float) (v : String) : Float := (env.get? v).getD (inp v)
  for i in k.code do
    env := match i with
      | .cst d c => env.insert d c.toFloat
      | .zero d => env.insert d 0.0
      | .add d a b => env.insert d (look env a + look env b)
      | .sub d a b => env.insert d (look env a - look env b)
      | .mul d a b => env.insert d (look env a * look env b)
      | .neg d a => env.insert d (-(look env a))
      | .fma d a b c => env.insert d (Float.fma (look env a) (look env b) (look env c))
      | .fms d a b c => env.insert d (Float.fma (look env a) (look env b) (-(look env c)))
      | .fnma d a b c => env.insert d (Float.fma (-(look env a)) (look env b) (look env c))
  return k.outs.map (look env)

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

/-- Print one instruction. Vector targets apply the scalar operation in every lane
(`_add_pd`, `_sub_pd`, `_mul_pd`, sign flip by `xor` with `-0.0`, and the fused
`_fmadd_pd` = `a*b+c`, `_fmsub_pd` = `a*b-c`, `_fnmadd_pd` = `-(a*b)+c`, each with one
rounding). -/
def Instr.toC (t : Target) (i : Instr) : String :=
  let ty := t.ty
  let p := t.pre
  match t, i with
  | .scalar, .cst d c => s!"const double {d} = {c.cLiteral};"
  | .scalar, .zero d => s!"const double {d} = 0.0;"
  | .scalar, .add d a b => s!"const double {d} = {a} + {b};"
  | .scalar, .sub d a b => s!"const double {d} = {a} - {b};"
  | .scalar, .mul d a b => s!"const double {d} = {a} * {b};"
  | .scalar, .neg d a => s!"const double {d} = -{a};"
  | .scalar, .fma d a b c => s!"const double {d} = fma({a}, {b}, {c});"
  | .scalar, .fms d a b c => s!"const double {d} = fma({a}, {b}, -{c});"
  | .scalar, .fnma d a b c => s!"const double {d} = fma(-{a}, {b}, {c});"
  | _, .cst d c => s!"const {ty} {d} = {p}_set1_pd({c.cLiteral});"
  | _, .zero d => s!"const {ty} {d} = {p}_setzero_pd();"
  | _, .add d a b => s!"const {ty} {d} = {p}_add_pd({a}, {b});"
  | _, .sub d a b => s!"const {ty} {d} = {p}_sub_pd({a}, {b});"
  | _, .mul d a b => s!"const {ty} {d} = {p}_mul_pd({a}, {b});"
  | _, .neg d a => s!"const {ty} {d} = {p}_xor_pd({a}, {p}_set1_pd(-0.0));"
  | _, .fma d a b c => s!"const {ty} {d} = {p}_fmadd_pd({a}, {b}, {c});"
  | _, .fms d a b c => s!"const {ty} {d} = {p}_fmsub_pd({a}, {b}, {c});"
  | _, .fnma d a b c => s!"const {ty} {d} = {p}_fnmadd_pd({a}, {b}, {c});"

def SSA.bodyC (k : SSA) (t : Target) (indent : String := "  ") : String :=
  String.join (k.code.toList.map fun i => indent ++ i.toC t ++ "\n")

end LeanFFTW.Gen
