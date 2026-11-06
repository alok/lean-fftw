/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Stockham

/-!
# Operation counts of the fast engine (executable)

The cost of a plan, as a number the planner can compute: every arithmetic operation of the
generated kernels, every load of a butterfly input or twiddle and every store of a
butterfly output, each weighted by a `Weights` record.

These functions run inside the planner (no Mathlib). `LeanFFTW/Proof/Cost.lean` writes the
same schedule as a CSLib query program (`Cslib.FreeM`) whose evaluation is
`stockhamWith`, the function the C engine is tested against bit for bit, and proves that
the program's query cost `Cslib.FreeM.cost` is `stockhamCost`, for every oracle. So the
numbers here are the operation counts of the executed algorithm, not annotations.
-/

namespace LeanFFTW.Gen

/-- The cost of each kind of operation of the engine. -/
structure Weights where
  /-- additions, subtractions and negations -/
  add : Nat
  /-- multiplications -/
  mul : Nat
  /-- fused multiply-adds (`fma`, `fms`, `fnma`) -/
  fma : Nat
  /-- loads of butterfly inputs and twiddles -/
  load : Nat
  /-- stores of butterfly outputs -/
  store : Nat
  deriving Repr, Inhabited, BEq

/-- Arithmetic only, one unit per operation (an `fma` is one operation). -/
def Weights.arith : Weights := ⟨1, 1, 1, 0, 0⟩

/-- FFTW's flop convention: an `fma` is two flops; memory is free. -/
def Weights.flops : Weights := ⟨1, 1, 2, 0, 0⟩

/-- Memory accesses only. -/
def Weights.mem : Weights := ⟨0, 0, 0, 1, 1⟩

/-- The cost of one kernel operation (constants and zero are free). -/
def KOp.cost (W : Weights) : KOp → Nat
  | .add .. | .sub .. | .neg .. => W.add
  | .mul .. => W.mul
  | .fma .. | .fms .. | .fnma .. => W.fma
  | .cst _ | .zero => 0

/-- The cost of a list of kernel operations. -/
def opsCost (W : Weights) (ops : List KOp) : Nat := (ops.map (KOp.cost W)).sum

/-- Scalar loads of one butterfly: `R` complex inputs and, when twiddled, `R - 1` complex
twiddles. -/
def bflyLoads (R : Nat) (tw : Bool) : Nat := 2 * R + (if tw then 2 * (R - 1) else 0)

/-- The cost of one butterfly of a pass running kernel `k`. -/
def bflyCost (W : Weights) (k : Kernel) (R : Nat) (tw : Bool) : Nat :=
  bflyLoads R tw * W.load + opsCost W k.ops.toList + k.outs.size * W.store

/-- The cost of pass `t` of the plan `rs`: `N / R` butterflies. -/
def passCost (W : Weights) (fwd : Bool) (N : Nat) (rs : Array Nat) (t : Nat) : Nat :=
  (N / rs.getD t 1) * bflyCost W (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1) (t ≥ 1)

/-- The cost of the whole Stockham schedule of the plan `rs`. -/
def stockhamCost (W : Weights) (fwd : Bool) (N : Nat) (rs : Array Nat) : Nat :=
  ((List.range rs.size).map (passCost W fwd N rs)).sum

end LeanFFTW.Gen
