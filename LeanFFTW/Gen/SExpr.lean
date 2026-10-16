/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.Trig

/-!
# Symbolic real expressions for kernel generation

`SExpr` is a straight-line real expression over numbered inputs and exact trigonometric
constants, with the operations the kernels execute (`+ - × neg` and the fused forms).
It has two semantics:

* exact, over `ℝ` (in `LeanFFTW/Proof/Gen.lean`), used to prove that generated kernels
  compute DFTs, and
* binary64, `SExpr.evalF`, with Lean `Float` operations (each IEEE-rounded, `fma` with a
  single rounding). The emitted C code performs exactly these operations, operand for
  operand, so `evalF` is the reference the C kernels are tested against bit for bit.

Constants are `cos (2πk/n)` and `sin (2πk/n)` with `0 < k/n < 1/4`, whose binary64
values come from the exact integer trigonometry of `Trig.lean`.
-/

namespace LeanFFTW.Gen

/-- Exact constants. -/
inductive Cst where
  /-- `cos (2πk/n)` -/
  | cos (k n : Nat)
  /-- `sin (2πk/n)` -/
  | sin (k n : Nat)
  /-- `√2/2 = cos(π/4)` -/
  | sqrthalf
  deriving BEq, Hashable, Repr, Inhabited

namespace Cst

/-- Binary64 value of a constant. -/
def toFloat : Cst → Float
  | .cos k n => (Trig.cosSin2Pi k n).1
  | .sin k n => (Trig.cosSin2Pi k n).2
  | .sqrthalf => (Trig.cosSin2Pi 1 8).1

/-- A C literal that denotes exactly the binary64 value (hexadecimal float). -/
def cLiteral (c : Cst) : String :=
  let b := c.toFloat.toBits
  let frac := b &&& 0xFFFFFFFFFFFFF
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let hex := String.ofList ((Nat.toDigits 16 frac.toNat).leftpad 13 '0')
  if e == 0 then "0.0" else s!"0x1.{hex}p{(e : Int) - 1023}"

end Cst

/-- Symbolic real expressions. -/
inductive SExpr where
  | input (i : Nat)
  | zero
  | cst (c : Cst)
  | add (a b : SExpr)
  | sub (a b : SExpr)
  | mul (a b : SExpr)
  | neg (a : SExpr)
  /-- `a * b + c`, one rounding -/
  | fma (a b c : SExpr)
  /-- `a * b - c`, one rounding -/
  | fms (a b c : SExpr)
  /-- `c - a * b`, one rounding -/
  | fnma (a b c : SExpr)
  deriving Inhabited, Repr

namespace SExpr

/-- Binary64 semantics. -/
def evalF (env : Nat → Float) : SExpr → Float
  | .input i => env i
  | .zero => 0.0
  | .cst c => c.toFloat
  | .add a b => evalF env a + evalF env b
  | .sub a b => evalF env a - evalF env b
  | .mul a b => evalF env a * evalF env b
  | .neg a => -(evalF env a)
  | .fma a b c => Float.fma (evalF env a) (evalF env b) (evalF env c)
  | .fms a b c => Float.fma (evalF env a) (evalF env b) (-(evalF env c))
  | .fnma a b c => Float.fma (-(evalF env a)) (evalF env b) (evalF env c)

/-! Smart constructors: local simplifications that are identities of real arithmetic
(and also exact in binary64 when they only remove `+0`, `-0`, double negation, or move a
negation into a subtraction). -/

def isZero : SExpr → Bool
  | .zero => true
  | _ => false

def mkNeg : SExpr → SExpr
  | .zero => .zero
  | .neg a => a
  | a => .neg a

def mkAdd : SExpr → SExpr → SExpr
  | .zero, b => b
  | a, .zero => a
  | a, .neg b => .sub a b
  | .neg a, b => .sub b a
  | a, b => .add a b

def mkSub : SExpr → SExpr → SExpr
  | a, .zero => a
  | .zero, b => mkNeg b
  | a, .neg b => .add a b
  | .neg a, b => mkNeg (.add a b)
  | a, b => .sub a b

/-- `c * x` for a constant `c`. -/
def mkMulC (c : Cst) : SExpr → SExpr
  | .zero => .zero
  | .neg a => mkNeg (.mul (.cst c) a)
  | a => .mul (.cst c) a

/-- `c1*a + c2*b` with one product fused. -/
def mkFmaAdd (c1 : Cst) (a : SExpr) (c2 : Cst) (b : SExpr) : SExpr :=
  match a, b with
  | .zero, _ => mkMulC c2 b
  | _, .zero => mkMulC c1 a
  | _, _ => .fma (.cst c1) a (mkMulC c2 b)

/-- `c1*a - c2*b` with one product fused. -/
def mkFmaSub (c1 : Cst) (a : SExpr) (c2 : Cst) (b : SExpr) : SExpr :=
  match a, b with
  | .zero, _ => mkNeg (mkMulC c2 b)
  | _, .zero => mkMulC c1 a
  | _, _ => .fms (.cst c1) a (mkMulC c2 b)

end SExpr

end LeanFFTW.Gen
