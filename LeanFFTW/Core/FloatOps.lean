/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.Alg
import LeanFFTW.Core.Trig

/-!
# Binary64 instantiation of the generic algorithms

Complex scalars are pairs of `Float`; materialized vectors are split-format pairs of
`FloatArray`s. Every arithmetic operation is a Lean `Float` operation, whose logical
meaning is Lean core's IEEE binary64 model (`Float.Model`); the compiled code uses the
C `double` operations behind `@[extern "lean_float_add"]` etc.
-/

namespace LeanFFTW

/-- A binary64 complex number. -/
structure FC where
  re : Float
  im : Float
  deriving Inhabited, Repr

/-- A split-format binary64 complex vector. -/
structure CArr where
  re : FloatArray
  im : FloatArray

instance : Inhabited CArr := ⟨⟨.empty, .empty⟩⟩

namespace CArr

/-- Number of complex entries. -/
@[inline] def size (v : CArr) : Nat := v.re.size

/-- Read entry `i` (`0` out of range). -/
@[inline] def get (v : CArr) (i : Nat) : FC := ⟨v.re.get! i, v.im.get! i⟩

/-- Materialize `f 0, …, f (n-1)`. -/
def ofFn (n : Nat) (f : Nat → FC) : CArr := Id.run do
  let mut re := FloatArray.emptyWithCapacity n
  let mut im := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    let z := f i
    re := re.push z.re
    im := im.push z.im
  return ⟨re, im⟩

end CArr

/-- Binary64 complex multiplication, the textbook formula with four products. -/
@[inline] def FC.mul (a b : FC) : FC :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- Twiddle `exp (∓2πi k/n)` from the exact integer trigonometry of `Trig.lean`. -/
def floatTw (fwd : Bool) (n k : Nat) : FC :=
  let (c, s) := Trig.cosSin2Pi k n
  if fwd then ⟨c, Trig.negZ s⟩ else ⟨c, s⟩

/-- The binary64 operations. -/
def floatOps : Ops FC CArr where
  zero := ⟨0.0, 0.0⟩
  add a b := ⟨a.re + b.re, a.im + b.im⟩
  sub a b := ⟨a.re - b.re, a.im - b.im⟩
  mul := FC.mul
  tw := floatTw
  build := CArr.ofFn
  get := CArr.get

end LeanFFTW
