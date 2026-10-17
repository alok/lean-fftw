/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.SExpr
import LeanFFTW.Core.Alg

/-!
# Symbolic complex arithmetic: running the generic algorithms on expressions

`SC` is a symbolic complex value: either a known twiddle constant `ω_n^k`, or a pair of
real expressions. `symOps` is an instance of the generic `Ops` interface, so the *same*
`exec`/`mkPlan` that are proved correct in `LeanFFTW/Proof/Exact.lean` produce, when run on
symbolic inputs, the straight-line code of a kernel.

Multiplication by a twiddle constant is canonicalized: the angle is reduced to a quarter
turn `i^q` (exact component swaps and negations) times a rotation by `β ∈ [0, π/2)`;
`β = 0` costs nothing, `β = π/4` costs two multiplications, and other angles cost two
fused multiply-adds and two multiplications by `cos β`, which FMA contraction folds into
the butterfly additions that follow.
-/

namespace LeanFFTW.Gen

/-- Symbolic complex values. -/
inductive SC where
  /-- the twiddle `exp (∓2πi k / n)` (`-` when `fwd`) -/
  | tw (fwd : Bool) (n k : Nat)
  /-- `re + i·im` -/
  | val (re im : SExpr)
  deriving Inhabited

open SExpr

namespace SC

/-- Multiply `re + i·im` by `i`. -/
def mulI (re im : SExpr) : SExpr × SExpr := (mkNeg im, re)

/-- Multiply by `i^q`. -/
def mulIPow (q : Nat) (re im : SExpr) : SExpr × SExpr :=
  match q % 4 with
  | 0 => (re, im)
  | 1 => (mkNeg im, re)
  | 2 => (mkNeg re, mkNeg im)
  | _ => (im, mkNeg re)

/-- Multiply `a + ib` by `exp(iθ)`, `θ = 2π k / n ∈ [0, π/2)`, `n > 0`. -/
def rotQ (k n : Nat) (a b : SExpr) : SExpr × SExpr :=
  if k == 0 then (a, b)
  else if 8 * k == n then
    -- (a + ib)(1 + i)/√2 = ((a - b) + i(a + b)) · √2/2
    (mkMulC .sqrthalf (mkSub a b), mkMulC .sqrthalf (mkAdd a b))
  else
    -- (a + ib)(c + is) = c·(a - tb) + i·c·(b + ta), t = s/c = tan θ: one fused operation
    -- per part, and the product by c fuses into the additions that consume the result
    -- (`SExpr.contract`). Use the octant to keep 0 < θ < π/4, so 0 < t < 1.
    if 8 * k < n then
      (mkMulC (.cos k n) (mkFnmaC (.tan k n) b a), mkMulC (.cos k n) (mkFmaC (.tan k n) a b))
    else
      -- θ = π/2 - φ, φ = 2π(n/4 - k)/n: (a + ib)(s' + ic') = c'·(t'a - b) + i·c'·(a + t'b)
      let k' := n - 4 * k  -- φ = 2π k' / (4n)
      (mkMulC (.cos k' (4 * n)) (mkFmsC (.tan k' (4 * n)) a b),
       mkMulC (.cos k' (4 * n)) (mkFmaC (.tan k' (4 * n)) b a))

/-- Multiply `a + ib` by `exp(± 2πi k/n)` (`-` when `fwd`), `n > 0`. -/
def rot (fwd : Bool) (n k : Nat) (a b : SExpr) : SExpr × SExpr :=
  let k := k % n
  -- exp(-2πik/n) = exp(2πi(n-k)/n)
  let k := if fwd then (n - k) % n else k
  -- angle 2πk/n = q·(π/2) + 2πk₁/(4n) with q = ⌊4k/n⌋, k₁ = 4k - q n ∈ [0, n)
  let q := 4 * k / n
  let k₁ := 4 * k - q * n
  let (a', b') := rotQ k₁ (4 * n) a b
  mulIPow q a' b'

/-- The real and imaginary parts of a symbolic value. -/
def parts : SC → SExpr × SExpr
  | .val re im => (re, im)
  | .tw fwd n k =>
      let (c, s) := rot fwd n k (.cst (.cos 0 1)) .zero
      (c, s)

def add (x y : SC) : SC :=
  let (a, b) := x.parts
  let (c, d) := y.parts
  .val (mkAdd a c) (mkAdd b d)

def sub (x y : SC) : SC :=
  let (a, b) := x.parts
  let (c, d) := y.parts
  .val (mkSub a c) (mkSub b d)

/-- General complex product (only used when neither factor is a known twiddle). -/
def mulGen (x y : SC) : SC :=
  let (a, b) := x.parts
  let (c, d) := y.parts
  .val (.fms a c (.mul b d)) (.fma a d (.mul b c))

def mul : SC → SC → SC
  | .tw fwd n k, .val a b => let (r, i) := rot fwd n k a b; .val r i
  | .val a b, .tw fwd n k => let (r, i) := rot fwd n k a b; .val r i
  | .tw f n k, .tw f' n' k' =>
      -- both constants: keep symbolic by rotating the second's parts
      let (a, b) := (SC.tw f' n' k').parts
      let (r, i) := rot f n k a b; .val r i
  | x, y => mulGen x y

end SC

/-- Symbolic vectors are arrays. -/
def symOps : Ops SC (Array SC) where
  zero := .val .zero .zero
  add := SC.add
  sub := SC.sub
  mul := SC.mul
  tw := fun fwd n k => .tw fwd n k
  build := fun n f => (Array.range n).map f
  get := fun v i => v.getD i (.val .zero .zero)

end LeanFFTW.Gen
