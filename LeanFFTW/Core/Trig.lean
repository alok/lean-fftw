/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/

/-!
# Twiddle factors from integer arithmetic

`cos (2πk/n)` and `sin (2πk/n)` are computed with fixed-point integer arithmetic
(`precBits` fractional bits) and then rounded to the nearest binary64 value, ties to even.
Nothing here calls the C math library, so every value is determined by Lean definitions
(the compiled code only uses arbitrary-precision `Nat`/`Int` arithmetic).

The angle is first reduced exactly, using the rational number `k/n`, to an octant
`θ ∈ [0, π/4]`; the Taylor series is then summed until the terms vanish at the working
precision. The fixed-point result has an absolute error of a few units of `2^-precBits`,
far below half an ulp of the final double, so the result is the correctly rounded value
except in astronomically unlikely near-tie cases. The accuracy statement used by the
floating-point error theorem is the weaker `|ŵ - w| ≤ 2^-53 |w| + 2^-100`, see
`LeanFFTW/Proof/Twiddle.lean`.
-/

namespace LeanFFTW.Trig

/-- Working precision in fractional bits. -/
def precBits : Nat := 160

/-- π to 60 decimal digits. -/
def piDigits : Nat := 3141592653589793238462643383279502884197169399375105820974944
/-- `piDigits = ⌊π · 10^60⌋`. -/
def piScale : Nat := 10 ^ 60

/-- `⌊π · 2^precBits⌋` (to within one unit). -/
def piFixed : Nat := piDigits * 2 ^ precBits / piScale

/-- Fixed-point multiply: `⌊a·b / 2^precBits⌋`. -/
@[inline] def fmul (a b : Nat) : Nat := a * b / 2 ^ precBits

/-- `θ · 2^precBits` for `θ = 2π · num / den`, with `num/den ∈ [0, 1/8]`. -/
def angleFixed (num den : Nat) : Nat := 2 * piFixed * num / den

/-- Taylor series for `cos θ` and `sin θ` at fixed point, `0 ≤ θ ≤ π/4`.
Returns `(cos θ · 2^p, sin θ · 2^p)` approximately. -/
def cosSinFixed (θ : Nat) : Nat × Nat := Id.run do
  let one := 2 ^ precBits
  let θ2 := fmul θ θ
  -- cos: Σ (-1)^j θ^(2j)/(2j)!, sin: Σ (-1)^j θ^(2j+1)/(2j+1)!
  let mut cPos : Nat := one
  let mut cNeg : Nat := 0
  let mut sPos : Nat := θ
  let mut sNeg : Nat := 0
  let mut tc : Nat := one   -- current cos term magnitude θ^(2j)/(2j)!
  let mut ts : Nat := θ     -- current sin term magnitude θ^(2j+1)/(2j+1)!
  for j in [1:40] do
    tc := fmul tc θ2 / ((2 * j - 1) * (2 * j))
    ts := fmul ts θ2 / ((2 * j) * (2 * j + 1))
    if j % 2 == 1 then
      cNeg := cNeg + tc
      sNeg := sNeg + ts
    else
      cPos := cPos + tc
      sPos := sPos + ts
  return (cPos - cNeg, sPos - sNeg)

/-- Round a nonnegative fixed-point value `v · 2^-precBits` to the nearest binary64,
ties to even. Assumes the result is a normal number (true for all twiddles: they are
`0` or at least `2^-40` in magnitude for `n < 2^38`). -/
def fixedToFloat (v : Nat) : Float :=
  if v == 0 then 0.0 else
  let lg := Nat.log2 v               -- 2^lg ≤ v < 2^(lg+1)
  -- normalize to a 53-bit significand q' with value q' · 2^(lg - 52 - precBits)
  let q' :=
    if lg ≤ 52 then v <<< (52 - lg)
    else
      let sh := lg - 52
      let q := v >>> sh
      let r := v - (q <<< sh)
      let half := 1 <<< (sh - 1)
      if r > half then q + 1
      else if r < half then q
      else if q % 2 == 0 then q else q + 1
  -- a rounding carry can produce 2^53
  let (q'', lg') := if q' == 2 ^ 53 then (2 ^ 52, lg + 1) else (q', lg)
  -- binary64: value = (2^52 + frac) · 2^(E - 1075), so E = lg' - precBits + 1023
  let e : Int := (lg' : Int) - precBits + 1023
  let frac := q'' - 2 ^ 52
  Float.ofBits (UInt64.ofNat ((e.toNat <<< 52) ||| frac))

/-- Negation that never produces `-0.0` (keeps twiddle zeros positive). -/
@[inline] def negZ (x : Float) : Float := if x == 0.0 then 0.0 else -x

/-- `(cos φ, sin φ)` for `φ = 2π · num / (8n)`, `0 ≤ num ≤ n`, as binary64. -/
def smallAt (n num : Nat) : Float × Float :=
  let (c, s) := cosSinFixed (angleFixed num (8 * n))
  (fixedToFloat c, fixedToFloat s)

/-- The exact octant reduction of `cosSin2Pi`, parameterized by the evaluator `small` of
the reduced angle (`small num ≈ (cos, sin) (2π · num / (8n))`, `num ≤ n`). -/
@[inline] def cosSin2PiWith (small : Nat → Float × Float) (k n : Nat) : Float × Float :=
  if n == 0 then (1.0, 0.0) else
  let k := k % n
  -- position in eighths of a turn: 8k = oct·n + rem, 0 ≤ rem < n
  let oct := (8 * k) / n
  let rem := (8 * k) % n
  -- angle = (oct + rem/n) · π/4.  Reduce to φ ∈ [0, π/4] using exact symmetries.
  -- For odd octants use the complementary angle (n - rem)/(8n).
  let (c, s) := if oct % 2 == 0 then small rem else small (n - rem)
  -- (C, S) = (cos φ, sin φ); map back per octant
  match oct with
  | 0 => (c, s)
  | 1 => (s, c)
  | 2 => (negZ s, c)
  | 3 => (negZ c, s)
  | 4 => (negZ c, negZ s)
  | 5 => (negZ s, negZ c)
  | 6 => (s, negZ c)
  | _ => (c, negZ s)

/-- `(cos (2π k/n), sin (2π k/n))` as binary64, computed from exact integer arithmetic.
Requires `n > 0`; `k` is reduced modulo `n`. -/
def cosSin2Pi (k n : Nat) : Float × Float := cosSin2PiWith (smallAt n) k n

/-- The table `m ↦ cosSin2Pi m n` for `m < n`. Every reduced angle `num` is a multiple of
`g = gcd 8 n`, so only `n / g + 1` values are evaluated; entry `m` is computed by the same
`cosSin2PiWith` as `cosSin2Pi m n`, from the same `smallAt n num`. -/
def cosSin2PiTable (n : Nat) : Array (Float × Float) :=
  let g := Nat.gcd 8 n
  let memo : Array (Float × Float) := (Array.range (n / g + 1)).map fun i => smallAt n (g * i)
  (Array.range n).map fun m => cosSin2PiWith (fun num => memo.getD (num / g) (1.0, 0.0)) m n

end LeanFFTW.Trig
