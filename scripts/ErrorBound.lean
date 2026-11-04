import LeanFFTW.Gen.Stockham
import Std.Data.HashSet

/-! Evaluates the right-hand side of `refTransform_error_depth` for concrete plans, and dumps
the generated constants so that κ can be measured.

    lake env lean --run scripts/ErrorBound.lean bound N R₀ R₁ …   -- per plan
    lake env lean --run scripts/ErrorBound.lean consts MAXN         -- every kernel constant, R ≤ MAXN

`bound` prints one JSON line: the largest rounding depth `a` and constant depth `b` over all
outputs (`depthArith`, an exact `Nat` computation, identical to the definition in
`Proof/RoundError.lean`), and `magMax`, the largest entry of `magArith ℓ` run on an input of
all ones (a magnitude bound for every input with `|re|, |im| ≤ 1`), evaluated in binary64
with |constants| rounded up by one part in 2⁵⁰, a margin far above its own rounding error.
For any input with all parts in [-1, 1], `refTransform_error_depth` then bounds every output's
absolute error by `((1+2⁻⁵³)^a (1+t)^b − 1) · magMax`, `t = max τ κ`.

`consts` prints the bit pattern `Cst.toFloat` of every constant that occurs in a kernel
`butterflyK fwd R tw` with `R ≤ MAXN` (prime factors ≤ 13), so κ can be measured against a high-precision reference outside Lean. -/

open LeanFFTW LeanFFTW.Gen

/-- Copy of `depthArith` (`LeanFFTW/Proof/RoundError.lean`, which needs Mathlib). -/
def depthA : Arith (Nat × Nat) where
  cst _ := (0, 1)
  zero := (0, 0)
  add a b := (max a.1 b.1 + 1, max a.2 b.2)
  sub a b := (max a.1 b.1 + 1, max a.2 b.2)
  mul a b := (a.1 + b.1 + 1, a.2 + b.2)
  neg a := a
  fma a b c := (max (a.1 + b.1) c.1 + 1, max (a.2 + b.2) c.2)
  fms a b c := (max (a.1 + b.1) c.1 + 1, max (a.2 + b.2) c.2)
  fnma a b c := (max c.1 (a.1 + b.1) + 1, max c.2 (a.2 + b.2))

/-- `magArith ℓ` evaluated in binary64 (constants' magnitudes rounded up). -/
def magF (ℓ : Float) : Arith Float where
  cst c := c.toFloat.abs * (1 + 2.0 ^ (-50.0)) + ℓ
  zero := 0
  add a b := a + b + ℓ
  sub a b := a + b + ℓ
  mul a b := a * b + ℓ
  neg a := a
  fma a b c := a * b + c + ℓ
  fms a b c := a * b + c + ℓ
  fnma a b c := c + a * b + ℓ

def twSize (rs : Array Nat) (t : Nat) : Nat := 2 * (rs.getD t 1 - 1) * passNs rs t

def bound (N : Nat) (rs : Array Nat) : String := Id.run do
  let d := stockhamWith depthA true N rs (fun t => Array.replicate (twSize rs t) (0, 1))
    (Array.replicate (2 * N) (0, 1))
  let ℓ : Float := 2.0 ^ (-1022.0)
  let m := stockhamWith (magF ℓ) true N rs (fun t => Array.replicate (twSize rs t) 1)
    (Array.replicate (2 * N) 1)
  let a := d.foldl (fun x p => max x p.1) 0
  let b := d.foldl (fun x p => max x p.2) 0
  let mm := m.foldl max 0
  let rsS := ",".intercalate (rs.toList.map toString)
  return s!"\{\"N\":{N},\"R\":[{rsS}],\"a\":{a},\"b\":{b},\"magMax\":{mm}}"

def main (args : List String) : IO Unit := do
  match args with
  | "bound" :: n :: rs => IO.println (bound n.toNat! (rs.map String.toNat!).toArray)
  | ["consts", mx] =>
    -- every constant of every kernel `butterflyK fwd R tw`, R ≤ MAXN with prime factors ≤ 13
    let smooth (n : Nat) : Bool := Id.run do
      let mut m := n
      for p in [2, 3, 5, 7, 11, 13] do
        while m % p == 0 && m > 1 do m := m / p
      return m == 1
    let mut seen : Std.HashSet Cst := {}
    for R in [2:mx.toNat! + 1] do
      if smooth R then
        for fwd in [true, false] do
          for tw in [true, false] do
            for op in (butterflyK fwd R tw).ops do
              if let .cst c := op then
                unless seen.contains c do
                  seen := seen.insert c
                  let (nm, k, n) := match c with
                    | .cos k n => ("cos", k, n) | .sin k n => ("sin", k, n)
                    | .sqrthalf => ("cos", 1, 8) | .tan k n => ("tan", k, n)
                  IO.println s!"{nm} {k} {n} {c.toFloat.toBits}"
  | _ => IO.eprintln "usage: bound N R... | consts MAXN"
