/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.Trig

/-!
# Twiddle tables of the fast (Stockham) engine

A fast plan of size `N = R₀ ⋯ R_{s-1}` runs `s` passes; pass `t` has
`ns = R₀ ⋯ R_{t-1}` and multiplies input `r` of butterfly `k` (`k < ns`) by
`ω_{ns·R}^{r·k} = ω_N^{r·k·N/(ns·R)}`, `ω_n = exp (∓2πi/n)`.

All twiddles of a plan are read from the single table `m ↦ cosSin2Pi m N`
(`Trig.cosSin2PiTable`), so the assembly engine and the Lean reference use identical values.
Pass `t ≥ 1` stores, for `1 ≤ r < R`, the `ns` real parts of its twiddles followed by
the `ns` imaginary parts; pass 0 needs none (`k = 0`).
-/

namespace LeanFFTW

/-- `ns` of pass `t`: the product of the radices before it. -/
def passNs (rs : Array Nat) (t : Nat) : Nat := (rs.extract 0 t).foldl (· * ·) 1

/-- Twiddle table of a pass `(R, ns)` of a plan of size `N`, from the table `tab` of
`cosSin2Pi m N`. The imaginary part is negated (never producing `-0.0`) for forward
transforms, exactly as in `floatTw`. -/
def passTwiddles (tab : Array (Float × Float)) (fwd : Bool) (N R ns : Nat) : FloatArray :=
  Id.run do
    let step := N / (ns * R)
    let mut t := FloatArray.emptyWithCapacity (2 * (R - 1) * ns)
    for r in [1:R] do
      for k in [0:ns] do
        t := t.push (tab.getD (r * k * step) (1.0, 0.0)).1
      for k in [0:ns] do
        let s := (tab.getD (r * k * step) (1.0, 0.0)).2
        t := t.push (if fwd then Trig.negZ s else s)
    return t

/-- All twiddle tables of a plan, passes `1, …, s-1`, concatenated. -/
def planTwiddles (fwd : Bool) (N : Nat) (rs : Array Nat) : FloatArray := Id.run do
  let tab := Trig.cosSin2PiTable N
  let mut out := FloatArray.emptyWithCapacity (2 * N)
  for t in [1:rs.size] do
    let tw := passTwiddles tab fwd N (rs.getD t 1) (passNs rs t)
    for i in [0:tw.size] do
      out := out.push tw[i]!
  return out

end LeanFFTW
