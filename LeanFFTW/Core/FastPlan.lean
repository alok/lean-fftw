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
(`Trig.cosSin2PiTable`), so the C engine and the Lean reference use identical values.
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

/-- Decode `[N, fwd, s, R₀, …, R_{s-1}]` (small integers, exact in binary64). -/
def decodeFastSpec (spec : FloatArray) : Nat × Bool × Array Nat :=
  let nat (i : Nat) : Nat := (spec.get! i).toUInt64.toNat
  let s := nat 2
  (nat 0, nat 1 == 1, (Array.range s).map fun i => nat (3 + i))

/-- C entry point: the twiddle tables of a fast plan. -/
@[export lfftw_fast_twiddles]
def fastTwiddlesFFI (spec : FloatArray) : FloatArray :=
  let (N, fwd, rs) := decodeFastSpec spec
  planTwiddles fwd N rs

/-- C entry point: the base table `ω_N^m`, `m < N`, interleaved `(re, im)`, for
`spec = [N, fwd]`; pass tables are gathered from it (entry `(r, k)` of pass `(R, ns)` is
entry `r·k·N/(ns·R)`), exactly as `passTwiddles` does. -/
@[export lfftw_fast_base_table]
def fastBaseTableFFI (spec : FloatArray) : FloatArray := Id.run do
  let N := (spec.get! 0).toUInt64.toNat
  let fwd := (spec.get! 1).toUInt64.toNat == 1
  let tab := Trig.cosSin2PiTable N
  let mut out := FloatArray.emptyWithCapacity (2 * N)
  for (c, s) in tab do
    out := (out.push c).push (if fwd then Trig.negZ s else s)
  return out

end LeanFFTW
