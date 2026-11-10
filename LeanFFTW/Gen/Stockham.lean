/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Emit
import LeanFFTW.Gen.SymDFT
import LeanFFTW.Core.FloatOps
import LeanFFTW.Core.FastPlan

/-!
# The Stockham schedule: butterflies and the reference transform

A transform of size `N = R₀ ⋯ R_{s-1}` runs `s` radix-`R` passes (Stockham autosort,
decimation in time). Pass `t` has `ns = R₀ ⋯ R_{t-1}` and, for every `j < N/R` with
`k = j mod ns`, `b = j / ns`,

```
v[r]  = in[j + r·N/R] · ω_{ns·R}^{r·k}        (r < R)
out[b·ns·R + k + r·ns] = (DFT_R v)[r]
```

The butterfly `DFT_R ∘ diag(ω)` is produced by running the proved generic `exec`/`mkPlan`
(radices that are powers of two) or the proved `symDFT` (other radices) on symbolic inputs
(`symOps`), so its straight-line code is a CSE'd image of a verified algorithm.

`refTransform` evaluates the passes in Lean `Float`. It is the reference every schedule of
the assembly engine (`LeanFFTW/Asm`) is tested against bit for bit, and the object of the
correctness and error theorems.
-/

namespace LeanFFTW.Gen

open LeanFFTW

/-! ## Butterflies -/

/-- Input `r` of a butterfly: variables `2r, 2r+1`, times the twiddle (variables
`2R + 2(r-1)`, `+1`) when `twiddled` and `r ≥ 1`. -/
def bflyIn (R : Nat) (twiddled : Bool) (r : Nat) : SC :=
  let xr : SC := .val (.input (2 * r)) (.input (2 * r + 1))
  if twiddled && r ≥ 1 then
    SC.mulGen (.val (.input (2 * R + 2 * (r - 1))) (.input (2 * R + 2 * (r - 1) + 1))) xr
  else xr

/-- The symbolic DFT of the butterfly inputs: the generic `exec`/`mkPlan` for powers of two;
otherwise the prime factor algorithm `pfaDFT` across the prime-power blocks of `R` (no
twiddles between coprime factors), with `symDFT` (paired odd-length leaves, factored
mixed-radix combination) inside each block. -/
def bflySym (fwd : Bool) (R : Nat) (twiddled : Bool) : Array SC :=
  if R &&& (R - 1) == 0 then exec symOps (mkPlan symOps fwd (primeFactors R)) (bflyIn R twiddled)
  else if PfaOK (ppBlocks R) R then pfaDFT fwd (ppBlocks R) (bflyIn R twiddled)
  else symDFT fwd (primeFactors R) (bflyIn R twiddled)

/-- The symbolic butterfly of a pass: inputs `x_r` (`r < R`, variables `2r, 2r+1`) and, when
`twiddled`, twiddles `w_r` (`1 ≤ r < R`, variables `2R + 2(r-1)`, `+1`). Returns the `2R`
output expressions `re y_0, im y_0, …`. -/
def butterfly (fwd : Bool) (R : Nat) (twiddled : Bool) : Array SExpr :=
  let y := bflySym fwd R twiddled
  (Array.range (2 * R)).map fun i =>
    (if i % 2 = 0 then (symOps.get y (i / 2)).parts.1 else (symOps.get y (i / 2)).parts.2).contract

/-- Number of inputs of a butterfly. -/
def butterflyInputs (R : Nat) (twiddled : Bool) : Nat := if twiddled then 4 * R - 2 else 2 * R

/-- The CSE'd kernel of a butterfly. -/
def butterflyK (fwd : Bool) (R : Nat) (twiddled : Bool) : Kernel :=
  cse (butterflyInputs R twiddled) (butterfly fwd R twiddled)

/-! ## Reference semantics (what the engine must reproduce bit for bit)

The passes are defined over any `Arith`, on interleaved data (`2N` scalars, real and
imaginary parts alternating). Over `floatArith` with the binary64 twiddle tables this is
the reference the engine is tested against; over exact real arithmetic with exact
twiddles it is the object of the correctness theorem (`LeanFFTW/Proof/Stockham.lean`). -/

/-- The inputs of butterfly `j` of a pass: the `R` complex inputs `z[j + r·N/R]`, then (if
`tw` is given) the twiddles `w_r`, `1 ≤ r < R`, of `k = j mod ns`. -/
def bflyInputs {α : Type} [Inhabited α] (R ns N : Nat) (tw : Option (Array α)) (z : Array α)
    (j : Nat) : Array α :=
  let NR := N / R
  let kk := j % ns
  let xs := (List.range R).foldl (fun acc r =>
    (acc.push (z.getD (2 * (j + r * NR)) default)).push (z.getD (2 * (j + r * NR) + 1) default)) #[]
  match tw with
  | none => xs
  | some t => (List.range (R - 1)).foldl (fun acc r =>
      (acc.push (t.getD (2 * r * ns + kk) default)).push (t.getD ((2 * r + 1) * ns + kk) default)) xs

/-- One Stockham pass: output `c = b·ns·R + k + r·ns` (`k < ns`, `r < R`) is output `r` of
butterfly `j = b·ns + k`. -/
def passWith {α : Type} [Inhabited α] (A : Arith α) (k : Kernel) (R ns N : Nat)
    (tw : Option (Array α)) (z : Array α) : Array α :=
  let bfs : Array (Array α) := (Array.range (N / R)).map fun j => k.eval A (bflyInputs R ns N tw z j)
  (Array.range (2 * N)).map fun i =>
    let c := i / 2
    let kk := c % ns
    let r := (c / ns) % R
    let b := c / (ns * R)
    (bfs.getD (b * ns + kk) #[]).getD (2 * r + i % 2) default

/-- All passes of the plan `rs`; `twOf t` is the twiddle table of pass `t ≥ 1`. -/
def stockhamWith {α : Type} [Inhabited α] (A : Arith α) (fwd : Bool) (N : Nat) (rs : Array Nat)
    (twOf : Nat → Array α) (z : Array α) : Array α := Id.run do
  let mut z := z
  for t in [0:rs.size] do
    let R := rs.getD t 1
    let ns := passNs rs t
    z := passWith A (butterflyK fwd R (t ≥ 1)) R ns N (if t ≥ 1 then some (twOf t) else none) z
  return z

/-- The binary64 reference transform of a fast plan on interleaved data. A single radix
(`s = 1`, the small codelets) is one untwiddled pass with `ns = 1`. -/
def refTransform (fwd : Bool) (N : Nat) (rs : Array Nat) (inp : FloatArray) : FloatArray :=
  let tab := Trig.cosSin2PiTable N
  let twOf (t : Nat) : Array Float := (passTwiddles tab fwd N (rs.getD t 1) (passNs rs t)).data
  ⟨stockhamWith floatArith fwd N rs twOf inp.data⟩

def joinLines (ls : List String) : String := String.join (ls.map (· ++ "\n"))

end LeanFFTW.Gen
