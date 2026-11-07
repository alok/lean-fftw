/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Stockham

/-!
# The in-place schedule, as a Lean program

The fast engine's in-place schedule (`LF_INPLACE`, the one the planner picks for most
power-of-two sizes from 1024 up) runs the same butterflies as the Stockham schedule but
keeps the data in one array:

* the first ("leaf") pass reads the input in natural order and writes leaf `d`'s outputs at
  positions `β(d)·R₀ + r`, where `β` reverses the mixed-radix digits of `d`;
* pass `t ≥ 1` (`ns = R₀⋯R_{t-1}`) works on blocks of size `ns·R`: butterfly `(B, q)` reads
  positions `B·ns·R + q + r·ns` (`r < R`) with the twiddles of column `q` and writes its
  outputs back to the same positions.

This file defines that schedule over any `Arith`, with each pass in gather form (every
output position names the butterfly output it holds). `LeanFFTW/Proof/InPlace.lean` proves
`inplaceWith A = stockhamWith A` for every arithmetic `A`: the two schedules perform the
same operations on the same values, so over binary64 they agree bit for bit, and over the
reals the in-place schedule computes the DFT (`stockhamWith_exact`).
-/

namespace LeanFFTW.Gen

/-- Product of a list of radices. -/
def radixProd (L : List Nat) : Nat := L.foldl (· * ·) 1

/-- Mixed-radix digit reversal for the radices `L` (first radix least significant on the
output side): `β (R :: L) i = β L (i mod m)·R + i / m`, `m = ∏ L`. -/
def digitRev : List Nat → Nat → Nat
  | [], _ => 0
  | R :: L, i => digitRev L (i % radixProd L) * R + i / radixProd L

/-- The inverse of `digitRev`: `γ (R :: L) P = γ L (P / R) + (P mod R)·∏ L`. -/
def digitRevInv : List Nat → Nat → Nat
  | [], _ => 0
  | R :: L, P => digitRevInv L (P / R) + (P % R) * radixProd L

/-- The inputs of in-place butterfly `(B, q)` of a pass: data at `c + r·ns` (`c = B·ns·R + q`,
`r < R`), then (if `tw` is given) the twiddles `w_r`, `1 ≤ r < R`, of column `q`. -/
def ipInputs {α : Type} [Inhabited α] (R ns : Nat) (tw : Option (Array α)) (y : Array α)
    (c q : Nat) : Array α :=
  let xs := (List.range R).foldl (fun acc r =>
    (acc.push (y.getD (2 * (c + r * ns)) default)).push (y.getD (2 * (c + r * ns) + 1) default)) #[]
  match tw with
  | none => xs
  | some t => (List.range (R - 1)).foldl (fun acc r =>
      (acc.push (t.getD (2 * r * ns + q) default)).push (t.getD ((2 * r + 1) * ns + q) default)) xs

/-- One in-place pass (`t ≥ 1`): position `B·ns·R + q + r·ns` holds output `r` of butterfly
`(B, q)`, whose inputs are the same positions. -/
def ipPass {α : Type} [Inhabited α] (A : Arith α) (k : Kernel) (R ns N : Nat)
    (tw : Option (Array α)) (y : Array α) : Array α :=
  let bfs : Array (Array α) := (Array.range (N / R)).map fun j =>
    k.eval A (ipInputs R ns tw y (j / ns * ns * R + j % ns) (j % ns))
  (Array.range (2 * N)).map fun i =>
    let c := i / 2
    let kk := c % ns
    let r := (c / ns) % R
    let b := c / (ns * R)
    (bfs.getD (b * ns + kk) #[]).getD (2 * r + i % 2) default

/-- The leaf pass: position `P·R + r` holds output `r` of the length-`R` DFT of the inputs
`x[γ(P) + i·N/R]`, where `γ = digitRevInv L` and `L` are the remaining radices. -/
def ipLeaf {α : Type} [Inhabited α] (A : Arith α) (k : Kernel) (R N : Nat) (L : List Nat)
    (x : Array α) : Array α :=
  let bfs : Array (Array α) := (Array.range (N / R)).map fun P =>
    k.eval A (bflyInputs R 1 N none x (digitRevInv L P))
  (Array.range (2 * N)).map fun i =>
    let c := i / 2
    (bfs.getD (c / R) #[]).getD (2 * (c % R) + i % 2) default

/-- The in-place schedule of the plan `rs` (at least one radix). -/
def inplaceWith {α : Type} [Inhabited α] (A : Arith α) (fwd : Bool) (N : Nat) (rs : Array Nat)
    (twOf : Nat → Array α) (x : Array α) : Array α :=
  let y := ipLeaf A (butterflyK fwd (rs.getD 0 1) false) (rs.getD 0 1) N (rs.toList.drop 1) x
  (List.range (rs.size - 1)).foldl (fun y u =>
    ipPass A (butterflyK fwd (rs.getD (u + 1) 1) true) (rs.getD (u + 1) 1) (passNs rs (u + 1)) N
      (some (twOf (u + 1))) y) y

/-- Leaf offsets of the in-place schedule: leaf `d` (`d < N/R₀`) writes its outputs at
positions `digitRev (R₁ … R_{s-1}) d · R₀ + r`. The C executor reads this table. -/
def leafOffsets (N : Nat) (rs : Array Nat) : Array Nat :=
  let R0 := rs.getD 0 1
  let L := rs.toList.drop 1
  (Array.range (N / R0)).map fun d => digitRev L d * R0

/-- C entry point: `spec = [N, s, R₀, …, R_{s-1}]`; the leaf offsets as doubles (exact). -/
@[export lfftw_leaf_offsets]
def leafOffsetsFFI (spec : FloatArray) : FloatArray :=
  let nat (i : Nat) : Nat := (spec.get! i).toUInt64.toNat
  let rs := (Array.range (nat 1)).map fun i => nat (2 + i)
  ⟨(leafOffsets (nat 0) rs).map (·.toFloat)⟩

end LeanFFTW.Gen
