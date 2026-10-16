/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import Mathlib.Analysis.Fourier.ZMod

/-!
# The specification: FFTW's discrete Fourier transform

FFTW computes the unnormalized DFT `Y k = Σ_{j<n} x j · exp(∓2πi jk/n)` with sign `−` for
`FFTW_FORWARD` and `+` for `FFTW_BACKWARD`.

The **independent specification** is Mathlib's `ZMod.dft` (`𝓕`, defined in
`Mathlib/Analysis/Fourier/ZMod.lean`), the Fourier transform on `ℤ/nℤ` with respect to the
standard additive character. This file defines the convenient sum form `dftSum` used by the
proofs and proves that it *is* Mathlib's `𝓕` (forward) and `n • 𝓕⁻` (backward), so every
correctness theorem stated with `dftSum` is a theorem about Mathlib's transform.
-/

open Complex Finset

namespace LeanFFTW

/-- The twiddle factor `exp (∓2πi k / n)`; `-` when `fwd` (FFTW_FORWARD). -/
noncomputable def twiddle (fwd : Bool) (n k : ℕ) : ℂ :=
  Complex.exp ((if fwd then -1 else 1) * (2 * Real.pi * I * k / n))

/-- The DFT as a finite sum: `Y k = Σ_{j<n} ω^{jk} x j`. -/
noncomputable def dftSum (fwd : Bool) (n : ℕ) (x : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range n, twiddle fwd n (j * k) * x j

section ZModBridge

open ZMod

variable {n : ℕ} [NeZero n]

lemma stdAddChar_natCast_neg (a : ℕ) :
    stdAddChar (-(a : ZMod n)) = twiddle true n a := by
  have h := stdAddChar_coe (N := n) (-(a : ℤ))
  push_cast at h
  rw [h, twiddle]
  congr 1
  simp only [ite_true]
  ring

lemma stdAddChar_natCast (a : ℕ) :
    stdAddChar ((a : ZMod n)) = twiddle false n a := by
  have h := stdAddChar_coe (N := n) ((a : ℤ))
  push_cast at h
  rw [h, twiddle]
  congr 1
  push_cast
  ring

/-- Reindex a sum over `ZMod n` as a sum over `range n` via `ZMod.val`. -/
lemma sum_zmod_eq_sum_range (f : ℕ → ℂ) :
    ∑ j : ZMod n, f j.val = ∑ j ∈ range n, f j := by
  rw [Finset.sum_range]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rfl

/-- **The forward `dftSum` is Mathlib's `ZMod.dft`.** -/
theorem dftSum_true_eq_dft (x : ℕ → ℂ) (k : ℕ) (_hk : k < n) :
    dftSum true n x k = 𝓕 (fun j : ZMod n => x j.val) (k : ZMod n) := by
  rw [dft_apply, dftSum]
  rw [← sum_zmod_eq_sum_range (fun j => twiddle true n (j * k) * x j)]
  refine Fintype.sum_congr _ _ (fun j => ?_)
  rw [smul_eq_mul, ← stdAddChar_natCast_neg]
  congr 2
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- **The backward `dftSum` is `n` times Mathlib's inverse DFT.** -/
theorem dftSum_false_eq_invDft (x : ℕ → ℂ) (k : ℕ) (_hk : k < n) :
    dftSum false n x k = (n : ℂ) * 𝓕⁻ (fun j : ZMod n => x j.val) (k : ZMod n) := by
  rw [invDFT_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast NeZero.ne n),
    one_mul, dftSum]
  rw [← sum_zmod_eq_sum_range (fun j => twiddle false n (j * k) * x j)]
  refine Fintype.sum_congr _ _ (fun j => ?_)
  rw [smul_eq_mul, ← stdAddChar_natCast]
  congr 2
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

end ZModBridge

end LeanFFTW
