/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Spec.DFT
import LeanFFTW.Core.Alg

/-!
# Exact-arithmetic correctness of the generic algorithms

We instantiate the scalar-generic algorithms of `LeanFFTW/Core/Alg.lean` with exact
complex numbers and prove that the executed plan computes `dftSum`, hence Mathlib's
`ZMod.dft` (see `LeanFFTW/Spec/DFT.lean`).

Main results:
* `LeanFFTW.dftSum_ct`: the Cooley–Tukey decomposition `n = r * m`;
* `LeanFFTW.exec_mkPlan_exact`: executing the plan built by `mkPlan` for any factorization
  with positive factors computes the DFT of the product size;
* `LeanFFTW.exec_mkPlan_exact_eq_dft`: the same, stated with Mathlib's `𝓕`.
-/

open Complex Finset

namespace LeanFFTW

/-- Exact complex instantiation of the generic operations. -/
noncomputable def exactOps : Ops ℂ (ℕ → ℂ) where
  zero := 0
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  tw := twiddle
  build _ f := f
  get v := v

/-! ### Twiddle algebra -/

lemma twiddle_add (fwd : Bool) (n a b : ℕ) :
    twiddle fwd n (a + b) = twiddle fwd n a * twiddle fwd n b := by
  simp only [twiddle, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma twiddle_mul_self (fwd : Bool) {n : ℕ} (hn : 0 < n) (q : ℕ) :
    twiddle fwd n (n * q) = 1 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [twiddle]
  have : (if fwd then (-1 : ℂ) else 1) * (2 * Real.pi * I * ((n * q : ℕ) : ℂ) / n)
      = ((if fwd then -(q : ℤ) else (q : ℤ)) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    field_simp
    split_ifs <;> push_cast <;> ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma twiddle_mod (fwd : Bool) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    twiddle fwd n (k % n) = twiddle fwd n k := by
  conv_rhs => rw [← Nat.mod_add_div k n, twiddle_add, twiddle_mul_self fwd hn, mul_one]

lemma twiddle_scale (fwd : Bool) {r m : ℕ} (hr : 0 < r) (a : ℕ) :
    twiddle fwd (r * m) (r * a) = twiddle fwd m a := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [twiddle]
  congr 1
  push_cast
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

/-! ### Sums -/

lemma sumRange_exact (n : ℕ) (f : ℕ → ℂ) :
    sumRange exactOps n f = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [sumRange, exactOps]
  | succ n ih =>
    simp only [sumRange, Nat.fold_succ] at ih ⊢
    rw [ih, Finset.sum_range_succ]
    rfl

/-- Split a sum over `range (r * m)` into a double sum over `j1 + r * j2`. -/
lemma sum_range_mul_split (r m : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ range (r * m), f j = ∑ j1 ∈ range r, ∑ j2 ∈ range m, f (j1 + r * j2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j1 _ => ?_)
    rw [Finset.sum_range_succ]
    congr 1
    · exact rfl
    · congr 1; ring

/-- **Cooley–Tukey (decimation in time).** For `n = r * m` and `k < n`,
`DFT_n(x)_k = Σ_{j1<r} ω_n^{j1 k} · DFT_m(x_{j1 + r ·})_{k mod m}`. -/
theorem dftSum_ct (fwd : Bool) {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (x : ℕ → ℂ) (k : ℕ) :
    dftSum fwd (r * m) x k =
      ∑ j1 ∈ range r, twiddle fwd (r * m) (j1 * k) *
        dftSum fwd m (fun j2 => x (j1 + r * j2)) (k % m) := by
  rw [dftSum, sum_range_mul_split]
  refine Finset.sum_congr rfl (fun j1 _ => ?_)
  rw [dftSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j2 _ => ?_)
  rw [← mul_assoc]
  congr 1
  rw [twiddle_mod fwd hm, add_mul, twiddle_add, mul_assoc, twiddle_scale fwd hr]

/-! ### Plans -/

lemma mkPlan_size (fwd : Bool) : ∀ fs : List ℕ, (mkPlan exactOps fwd fs).size = fs.prod
  | [] => rfl
  | [p] => by simp [mkPlan, Plan.size]
  | r :: s :: rest => by
    simp only [mkPlan, Plan.size]
    rw [mkPlan_size fwd (s :: rest)]
    simp

/-- **Correctness of the executed plan in exact arithmetic.** For any factorization `fs`
with positive factors, executing `mkPlan fs` computes the DFT of size `fs.prod`. -/
theorem exec_mkPlan_exact (fwd : Bool) :
    ∀ (fs : List ℕ), (∀ f ∈ fs, 0 < f) → ∀ (x : ℕ → ℂ) (k : ℕ), k < fs.prod →
      exec exactOps (mkPlan exactOps fwd fs) x k = dftSum fwd fs.prod x k
  | [], _, x, k, hk => by
    simp only [List.prod_nil, Nat.lt_one_iff] at hk
    subst hk
    simp [mkPlan, exec, exactOps, sumRange_exact, dftSum, twiddle]
  | [p], hpos, x, k, hk => by
    have hp : 0 < p := hpos p (by simp)
    simp only [mkPlan, exec, List.prod_cons, List.prod_nil, mul_one]
    change sumRange exactOps p _ = _
    rw [sumRange_exact, dftSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change twiddle fwd p (j * k % p) * x j = _
    rw [twiddle_mod fwd hp]
  | r :: s :: rest, hpos, x, k, hk => by
    have hr : 0 < r := hpos r (by simp)
    have hrest : ∀ f ∈ s :: rest, 0 < f := fun f hf => hpos f (List.mem_cons_of_mem _ hf)
    have hm : 0 < (s :: rest).prod := List.prod_pos hrest
    set m := (s :: rest).prod with hmdef
    have hsize : (mkPlan exactOps fwd (s :: rest)).size = m := mkPlan_size fwd _
    simp only [mkPlan, exec, List.prod_cons]
    rw [List.prod_cons] at hk
    change sumRange exactOps r _ = _
    rw [sumRange_exact, hsize, ← hmdef]
    rw [show r * (s * rest.prod) = r * m by rw [hmdef, List.prod_cons], dftSum_ct fwd hr hm]
    refine Finset.sum_congr rfl (fun j1 hj1 => ?_)
    change twiddle fwd (r * m) (j1 * k % (r * m)) * _ = _
    rw [twiddle_mod fwd (Nat.mul_pos hr hm)]
    congr 1
    have hj1' : j1 < r := Finset.mem_range.mp hj1
    have hget : (((Array.range r).map fun j1 =>
        exec exactOps (mkPlan exactOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2))).getD j1
          default) = exec exactOps (mkPlan exactOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2)) := by
      simp [Array.getD, hj1']
    change (((Array.range r).map fun j1 =>
        exec exactOps (mkPlan exactOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2))).getD j1
          default) (k % m) = _
    rw [hget]
    exact exec_mkPlan_exact fwd (s :: rest) hrest _ _ (Nat.mod_lt _ hm)

/-- The generic engine's 1-D plans compute Mathlib's DFT (forward case). -/
theorem exec_mkPlan_exact_eq_dft (fs : List ℕ) (hpos : ∀ f ∈ fs, 0 < f)
    (x : ℕ → ℂ) (k : ℕ) (hk : k < fs.prod) :
    haveI : NeZero fs.prod := ⟨(List.prod_pos hpos).ne'⟩
    exec exactOps (mkPlan exactOps true fs) x k =
      ZMod.dft (fun j : ZMod fs.prod => x j.val) (k : ZMod fs.prod) := by
  haveI : NeZero fs.prod := ⟨(List.prod_pos hpos).ne'⟩
  rw [exec_mkPlan_exact true fs hpos x k hk, dftSum_true_eq_dft x k hk]

end LeanFFTW
