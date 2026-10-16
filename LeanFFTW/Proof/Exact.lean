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
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (if fwd then (-1 : ℂ) else 1) * (2 * Real.pi * I * ((n * q : ℕ) : ℂ) / n)
      = (z : ℂ) * (2 * Real.pi * I) := by
    refine ⟨if fwd then -(q : ℤ) else q, ?_⟩
    cases fwd
    · simp only [Bool.false_eq_true, ite_false]
      push_cast
      field_simp
    · simp only [ite_true]
      push_cast
      field_simp
  rw [twiddle, hz, Complex.exp_int_mul_two_pi_mul_I]

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
    rw [Finset.sum_range_succ, Nat.add_comm (r * m) j1]

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
  have h1 : twiddle fwd m (j2 * (k % m)) = twiddle fwd m (j2 * k) := by
    have : j2 * (k % m) % m = j2 * k % m := by simp [Nat.mul_mod]
    rw [← twiddle_mod fwd hm, this, twiddle_mod fwd hm]
  rw [h1, ← twiddle_scale fwd hr (j2 * k), ← twiddle_add]
  congr 1
  ring

/-! ### Plans -/

lemma mkPlan_size (fwd : Bool) : ∀ fs : List ℕ, (mkPlan exactOps fwd fs).size = fs.prod
  | [] => by simp [mkPlan, Plan.size]
  | [p] => by simp [mkPlan, Plan.size]
  | r :: s :: rest => by
    simp only [mkPlan, Plan.size]
    rw [mkPlan_size fwd (s :: rest)]
    simp

/-- One step of `exec` on a direct node, in exact arithmetic. -/
lemma exec_direct_exact (n : ℕ) (w : ℕ → ℂ) (x : ℕ → ℂ) (k : ℕ) :
    exec exactOps (.direct n w) x k = ∑ j ∈ range n, w (j * k % n) * x j := by
  simp only [exec]
  change sumRange exactOps n _ = _
  rw [sumRange_exact]
  rfl

/-- One step of `exec` on a Cooley–Tukey node, in exact arithmetic. -/
lemma exec_ct_exact (r : ℕ) (w : ℕ → ℂ) (sub : Plan (ℕ → ℂ)) (x : ℕ → ℂ) (k : ℕ) :
    exec exactOps (.ct r w sub) x k =
      ∑ j1 ∈ range r, w (j1 * k % (r * sub.size)) *
        exec exactOps sub (fun j2 => x (j1 + r * j2)) (k % sub.size) := by
  simp only [exec]
  change sumRange exactOps r _ = _
  rw [sumRange_exact]
  refine Finset.sum_congr rfl (fun j1 hj1 => ?_)
  have hj1' : j1 < r := Finset.mem_range.mp hj1
  change w _ * (((Array.range r).map fun j1 =>
      exec exactOps sub (fun j2 => x (j1 + r * j2))).getD j1 default) _ = _
  simp [Array.getD, hj1']

/-- **Correctness of the executed plan in exact arithmetic.** For any factorization `fs`
with positive factors, executing `mkPlan fs` computes the DFT of size `fs.prod`. -/
theorem exec_mkPlan_exact (fwd : Bool) :
    ∀ (fs : List ℕ), (∀ f ∈ fs, 0 < f) → ∀ (x : ℕ → ℂ) (k : ℕ), k < fs.prod →
      exec exactOps (mkPlan exactOps fwd fs) x k = dftSum fwd fs.prod x k
  | [], _, x, k, hk => by
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [mkPlan]
    rw [exec_direct_exact]
    simp [dftSum, exactOps]
  | [p], hpos, x, k, hk => by
    have hp : 0 < p := hpos p (by simp)
    simp only [mkPlan]
    rw [exec_direct_exact]
    simp only [List.prod_cons, List.prod_nil, mul_one, dftSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change twiddle fwd p (j * k % p) * x j = _
    rw [twiddle_mod fwd hp]
  | r :: s :: rest, hpos, x, k, hk => by
    have hr : 0 < r := hpos r (by simp)
    have hrest : ∀ f ∈ s :: rest, 0 < f := fun f hf => hpos f (List.mem_cons_of_mem _ hf)
    have hm : 0 < (s :: rest).prod := List.prod_pos hrest
    have hsize : (mkPlan exactOps fwd (s :: rest)).size = (s :: rest).prod := mkPlan_size fwd _
    have hprod : (r :: s :: rest).prod = r * (s :: rest).prod := List.prod_cons
    have hplan : mkPlan exactOps fwd (r :: s :: rest) =
        .ct r (exactOps.build (r * (s :: rest).prod) (exactOps.tw fwd (r * (s :: rest).prod)))
          (mkPlan exactOps fwd (s :: rest)) := by
      simp only [mkPlan]
    rw [hplan, exec_ct_exact, hsize, hprod, dftSum_ct fwd hr hm]
    refine Finset.sum_congr rfl (fun j1 _ => ?_)
    change twiddle fwd _ (j1 * k % _) * _ = _
    rw [twiddle_mod fwd (Nat.mul_pos hr hm)]
    congr 1
    exact exec_mkPlan_exact fwd (s :: rest) hrest _ _ (Nat.mod_lt _ hm)

/-- The generic engine's 1-D plans compute Mathlib's DFT (forward case). -/
theorem exec_mkPlan_exact_eq_dft (fs : List ℕ) (hpos : ∀ f ∈ fs, 0 < f)
    (x : ℕ → ℂ) (k : ℕ) (hk : k < fs.prod) :
    haveI : NeZero fs.prod := ⟨(List.prod_pos hpos).ne'⟩
    exec exactOps (mkPlan exactOps true fs) x k =
      ZMod.dft (fun j : ZMod fs.prod => x j.val) (k : ZMod fs.prod) := by
  have : NeZero fs.prod := ⟨(List.prod_pos hpos).ne'⟩
  rw [exec_mkPlan_exact true fs hpos x k hk, dftSum_true_eq_dft x k hk]

end LeanFFTW
