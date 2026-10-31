/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Proof.Exact
import LeanFFTW.Proof.Kernel
import LeanFFTW.Gen.Stockham

/-!
# The generated butterflies compute DFTs (exact arithmetic)

Expressions are evaluated over the reals, with each constant `Cst.cos k n` denoting
`cos (2πk/n)` exactly (`realArith`). Symbolic complex values (`SC`) denote complex numbers
(`SC.toC`), and every `symOps` operation is shown to denote the corresponding complex
operation; running the generic `exec`/`mkPlan` on symbolic inputs therefore computes, under
evaluation, what `exec` computes on exact complex numbers, which is the DFT
(`exec_mkPlan_exact`). With `cse_correct` this gives `butterflyK_correct`: the kernels the
C code is printed from compute `DFT_R (w ⊙ x)`.
-/

open Complex Finset

namespace LeanFFTW.Gen

open LeanFFTW

/-- The exact value of a constant. -/
noncomputable def Cst.toReal : Cst → ℝ
  | .cos k n => Real.cos (2 * Real.pi * k / n)
  | .sin k n => Real.sin (2 * Real.pi * k / n)
  | .sqrthalf => Real.sqrt 2 / 2
  | .tan k n => Real.tan (2 * Real.pi * k / n)

/-- Exact real arithmetic. -/
noncomputable def realArith : Arith ℝ where
  cst := Cst.toReal
  zero := 0
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  neg a := -a
  fma a b c := a * b + c
  fms a b c := a * b - c
  fnma a b c := c - a * b

theorem realArith_comm : realArith.Comm where
  add a b := by simp only [realArith]; ring
  mul a b := by simp only [realArith]; ring
  fma a b c := by simp only [realArith]; ring
  fms a b c := by simp only [realArith]; ring
  fnma a b c := by simp only [realArith]; ring

section Eval

variable (env : ℕ → ℝ)

/-- Real value of an expression. -/
noncomputable abbrev ev (e : SExpr) : ℝ := e.evalWith realArith env

@[simp] theorem ev_input (i : ℕ) : ev env (.input i) = env i := rfl
@[simp] theorem ev_zero : ev env .zero = 0 := rfl
@[simp] theorem ev_cst (c : Cst) : ev env (.cst c) = c.toReal := rfl
@[simp] theorem ev_add (a b : SExpr) : ev env (.add a b) = ev env a + ev env b := rfl
@[simp] theorem ev_sub (a b : SExpr) : ev env (.sub a b) = ev env a - ev env b := rfl
@[simp] theorem ev_mul (a b : SExpr) : ev env (.mul a b) = ev env a * ev env b := rfl
@[simp] theorem ev_neg (a : SExpr) : ev env (.neg a) = -ev env a := rfl
@[simp] theorem ev_fma (a b c : SExpr) : ev env (.fma a b c) = ev env a * ev env b + ev env c := rfl
@[simp] theorem ev_fms (a b c : SExpr) : ev env (.fms a b c) = ev env a * ev env b - ev env c := rfl
@[simp] theorem ev_fnma (a b c : SExpr) : ev env (.fnma a b c) = ev env c - ev env a * ev env b := rfl

open SExpr in
theorem ev_mkNeg (a : SExpr) : ev env (mkNeg a) = -ev env a := by
  unfold mkNeg; split <;> simp

open SExpr in
theorem ev_mkAdd (a b : SExpr) : ev env (mkAdd a b) = ev env a + ev env b := by
  unfold mkAdd; split <;> simp <;> ring

open SExpr in
theorem ev_mkSub (a b : SExpr) : ev env (mkSub a b) = ev env a - ev env b := by
  unfold mkSub; split <;> simp [ev_mkNeg]; ring

open SExpr in
theorem ev_mkMulC (c : Cst) (a : SExpr) : ev env (mkMulC c a) = c.toReal * ev env a := by
  unfold mkMulC; split <;> simp [ev_mkNeg]

open SExpr in
theorem ev_mkFmaAdd (c1 : Cst) (a : SExpr) (c2 : Cst) (b : SExpr) :
    ev env (mkFmaAdd c1 a c2 b) = c1.toReal * ev env a + c2.toReal * ev env b := by
  unfold mkFmaAdd; split <;> simp [ev_mkMulC]

open SExpr in
theorem ev_mkFmaSub (c1 : Cst) (a : SExpr) (c2 : Cst) (b : SExpr) :
    ev env (mkFmaSub c1 a c2 b) = c1.toReal * ev env a - c2.toReal * ev env b := by
  unfold mkFmaSub; split <;> simp [ev_mkMulC, ev_mkNeg]

open SExpr in
theorem ev_mkFnmaC (t : Cst) (b a : SExpr) : ev env (mkFnmaC t b a) = ev env a - t.toReal * ev env b := by
  unfold mkFnmaC; split <;> simp

open SExpr in
theorem ev_mkFmaC (t : Cst) (a b : SExpr) : ev env (mkFmaC t a b) = t.toReal * ev env a + ev env b := by
  unfold mkFmaC; split <;> simp

open SExpr in
theorem ev_mkFmsC (t : Cst) (a b : SExpr) : ev env (mkFmsC t a b) = t.toReal * ev env a - ev env b := by
  unfold mkFmsC; split <;> simp [ev_mkNeg]

/-- The complex number denoted by a pair of expressions. -/
noncomputable def evC (p : SExpr × SExpr) : ℂ := ⟨ev env p.1, ev env p.2⟩

theorem evC_mul_mk (p : SExpr × SExpr) (c s : ℝ) :
    evC env p * ⟨c, s⟩ = ⟨ev env p.1 * c - ev env p.2 * s, ev env p.1 * s + ev env p.2 * c⟩ := by
  apply Complex.ext <;> simp [evC]

/-- The anticlockwise twiddle in coordinates. -/
theorem twiddle_false_eq (n k : ℕ) :
    twiddle false n k = ⟨Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)⟩ := by
  have h : twiddle false n k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * I) := by
    rw [twiddle]; congr 1; push_cast; simp; ring
  rw [h]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
  · rw [Complex.exp_ofReal_mul_I_im]

theorem twiddle_true_eq_inv (n k : ℕ) : twiddle true n k = (twiddle false n k)⁻¹ := by
  simp only [twiddle, ite_true, Bool.false_eq_true, ite_false, neg_one_mul, one_mul,
    Complex.exp_neg]

theorem I_eq_twiddle : I = twiddle false 4 1 := by
  rw [twiddle, ← Complex.exp_pi_div_two_mul_I]
  congr 1; push_cast; simp; ring

theorem twiddle_pow (fwd : Bool) (n k q : ℕ) : twiddle fwd n k ^ q = twiddle fwd n (k * q) := by
  induction q with
  | zero => simp [twiddle]
  | succ q ih => rw [pow_succ, ih, ← twiddle_add]; ring_nf

theorem I_pow_mod (q : ℕ) : I ^ q = I ^ (q % 4) := by
  conv_lhs => rw [← Nat.div_add_mod q 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem cos_two_pi_div_pos {k n : ℕ} (hn : 0 < n) (hk : 4 * k < n) :
    0 < Real.cos (2 * Real.pi * k / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (4 * k : ℝ) < n := by exact_mod_cast hk
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 ≤ 2 * Real.pi * k / n := by positivity
    linarith [Real.pi_pos]
  · rw [div_lt_iff₀ hn']
    nlinarith [Real.pi_pos]

/-- Rotation by `θ = 2πk/n ∈ [0, π/2)`. -/
theorem evC_rotQ (k n : ℕ) (hn : 0 < n) (hk : 4 * k < n) (a b : SExpr) :
    evC env (SC.rotQ k n a b) = evC env (a, b) * twiddle false n k := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [twiddle_false_eq, evC_mul_mk]
  unfold SC.rotQ
  split
  · next h0 =>
    have : k = 0 := by simpa using h0
    subst this
    apply Complex.ext <;> simp [evC]
  split
  · next _ h8 =>
    have h8' : 8 * k = n := by simpa using h8
    have hθ : 2 * Real.pi * k / n = Real.pi / 4 := by
      rw [← h8']; push_cast
      have hk0 : (k : ℝ) ≠ 0 := by
        intro h; simp at h; subst h; simp at h8'; omega
      field_simp; ring
    rw [hθ, Real.cos_pi_div_four, Real.sin_pi_div_four]
    apply Complex.ext <;> simp [evC, ev_mkMulC, ev_mkSub, ev_mkAdd, Cst.toReal] <;> ring
  split
  · have ht := Real.tan_mul_cos (cos_two_pi_div_pos hn hk).ne'
    apply Complex.ext <;> simp only [evC, ev_mkMulC, ev_mkFnmaC, ev_mkFmaC, Cst.toReal]
    · linear_combination (-ev env b) * ht
    · linear_combination (ev env a) * ht
  · have hle : 4 * k ≤ n := by omega
    have hθ : 2 * Real.pi * ((n - 4 * k : ℕ) : ℝ) / ((4 * n : ℕ) : ℝ) =
        Real.pi / 2 - 2 * Real.pi * k / n := by
      push_cast [Nat.cast_sub hle]
      field_simp; ring
    have ht := Real.tan_mul_cos (cos_two_pi_div_pos (k := n - 4 * k) (n := 4 * n)
      (by omega) (by omega)).ne'
    rw [hθ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at ht
    apply Complex.ext <;>
      simp only [evC, ev_mkMulC, ev_mkFmsC, ev_mkFmaC, Cst.toReal, hθ,
        Real.cos_pi_div_two_sub]
    · linear_combination (ev env a) * ht
    · linear_combination (ev env b) * ht

theorem evC_mulIPow (q : ℕ) (re im : SExpr) :
    evC env (SC.mulIPow q re im) = evC env (re, im) * I ^ q := by
  rw [I_pow_mod]
  unfold SC.mulIPow
  split
  · next h => rw [h]; simp
  · next h => rw [h]; apply Complex.ext <;> simp [evC, ev_mkNeg]
  · next h => rw [h]; apply Complex.ext <;> simp [evC, ev_mkNeg, pow_two]
  · rename_i h0 h1 h2
    simp only [imp_false] at h0 h1 h2
    have : q % 4 = 3 := by omega
    rw [this]
    apply Complex.ext <;> simp [evC, ev_mkNeg, pow_succ]

/-- **Twiddle multiplication** is exact: `rot fwd n k a b` denotes `(a + ib) · ω`. -/
theorem evC_rot (fwd : Bool) (n k : ℕ) (hn : 0 < n) (a b : SExpr) :
    evC env (SC.rot fwd n k a b) = evC env (a, b) * twiddle fwd n k := by
  set k1 := if fwd then (n - k % n) % n else k % n with hk1
  have hk1n : k1 < n := by rw [hk1]; split <;> exact Nat.mod_lt _ hn
  have hrot : SC.rot fwd n k a b =
      SC.mulIPow (4 * k1 / n) (SC.rotQ (4 * k1 - 4 * k1 / n * n) (4 * n) a b).1
        (SC.rotQ (4 * k1 - 4 * k1 / n * n) (4 * n) a b).2 := by
    simp only [SC.rot, hk1]
  have hk₁ : 4 * k1 - 4 * k1 / n * n = 4 * k1 % n := by
    rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm n]
  rw [hrot, evC_mulIPow, hk₁]
  have hq := evC_rotQ env (4 * k1 % n) (4 * n) (by omega) (by have := Nat.mod_lt (4 * k1) hn; omega) a b
  rw [show ((SC.rotQ (4 * k1 % n) (4 * n) a b).1, (SC.rotQ (4 * k1 % n) (4 * n) a b).2) =
    SC.rotQ (4 * k1 % n) (4 * n) a b from rfl, hq, mul_assoc]
  congr 1
  rw [I_eq_twiddle, twiddle_pow, one_mul, ← twiddle_scale false hn (4 * k1 / n), Nat.mul_comm n 4,
    ← twiddle_add, Nat.mod_add_div, twiddle_scale false (by norm_num : 0 < 4)]
  rw [hk1]
  cases fwd
  · simp only [Bool.false_eq_true, ite_false]
    exact twiddle_mod false hn k
  · simp only [ite_true]
    rw [twiddle_mod false hn, twiddle_true_eq_inv]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← twiddle_mod false hn k, ← twiddle_add, Nat.sub_add_cancel (Nat.mod_lt k hn).le]
    simpa using twiddle_mul_self false hn 1

/-! ### Inputs used by expressions -/

open SExpr

variable {m : ℕ}

theorem il_mkNeg {a : SExpr} (h : a.InputsLt m) : (mkNeg a).InputsLt m := by
  unfold mkNeg; split <;> simp_all [SExpr.InputsLt]

theorem il_mkAdd {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) : (mkAdd a b).InputsLt m := by
  unfold mkAdd; split <;> simp_all [SExpr.InputsLt]

theorem il_mkSub {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) : (mkSub a b).InputsLt m := by
  unfold mkSub; split <;> (try apply il_mkNeg) <;> simp_all [SExpr.InputsLt]

theorem il_mkMulC (c : Cst) {a : SExpr} (ha : a.InputsLt m) : (mkMulC c a).InputsLt m := by
  unfold mkMulC; split <;> (try apply il_mkNeg) <;> simp_all [SExpr.InputsLt]

theorem il_mkFmaAdd (c1 c2 : Cst) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (mkFmaAdd c1 a c2 b).InputsLt m := by
  unfold mkFmaAdd; split <;> simp_all [SExpr.InputsLt, il_mkMulC]

theorem il_mkFmaSub (c1 c2 : Cst) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (mkFmaSub c1 a c2 b).InputsLt m := by
  unfold mkFmaSub; split <;> simp_all [SExpr.InputsLt, il_mkMulC, il_mkNeg]

theorem il_mkFnmaC (t : Cst) {a b : SExpr} (hb : b.InputsLt m) (ha : a.InputsLt m) :
    (mkFnmaC t b a).InputsLt m := by
  unfold mkFnmaC; split <;> simp_all [SExpr.InputsLt]

theorem il_mkFmaC (t : Cst) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (mkFmaC t a b).InputsLt m := by
  unfold mkFmaC; split <;> simp_all [SExpr.InputsLt]

theorem il_mkFmsC (t : Cst) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (mkFmsC t a b).InputsLt m := by
  unfold mkFmsC; split <;> simp_all [SExpr.InputsLt, il_mkNeg]

theorem il_rotQ (k n : ℕ) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (SC.rotQ k n a b).1.InputsLt m ∧ (SC.rotQ k n a b).2.InputsLt m := by
  unfold SC.rotQ
  split; · exact ⟨ha, hb⟩
  split; · exact ⟨il_mkMulC _ (il_mkSub ha hb), il_mkMulC _ (il_mkAdd ha hb)⟩
  split
  · exact ⟨il_mkMulC _ (il_mkFnmaC _ hb ha), il_mkMulC _ (il_mkFmaC _ ha hb)⟩
  · exact ⟨il_mkMulC _ (il_mkFmsC _ ha hb), il_mkMulC _ (il_mkFmaC _ hb ha)⟩

theorem il_mulIPow (q : ℕ) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (SC.mulIPow q a b).1.InputsLt m ∧ (SC.mulIPow q a b).2.InputsLt m := by
  unfold SC.mulIPow; split <;> simp_all [il_mkNeg]

theorem il_rot (fwd : Bool) (n k : ℕ) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (SC.rot fwd n k a b).1.InputsLt m ∧ (SC.rot fwd n k a b).2.InputsLt m := by
  simp only [SC.rot]
  have := il_rotQ (m := m) (4 * (if fwd then (n - k % n) % n else k % n) -
    4 * (if fwd then (n - k % n) % n else k % n) / n * n) (4 * n) ha hb
  exact il_mulIPow _ this.1 this.2

/-! ### Symbolic complex values -/

/-- The complex number denoted by a symbolic value. -/
noncomputable def SC.toC : SC → ℂ
  | .tw fwd n k => twiddle fwd n k
  | .val re im => evC env (re, im)

/-- Well-formed symbolic values: twiddles have positive order, and expressions only use
inputs below `m`. -/
def SC.Good (m : ℕ) : SC → Prop
  | .tw _ n _ => 0 < n
  | .val re im => re.InputsLt m ∧ im.InputsLt m

theorem parts_spec {x : SC} (hx : x.Good m) :
    evC env x.parts = x.toC env ∧ x.parts.1.InputsLt m ∧ x.parts.2.InputsLt m := by
  cases x with
  | tw fwd n k =>
    simp only [SC.Good] at hx
    simp only [SC.parts, SC.toC]
    refine ⟨?_, il_rot fwd n k (by simp [SExpr.InputsLt]) (by simp [SExpr.InputsLt])⟩
    rw [show ((SC.rot fwd n k (.cst (.cos 0 1)) .zero).1, (SC.rot fwd n k (.cst (.cos 0 1)) .zero).2) =
      SC.rot fwd n k (.cst (.cos 0 1)) .zero from rfl, evC_rot env fwd n k hx]
    have : evC env (SExpr.cst (Cst.cos 0 1), SExpr.zero) = 1 := by
      apply Complex.ext <;> simp [evC, Cst.toReal]
    rw [this, one_mul]
  | val re im => exact ⟨rfl, hx⟩

theorem sc_add {x y : SC} (hx : x.Good m) (hy : y.Good m) :
    (SC.add x y).toC env = x.toC env + y.toC env ∧ (SC.add x y).Good m := by
  obtain ⟨px, px1, px2⟩ := parts_spec env hx
  obtain ⟨py, py1, py2⟩ := parts_spec env hy
  refine ⟨?_, il_mkAdd px1 py1, il_mkAdd px2 py2⟩
  rw [← px, ← py]
  apply Complex.ext <;> simp [SC.add, SC.toC, evC, ev_mkAdd]

theorem sc_sub {x y : SC} (hx : x.Good m) (hy : y.Good m) :
    (SC.sub x y).toC env = x.toC env - y.toC env ∧ (SC.sub x y).Good m := by
  obtain ⟨px, px1, px2⟩ := parts_spec env hx
  obtain ⟨py, py1, py2⟩ := parts_spec env hy
  refine ⟨?_, il_mkSub px1 py1, il_mkSub px2 py2⟩
  rw [← px, ← py]
  apply Complex.ext <;> simp [SC.sub, SC.toC, evC, ev_mkSub]

theorem sc_mulGen {x y : SC} (hx : x.Good m) (hy : y.Good m) :
    (SC.mulGen x y).toC env = x.toC env * y.toC env ∧ (SC.mulGen x y).Good m := by
  obtain ⟨px, px1, px2⟩ := parts_spec env hx
  obtain ⟨py, py1, py2⟩ := parts_spec env hy
  refine ⟨?_, ⟨⟨px1, py1, px2, py2⟩, ⟨px1, py2, px2, py1⟩⟩⟩
  rw [← px, ← py]
  apply Complex.ext <;> simp [SC.mulGen, SC.toC, evC]

theorem sc_mul {x y : SC} (hx : x.Good m) (hy : y.Good m) :
    (SC.mul x y).toC env = x.toC env * y.toC env ∧ (SC.mul x y).Good m := by
  cases x with
  | tw f n k =>
    cases y with
    | tw f' n' k' =>
      obtain ⟨py, py1, py2⟩ := parts_spec env hy
      simp only [SC.Good] at hx
      refine ⟨?_, il_rot f n k py1 py2⟩
      simp only [SC.mul, SC.toC]
      rw [show evC env ((SC.rot f n k (SC.tw f' n' k').parts.1 (SC.tw f' n' k').parts.2).1,
        (SC.rot f n k (SC.tw f' n' k').parts.1 (SC.tw f' n' k').parts.2).2) =
        evC env (SC.rot f n k (SC.tw f' n' k').parts.1 (SC.tw f' n' k').parts.2) from rfl,
        evC_rot env f n k hx, show ((SC.tw f' n' k').parts.1, (SC.tw f' n' k').parts.2) =
          (SC.tw f' n' k').parts from rfl, py, mul_comm]
      rfl
    | val a b =>
      simp only [SC.Good] at hx hy
      refine ⟨?_, il_rot f n k hy.1 hy.2⟩
      simp only [SC.mul, SC.toC]
      rw [show evC env ((SC.rot f n k a b).1, (SC.rot f n k a b).2) = evC env (SC.rot f n k a b)
        from rfl, evC_rot env f n k hx, mul_comm]
  | val a b =>
    cases y with
    | tw f n k =>
      simp only [SC.Good] at hx hy
      refine ⟨?_, il_rot f n k hx.1 hx.2⟩
      simp only [SC.mul, SC.toC]
      rw [show evC env ((SC.rot f n k a b).1, (SC.rot f n k a b).2) = evC env (SC.rot f n k a b)
        from rfl, evC_rot env f n k hy]
    | val c d =>
      exact sc_mulGen env hx hy

end Eval

/-! ### Running the generic algorithm on symbolic values -/

section Exec

variable (env : ℕ → ℝ) {m : ℕ}

theorem symOps_get_build (n : ℕ) (f : ℕ → SC) {i : ℕ} (hi : i < n) :
    symOps.get (symOps.build n f) i = f i := by
  simp [symOps, Array.getD, hi]

theorem sumRange_congr {C V : Type} (O : Ops C V) (n : ℕ) (f g : ℕ → C)
    (h : ∀ j < n, f j = g j) : sumRange O n f = sumRange O n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, Nat.fold_succ] at ih ⊢
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem sumRange_sym (n : ℕ) (f : ℕ → SC) (hf : ∀ j < n, (f j).Good m) :
    (sumRange symOps n f).toC env = ∑ j ∈ range n, (f j).toC env ∧
      (sumRange symOps n f).Good m := by
  induction n with
  | zero =>
    refine ⟨?_, by simp [sumRange, symOps, SC.Good, SExpr.InputsLt]⟩
    simp only [sumRange, Nat.fold_zero, Finset.range_zero, Finset.sum_empty]
    apply Complex.ext <;> simp [symOps, SC.toC, evC]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (by omega))
    have : sumRange symOps (n + 1) f = SC.add (sumRange symOps n f) (f n) := by
      simp only [sumRange, Nat.fold_succ]; rfl
    rw [this]
    obtain ⟨a1, a2⟩ := sc_add env h2 (hf n (by omega))
    exact ⟨by rw [a1, h1, Finset.sum_range_succ], a2⟩

theorem mkPlan_size_gen {C V : Type} (O : Ops C V) (fwd : Bool) :
    ∀ fs : List ℕ, (mkPlan O fwd fs).size = fs.prod
  | [] => by simp [mkPlan, Plan.size]
  | [p] => by simp [mkPlan, Plan.size]
  | r :: s :: rest => by
    simp only [mkPlan, Plan.size]
    rw [mkPlan_size_gen O fwd (s :: rest)]
    simp

theorem exec_direct_sym (n : ℕ) (w : Array SC) (x : ℕ → SC) {k : ℕ} (hk : k < n) :
    symOps.get (exec symOps (.direct n w) x) k =
      sumRange symOps n (fun j => symOps.mul (symOps.get w (j * k % n)) (x j)) := by
  simp only [exec]
  exact symOps_get_build _ _ hk

theorem exec_ct_sym (r : ℕ) (w : Array SC) (sub : Plan (Array SC)) (x : ℕ → SC) {k : ℕ}
    (hk : k < r * sub.size) :
    symOps.get (exec symOps (.ct r w sub) x) k =
      sumRange symOps r (fun j1 => symOps.mul (symOps.get w (j1 * k % (r * sub.size)))
        (symOps.get (exec symOps sub (fun j2 => x (j1 + r * j2))) (k % sub.size))) := by
  simp only [exec]
  rw [symOps_get_build _ _ hk]
  apply sumRange_congr
  intro j1 hj1
  simp [Array.getD, hj1]

/-- One direct node: symbolic execution denotes exact execution. -/
theorem direct_sym (fwd : Bool) (n : ℕ) (hn : 0 < n) (x : ℕ → SC)
    (hx : ∀ j < n, (x j).Good m) (k : ℕ) (hk : k < n) :
    (symOps.get (exec symOps (.direct n (symOps.build n (symOps.tw fwd n))) x) k).toC env =
      exec exactOps (.direct n (exactOps.build n (exactOps.tw fwd n))) (fun j => (x j).toC env) k ∧
    (symOps.get (exec symOps (.direct n (symOps.build n (symOps.tw fwd n))) x) k).Good m := by
  rw [exec_direct_sym _ _ _ hk, exec_direct_exact]
  have hmul : ∀ j < n,
      (symOps.mul (symOps.get (symOps.build n (symOps.tw fwd n)) (j * k % n)) (x j)).toC env =
        twiddle fwd n (j * k % n) * (x j).toC env ∧
      (symOps.mul (symOps.get (symOps.build n (symOps.tw fwd n)) (j * k % n)) (x j)).Good m := by
    intro j hj
    rw [symOps_get_build _ _ (Nat.mod_lt _ hn)]
    exact sc_mul env (m := m) (x := SC.tw fwd n (j * k % n)) hn (hx j hj)
  obtain ⟨h1, h2⟩ := sumRange_sym env n _ (fun j hj => (hmul j hj).2)
  refine ⟨?_, h2⟩
  rw [h1]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hmul j (Finset.mem_range.mp hj)).1]
  rfl

/-- **Symbolic execution denotes exact execution.** -/
theorem exec_sym (fwd : Bool) : ∀ (fs : List ℕ), (∀ f ∈ fs, 0 < f) → ∀ (x : ℕ → SC),
    (∀ j < fs.prod, (x j).Good m) → ∀ k < fs.prod,
      (symOps.get (exec symOps (mkPlan symOps fwd fs) x) k).toC env =
        exec exactOps (mkPlan exactOps fwd fs) (fun j => (x j).toC env) k ∧
      (symOps.get (exec symOps (mkPlan symOps fwd fs) x) k).Good m
  | [], _, x, hx, k, hk => by
    simp only [mkPlan]
    exact direct_sym env fwd 1 (by norm_num) x (fun j hj => hx j (by simpa using hj)) k
      (by simpa using hk)
  | [p], hpos, x, hx, k, hk => by
    simp only [mkPlan]
    exact direct_sym env fwd p (hpos p (by simp)) x (fun j hj => hx j (by simpa using hj)) k
      (by simpa using hk)
  | r :: s :: rest, hpos, x, hx, k, hk => by
    have hr : 0 < r := hpos r (by simp)
    have hrest : ∀ f ∈ s :: rest, 0 < f := fun f hf => hpos f (List.mem_cons_of_mem _ hf)
    have hm : 0 < (s :: rest).prod := List.prod_pos hrest
    have hszS : (mkPlan symOps fwd (s :: rest)).size = (s :: rest).prod := mkPlan_size_gen _ _ _
    have hszE : (mkPlan exactOps fwd (s :: rest)).size = (s :: rest).prod := mkPlan_size_gen _ _ _
    have hprod : (r :: s :: rest).prod = r * (s :: rest).prod := List.prod_cons
    have hplanS : mkPlan symOps fwd (r :: s :: rest) =
        .ct r (symOps.build (r * (s :: rest).prod) (symOps.tw fwd (r * (s :: rest).prod)))
          (mkPlan symOps fwd (s :: rest)) := by simp only [mkPlan]
    have hplanE : mkPlan exactOps fwd (r :: s :: rest) =
        .ct r (exactOps.build (r * (s :: rest).prod) (exactOps.tw fwd (r * (s :: rest).prod)))
          (mkPlan exactOps fwd (s :: rest)) := by simp only [mkPlan]
    rw [hprod] at hk hx
    rw [hplanS, hplanE, exec_ct_sym _ _ _ _ (by rw [hszS]; exact hk), exec_ct_exact, hszS, hszE]
    have hsub : ∀ j1 < r,
        (symOps.get (exec symOps (mkPlan symOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2)))
          (k % (s :: rest).prod)).toC env =
          exec exactOps (mkPlan exactOps fwd (s :: rest)) (fun j2 => (x (j1 + r * j2)).toC env)
            (k % (s :: rest).prod) ∧
        (symOps.get (exec symOps (mkPlan symOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2)))
          (k % (s :: rest).prod)).Good m := fun j1 hj1 =>
      exec_sym fwd (s :: rest) hrest (fun j2 => x (j1 + r * j2))
        (fun j2 hj2 => hx _ (by nlinarith)) (k % (s :: rest).prod) (Nat.mod_lt _ hm)
    have hmul : ∀ j1 < r,
        (symOps.mul (symOps.get (symOps.build (r * (s :: rest).prod)
            (symOps.tw fwd (r * (s :: rest).prod))) (j1 * k % (r * (s :: rest).prod)))
          (symOps.get (exec symOps (mkPlan symOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2)))
            (k % (s :: rest).prod))).toC env =
          twiddle fwd (r * (s :: rest).prod) (j1 * k % (r * (s :: rest).prod)) *
            exec exactOps (mkPlan exactOps fwd (s :: rest)) (fun j2 => (x (j1 + r * j2)).toC env)
              (k % (s :: rest).prod) ∧
        (symOps.mul (symOps.get (symOps.build (r * (s :: rest).prod)
            (symOps.tw fwd (r * (s :: rest).prod))) (j1 * k % (r * (s :: rest).prod)))
          (symOps.get (exec symOps (mkPlan symOps fwd (s :: rest)) (fun j2 => x (j1 + r * j2)))
            (k % (s :: rest).prod))).Good m := by
      intro j1 hj1
      rw [symOps_get_build _ _ (Nat.mod_lt _ (Nat.mul_pos hr hm))]
      obtain ⟨s1, s2⟩ := hsub j1 hj1
      obtain ⟨m1, m2⟩ := sc_mul env (m := m)
        (x := SC.tw fwd (r * (s :: rest).prod) (j1 * k % (r * (s :: rest).prod)))
        (Nat.mul_pos hr hm) s2
      exact ⟨m1.trans (by rw [s1]; rfl), m2⟩
    obtain ⟨h1, h2⟩ := sumRange_sym env r _ (fun j1 hj1 => (hmul j1 hj1).2)
    refine ⟨?_, h2⟩
    rw [h1]
    apply Finset.sum_congr rfl
    intro j1 hj1
    rw [(hmul j1 (Finset.mem_range.mp hj1)).1]
    rfl

/-! ## Prime factorization used by the butterflies -/

theorem primeFactors_go_spec : ∀ (fuel n d : ℕ), 1 ≤ d →
    (∀ f ∈ primeFactors.go n d fuel, 0 < f) ∧ (1 ≤ n → (primeFactors.go n d fuel).prod = n)
  | 0, n, d, _ => by
    unfold primeFactors.go
    split_ifs with h
    · exact ⟨by simp; omega, by simp⟩
    · exact ⟨by simp, by intro; simp; omega⟩
  | fuel + 1, n, d, hd => by
    unfold primeFactors.go
    split_ifs with h1 h2 h3
    · exact ⟨by simp, by intro; simp; omega⟩
    · exact ⟨by simp; omega, by simp⟩
    · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h3)
      have hdn : d ≤ n := by nlinarith
      obtain ⟨ih1, ih2⟩ := primeFactors_go_spec fuel (n / d) d hd
      refine ⟨?_, fun _ => ?_⟩
      · intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · omega
        · exact ih1 f hf
      · rw [List.prod_cons, ih2 (Nat.div_pos hdn (by omega)), Nat.mul_div_cancel' hdvd]
    · exact primeFactors_go_spec fuel n (d + 1) (by omega)

theorem primeFactors_pos (n : ℕ) : ∀ f ∈ primeFactors n, 0 < f :=
  (primeFactors_go_spec n n 2 (by norm_num)).1

theorem primeFactors_prod {n : ℕ} (hn : 0 < n) : (primeFactors n).prod = n :=
  (primeFactors_go_spec n n 2 (by norm_num)).2 hn

/-! ## FMA contraction preserves exact values -/

section Contract

open SExpr

theorem ev_contractAdd (env : ℕ → ℝ) (a b : SExpr) :
    ev env (contractAdd a b) = ev env a + ev env b := by
  unfold contractAdd; split <;> simp; ring

theorem ev_contractSub (env : ℕ → ℝ) (a b : SExpr) :
    ev env (contractSub a b) = ev env a - ev env b := by
  unfold contractSub; split <;> simp

theorem ev_contract (env : ℕ → ℝ) : ∀ e : SExpr, ev env e.contract = ev env e
  | .add a b => by simp only [contract, ev_contractAdd, ev_contract env a, ev_contract env b, ev_add]
  | .sub a b => by simp only [contract, ev_contractSub, ev_contract env a, ev_contract env b, ev_sub]
  | .mul a b => by simp only [contract, ev_mul, ev_contract env a, ev_contract env b]
  | .neg a => by simp only [contract, ev_neg, ev_contract env a]
  | .fma a b c => by simp only [contract, ev_fma, ev_contract env a, ev_contract env b, ev_contract env c]
  | .fms a b c => by simp only [contract, ev_fms, ev_contract env a, ev_contract env b, ev_contract env c]
  | .fnma a b c => by simp only [contract, ev_fnma, ev_contract env a, ev_contract env b, ev_contract env c]
  | .input _ => rfl
  | .zero => rfl
  | .cst _ => rfl

theorem il_contractAdd {m : ℕ} {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (contractAdd a b).InputsLt m := by
  unfold contractAdd; split <;> simp_all [SExpr.InputsLt]

theorem il_contractSub {m : ℕ} {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (contractSub a b).InputsLt m := by
  unfold contractSub; split <;> simp_all [SExpr.InputsLt]

theorem il_contract {m : ℕ} : ∀ {e : SExpr}, e.InputsLt m → e.contract.InputsLt m
  | .add _ _, h => il_contractAdd (il_contract h.1) (il_contract h.2)
  | .sub _ _, h => il_contractSub (il_contract h.1) (il_contract h.2)
  | .mul _ _, h => ⟨il_contract h.1, il_contract h.2⟩
  | .neg a, h => il_contract (e := a) h
  | .fma _ _ _, h => ⟨il_contract h.1, il_contract h.2.1, il_contract h.2.2⟩
  | .fms _ _ _, h => ⟨il_contract h.1, il_contract h.2.1, il_contract h.2.2⟩
  | .fnma _ _ _, h => ⟨il_contract h.1, il_contract h.2.1, il_contract h.2.2⟩
  | .input _, h => h
  | .zero, h => h
  | .cst _, h => h

end Contract

/-! ## Paired odd-length leaves and factored mixed-radix butterflies (`symDFT`) -/

/-- The sign of a flag. -/
noncomputable def sgn (b : Bool) : ℝ := if b then -1 else 1

/-! ### Constants -/

theorem cosH_spec {m n : ℕ} (hn : 0 < n) (h2 : 2 * m ≤ n) :
    sgn (cosH m n).1 * (cosH m n).2.toReal = Real.cos (2 * Real.pi * m / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold cosH
  split_ifs with h4
  · simp [sgn, Cst.toReal]
  · simp only [sgn, ite_true, Cst.toReal]
    rw [Nat.cast_sub h2]
    push_cast
    have : 2 * Real.pi * ((n : ℝ) - 2 * m) / (2 * n) = Real.pi - 2 * Real.pi * m / n := by
      field_simp
    rw [this, Real.cos_pi_sub]; ring

theorem cosQ_spec {m n : ℕ} (hm : m < n) :
    sgn (cosQ m n).1 * (cosQ m n).2.toReal = Real.cos (2 * Real.pi * m / n) := by
  have hn : 0 < n := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold cosQ
  split_ifs with h2
  · exact cosH_spec hn h2
  · rw [cosH_spec hn (by omega), Nat.cast_sub hm.le]
    have : 2 * Real.pi * ((n : ℝ) - m) / n = 2 * Real.pi - 2 * Real.pi * m / n := by
      field_simp
    rw [this, Real.cos_two_pi_sub]

theorem sinH_spec {m n : ℕ} (hn : 0 < n) (h2 : 2 * m ≤ n) :
    (sinH m n).toReal = Real.sin (2 * Real.pi * m / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sinH
  split_ifs with h4
  · simp [Cst.toReal]
  · simp only [Cst.toReal]
    rw [Nat.cast_sub h2]
    push_cast
    have : 2 * Real.pi * ((n : ℝ) - 2 * m) / (2 * n) = Real.pi - 2 * Real.pi * m / n := by
      field_simp
    rw [this, Real.sin_pi_sub]

theorem sinQ_spec {m n : ℕ} (hm : m < n) :
    sgn (sinQ m n).1 * (sinQ m n).2.toReal = Real.sin (2 * Real.pi * m / n) := by
  have hn : 0 < n := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sinQ
  split_ifs with h2
  · simp only [sgn, Bool.false_eq_true, ite_false, one_mul]; exact sinH_spec hn h2
  · simp only [sgn, ite_true]
    rw [sinH_spec hn (by omega), Nat.cast_sub hm.le]
    have : 2 * Real.pi * ((n : ℝ) - m) / n = 2 * Real.pi - 2 * Real.pi * m / n := by
      field_simp
    rw [this, Real.sin_two_pi_sub]; ring

/-! ### Fused accumulations -/

open SExpr in
theorem ev_sfma (ng : Bool) (c : Cst) (a acc : SExpr) :
    ev env (sfma ng c a acc) = ev env acc + sgn ng * c.toReal * ev env a := by
  unfold sfma sgn; cases ng <;> simp [ev_mkFnmaC, ev_mkFmaC] <;> ring

open SExpr in
theorem ev_smul (ng : Bool) (c : Cst) (a : SExpr) :
    ev env (smul ng c a) = sgn ng * c.toReal * ev env a := by
  unfold smul sgn; cases ng <;> simp [ev_mkNeg, ev_mkMulC]

/-- The value of a term `±c·a`. -/
noncomputable def tval (t : Bool × Cst × SExpr) : ℝ := sgn t.1 * t.2.1.toReal * ev env t.2.2

theorem ev_lacc (ts : List (Bool × Cst × SExpr)) : ∀ init : SExpr,
    ev env (lacc init ts) = ev env init + (ts.map (tval env)).sum := by
  induction ts with
  | nil => intro init; simp [lacc]
  | cons t ts ih =>
    intro init
    simp only [lacc, List.foldl_cons] at ih ⊢
    rw [ih, ev_sfma, List.map_cons, List.sum_cons, tval]; ring

theorem ev_lsum (ts : List (Bool × Cst × SExpr)) :
    ev env (lsum ts) = (ts.map (tval env)).sum := by
  cases ts with
  | nil => simp [lsum]
  | cons t ts => rw [lsum, ev_lacc, ev_smul, List.map_cons, List.sum_cons, tval]

theorem il_sfma (ng : Bool) (c : Cst) {a acc : SExpr} (ha : a.InputsLt m) (hacc : acc.InputsLt m) :
    (sfma ng c a acc).InputsLt m := by
  unfold sfma; cases ng
  · exact il_mkFmaC c ha hacc
  · exact il_mkFnmaC c ha hacc

theorem il_smul (ng : Bool) (c : Cst) {a : SExpr} (ha : a.InputsLt m) : (smul ng c a).InputsLt m := by
  unfold smul; cases ng
  · exact il_mkMulC c ha
  · exact il_mkNeg (il_mkMulC c ha)

theorem il_lacc (ts : List (Bool × Cst × SExpr)) (hts : ∀ t ∈ ts, t.2.2.InputsLt m) :
    ∀ init : SExpr, init.InputsLt m → (lacc init ts).InputsLt m := by
  induction ts with
  | nil => intro init h; simpa [lacc] using h
  | cons t ts ih =>
    intro init h
    simp only [lacc, List.foldl_cons] at ih ⊢
    exact ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) _
      (il_sfma _ _ (hts t (by simp)) h)

theorem il_lsum (ts : List (Bool × Cst × SExpr)) (hts : ∀ t ∈ ts, t.2.2.InputsLt m) :
    (lsum ts).InputsLt m := by
  cases ts with
  | nil => simp [lsum, SExpr.InputsLt]
  | cons t ts =>
    exact il_lacc ts (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) _
      (il_smul _ _ (hts t (by simp)))

theorem list_sum_range (f : ℕ → ℝ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem ev_foldAdd (g : ℕ → SExpr) (l : List ℕ) : ∀ init : SExpr,
    ev env (l.foldl (fun acc i => SExpr.mkAdd acc (g i)) init) = ev env init + (l.map fun i => ev env (g i)).sum := by
  induction l with
  | nil => intro init; simp
  | cons i l ih =>
    intro init
    rw [List.foldl_cons, ih, ev_mkAdd, List.map_cons, List.sum_cons]; ring

theorem il_foldAdd (g : ℕ → SExpr) (l : List ℕ) (hg : ∀ i ∈ l, (g i).InputsLt m) : ∀ init : SExpr,
    init.InputsLt m → (l.foldl (fun acc i => SExpr.mkAdd acc (g i)) init).InputsLt m := by
  induction l with
  | nil => intro init h; simpa using h
  | cons i l ih =>
    intro init h
    rw [List.foldl_cons]
    exact ih (fun i' hi' => hg i' (List.mem_cons_of_mem _ hi')) _ (il_mkAdd h (hg i (by simp)))

/-! ### Twiddles in coordinates -/

theorem inv_cs (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (⟨c, s⟩ : ℂ)⁻¹ = ⟨c, -s⟩ := by
  have hn : Complex.normSq ⟨c, s⟩ = 1 := by rw [Complex.normSq_mk]; nlinarith
  apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im, hn]

theorem twiddle_cs (fwd : Bool) {n : ℕ} (hn : 0 < n) (q : ℕ) :
    twiddle fwd n q = ⟨Real.cos (2 * Real.pi * (q % n : ℕ) / n),
      sgn fwd * Real.sin (2 * Real.pi * (q % n : ℕ) / n)⟩ := by
  rw [← twiddle_mod fwd hn q]
  cases fwd
  · rw [twiddle_false_eq]; simp [sgn]
  · rw [twiddle_true_eq_inv, twiddle_false_eq, inv_cs _ _ (by rw [add_comm]; exact Real.sin_sq_add_cos_sq _)]
    simp [sgn]

theorem twiddle_pair (fwd : Bool) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) (k : ℕ) :
    twiddle fwd n ((n - j) * k) = (twiddle fwd n (j * k))⁻¹ := by
  have : twiddle fwd n ((n - j) * k) * twiddle fwd n (j * k) = 1 := by
    rw [← twiddle_add, ← Nat.add_mul, Nat.sub_add_cancel hj, twiddle_mul_self fwd hn]
  exact eq_inv_of_mul_eq_one_left this

theorem twiddle_cs_sq (fwd : Bool) (θ : ℝ) : Real.cos θ ^ 2 + (sgn fwd * Real.sin θ) ^ 2 = 1 := by
  have := Real.cos_sq_add_sin_sq θ
  unfold sgn; cases fwd <;> simp [this]

/-! ### The odd-length leaf -/

/-- Pair the terms `j` and `2h + 1 - j` of a sum. -/
theorem sum_pair (f : ℕ → ℂ) (h : ℕ) :
    ∑ j ∈ range (2 * h + 1), f j = f 0 + ∑ i ∈ range h, (f (i + 1) + f (2 * h + 1 - (i + 1))) := by
  rw [Finset.sum_range_succ', two_mul, Finset.sum_range_add, Finset.sum_add_distrib]
  rw [← Finset.sum_range_reflect (fun x => f (h + x + 1)) h]
  have : ∑ j ∈ range h, f (h + (h - 1 - j) + 1) = ∑ j ∈ range h, f (2 * h + 1 - (j + 1)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := Finset.mem_range.mp hj
    congr 1; omega
  rw [this, two_mul]; ring

/-- A DFT of odd length as a sum over pairs, given the twiddles of the pairs. -/
theorem dft_odd_pairs (fwd : Bool) {p : ℕ} (hp : p % 2 = 1) (X : ℕ → ℂ) (k : ℕ) (T : ℕ → ℂ)
    (h1 : ∀ i < p / 2, twiddle fwd p ((i + 1) * k) = T i)
    (h2 : ∀ i < p / 2, twiddle fwd p ((p - (i + 1)) * k) = (T i)⁻¹) :
    dftSum fwd p X k = X 0 + ∑ i ∈ range (p / 2), (T i * X (i + 1) + (T i)⁻¹ * X (p - (i + 1))) := by
  have hp2 : p = 2 * (p / 2) + 1 := by omega
  unfold dftSum
  rw [hp2, sum_pair, ← hp2]
  have h0 : twiddle fwd p (0 * k) = 1 := by simp [twiddle]
  rw [h0, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  rw [h1 i hi', h2 i hi']

/-- One pair: `T x + T⁻¹ y = c (x + y) + i t (x - y)` for `T = c + i t` of modulus one. -/
theorem pair_term (c t : ℝ) (h : c ^ 2 + t ^ 2 = 1) (x y : ℂ) :
    (⟨c, t⟩ : ℂ) * x + (⟨c, t⟩ : ℂ)⁻¹ * y = (c : ℂ) * (x + y) + I * ((t : ℂ) * (x - y)) := by
  rw [inv_cs c t h]
  apply Complex.ext <;> simp <;> ring

/-! ### Values of the pieces of `oddLeaf` -/

section OddLeaf

variable {p : ℕ} (x : ℕ → SC)

/-- The angle `2π (q mod p) / p`. -/
noncomputable def ang (p q : ℕ) : ℝ := 2 * Real.pi * ((q % p : ℕ) : ℝ) / p

theorem toC_val (a b : SExpr) : (SC.val a b).toC env = evC env (a, b) := rfl

theorem parts_re_im {j : ℕ} (hj : (x j).Good m) :
    ev env (x j).parts.1 = ((x j).toC env).re ∧ ev env (x j).parts.2 = ((x j).toC env).im ∧
      (x j).parts.1.InputsLt m ∧ (x j).parts.2.InputsLt m := by
  obtain ⟨h, h1, h2⟩ := parts_spec env hj
  exact ⟨by rw [← h]; rfl, by rw [← h]; rfl, h1, h2⟩

theorem pairA_spec (hx : ∀ j < p, (x j).Good m) {i : ℕ} (hi : i < p / 2) :
    evC env (pairA p x i) = (x (i + 1)).toC env + (x (p - (i + 1))).toC env ∧
      (pairA p x i).1.InputsLt m ∧ (pairA p x i).2.InputsLt m := by
  obtain ⟨a1, a2, a3, a4⟩ := parts_re_im env x (hx (i + 1) (by omega))
  obtain ⟨b1, b2, b3, b4⟩ := parts_re_im env x (hx (p - (i + 1)) (by omega))
  refine ⟨?_, il_mkAdd a3 b3, il_mkAdd a4 b4⟩
  apply Complex.ext <;> simp [pairA, evC, ev_mkAdd, a1, a2, b1, b2]

theorem pairB_spec (hx : ∀ j < p, (x j).Good m) {i : ℕ} (hi : i < p / 2) :
    evC env (pairB p x i) = (x (i + 1)).toC env - (x (p - (i + 1))).toC env ∧
      (pairB p x i).1.InputsLt m ∧ (pairB p x i).2.InputsLt m := by
  obtain ⟨a1, a2, a3, a4⟩ := parts_re_im env x (hx (i + 1) (by omega))
  obtain ⟨b1, b2, b3, b4⟩ := parts_re_im env x (hx (p - (i + 1)) (by omega))
  refine ⟨?_, il_mkSub a3 b3, il_mkSub a4 b4⟩
  apply Complex.ext <;> simp [pairB, evC, ev_mkSub, a1, a2, b1, b2]

theorem oddA_spec (hp : 0 < p) (hx : ∀ j < p, (x j).Good m) (k : ℕ) :
    evC env (oddA p k x) = (x 0).toC env + ∑ i ∈ range (p / 2),
        (Real.cos (ang p ((i + 1) * k)) : ℂ) * ((x (i + 1)).toC env + (x (p - (i + 1))).toC env) ∧
      (oddA p k x).1.InputsLt m ∧ (oddA p k x).2.InputsLt m := by
  obtain ⟨z1, z2, z3, z4⟩ := parts_re_im env x (hx 0 hp)
  have hc : ∀ i, sgn (cosQ ((i + 1) * k % p) p).1 * (cosQ ((i + 1) * k % p) p).2.toReal =
      Real.cos (ang p ((i + 1) * k)) := fun i => cosQ_spec (Nat.mod_lt _ hp)
  have hil : ∀ (part : SExpr × SExpr → SExpr), (∀ i < p / 2, (part (pairA p x i)).InputsLt m) →
      ∀ t ∈ cTerms p k x part, t.2.2.InputsLt m := by
    intro part hpart t ht
    simp only [cTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact hpart i hi
  refine ⟨?_, il_lacc _ (hil _ fun i hi => (pairA_spec env x hx hi).2.1) _ z3,
    il_lacc _ (hil _ fun i hi => (pairA_spec env x hx hi).2.2) _ z4⟩
  apply Complex.ext
  · simp only [oddA, evC, ev_lacc, cTerms, List.map_map, Complex.add_re, Complex.re_sum,
      Complex.re_ofReal_mul]
    rw [z1, list_sum_range]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Function.comp, tval]
    rw [hc i, show ev env (pairA p x i).1 = (evC env (pairA p x i)).re from rfl,
      (pairA_spec env x hx (Finset.mem_range.mp hi)).1, Complex.add_re]
  · simp only [oddA, evC, ev_lacc, cTerms, List.map_map, Complex.add_im, Complex.im_sum,
      Complex.im_ofReal_mul]
    rw [z2, list_sum_range]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Function.comp, tval]
    rw [hc i, show ev env (pairA p x i).2 = (evC env (pairA p x i)).im from rfl,
      (pairA_spec env x hx (Finset.mem_range.mp hi)).1, Complex.add_im]

theorem oddS_spec (hp : 0 < p) (hx : ∀ j < p, (x j).Good m) (k : ℕ) :
    evC env (oddS p k x) = ∑ i ∈ range (p / 2),
        (Real.sin (ang p ((i + 1) * k)) : ℂ) * ((x (i + 1)).toC env - (x (p - (i + 1))).toC env) ∧
      (oddS p k x).1.InputsLt m ∧ (oddS p k x).2.InputsLt m := by
  have hs : ∀ i, sgn (sinQ ((i + 1) * k % p) p).1 * (sinQ ((i + 1) * k % p) p).2.toReal =
      Real.sin (ang p ((i + 1) * k)) := fun i => sinQ_spec (Nat.mod_lt _ hp)
  have hil : ∀ (part : SExpr × SExpr → SExpr), (∀ i < p / 2, (part (pairB p x i)).InputsLt m) →
      ∀ t ∈ sTerms p k x part, t.2.2.InputsLt m := by
    intro part hpart t ht
    simp only [sTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact hpart i hi
  refine ⟨?_, il_lsum _ (hil _ fun i hi => (pairB_spec env x hx hi).2.1),
    il_lsum _ (hil _ fun i hi => (pairB_spec env x hx hi).2.2)⟩
  apply Complex.ext
  · simp only [oddS, evC, ev_lsum, sTerms, List.map_map, Complex.re_sum, Complex.re_ofReal_mul]
    rw [list_sum_range]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Function.comp, tval]
    rw [hs i, show ev env (pairB p x i).1 = (evC env (pairB p x i)).re from rfl,
      (pairB_spec env x hx (Finset.mem_range.mp hi)).1, Complex.sub_re]
  · simp only [oddS, evC, ev_lsum, sTerms, List.map_map, Complex.im_sum, Complex.im_ofReal_mul]
    rw [list_sum_range]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Function.comp, tval]
    rw [hs i, show ev env (pairB p x i).2 = (evC env (pairB p x i)).im from rfl,
      (pairB_spec env x hx (Finset.mem_range.mp hi)).1, Complex.sub_im]

theorem oddX0_spec (hp : 0 < p) (hx : ∀ j < p, (x j).Good m) :
    (oddX0 p x).toC env = (x 0).toC env + ∑ i ∈ range (p / 2),
        ((x (i + 1)).toC env + (x (p - (i + 1))).toC env) ∧ (oddX0 p x).Good m := by
  obtain ⟨z1, z2, z3, z4⟩ := parts_re_im env x (hx 0 hp)
  have hl : ∀ i ∈ List.range (p / 2), i < p / 2 := fun i hi => List.mem_range.mp hi
  refine ⟨?_, il_foldAdd _ _ (fun i hi => (pairA_spec env x hx (hl i hi)).2.1) _ z3,
    il_foldAdd _ _ (fun i hi => (pairA_spec env x hx (hl i hi)).2.2) _ z4⟩
  apply Complex.ext
  · simp only [oddX0, toC_val, evC, ev_foldAdd, Complex.add_re, Complex.re_sum]
    rw [z1, list_sum_range]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [show ev env (pairA p x i).1 = (evC env (pairA p x i)).re from rfl,
      (pairA_spec env x hx (Finset.mem_range.mp hi)).1, Complex.add_re]
  · simp only [oddX0, toC_val, evC, ev_foldAdd, Complex.add_im, Complex.im_sum]
    rw [z2, list_sum_range]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [show ev env (pairA p x i).2 = (evC env (pairA p x i)).im from rfl,
      (pairA_spec env x hx (Finset.mem_range.mp hi)).1, Complex.add_im]

theorem oddPlus_spec (k : ℕ) (hp : 0 < p) (hx : ∀ j < p, (x j).Good m) :
    (oddPlus p k x).toC env = evC env (oddA p k x) + I * evC env (oddS p k x) ∧
      (oddPlus p k x).Good m := by
  obtain ⟨-, a1, a2⟩ := oddA_spec env x hp hx k
  obtain ⟨-, s1, s2⟩ := oddS_spec env x hp hx k
  refine ⟨?_, il_mkSub a1 s2, il_mkAdd a2 s1⟩
  rw [oddPlus, toC_val]
  apply Complex.ext <;> simp [evC, ev_mkSub, ev_mkAdd, sub_eq_add_neg]

theorem oddMinus_spec (k : ℕ) (hp : 0 < p) (hx : ∀ j < p, (x j).Good m) :
    (oddMinus p k x).toC env = evC env (oddA p k x) - I * evC env (oddS p k x) ∧
      (oddMinus p k x).Good m := by
  obtain ⟨-, a1, a2⟩ := oddA_spec env x hp hx k
  obtain ⟨-, s1, s2⟩ := oddS_spec env x hp hx k
  refine ⟨?_, il_mkAdd a1 s2, il_mkSub a2 s1⟩
  rw [oddMinus, toC_val]
  apply Complex.ext <;> simp [evC, ev_mkSub, ev_mkAdd, sub_eq_add_neg]

/-- The DFT of odd length in terms of `A_{k₀}` and `S_{k₀}`, when the twiddles of the pairs
are `cos ± i e sin` of the angles `2π j k₀ / p`. -/
theorem dft_odd_AS (fwd : Bool) (hp : p % 2 = 1) (hx : ∀ j < p, (x j).Good m) (k k0 : ℕ)
    (e : ℝ) (he : e ^ 2 = 1) (T : ℕ → ℂ)
    (hT : ∀ i < p / 2, T i = ⟨Real.cos (ang p ((i + 1) * k0)), e * Real.sin (ang p ((i + 1) * k0))⟩)
    (h1 : ∀ i < p / 2, twiddle fwd p ((i + 1) * k) = T i)
    (h2 : ∀ i < p / 2, twiddle fwd p ((p - (i + 1)) * k) = (T i)⁻¹) :
    dftSum fwd p (fun j => (x j).toC env) k =
      evC env (oddA p k0 x) + I * ((e : ℂ) * evC env (oddS p k0 x)) := by
  have hp0 : 0 < p := by omega
  rw [dft_odd_pairs fwd hp _ k T h1 h2, (oddA_spec env x hp0 hx k0).1, (oddS_spec env x hp0 hx k0).1]
  rw [add_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  rw [hT i hi', pair_term _ _ (by rw [mul_pow, he, one_mul]; exact Real.cos_sq_add_sin_sq _)]
  push_cast; ring

/-- Outputs `1 ≤ k ≤ p/2`: `X_k = A_k + i·(±S_k)`. -/
theorem dft_odd_low (fwd : Bool) (hp : p % 2 = 1) (hx : ∀ j < p, (x j).Good m) (k : ℕ) :
    dftSum fwd p (fun j => (x j).toC env) k =
      evC env (oddA p k x) + I * ((sgn fwd : ℂ) * evC env (oddS p k x)) := by
  have hp0 : 0 < p := by omega
  exact dft_odd_AS env x fwd hp hx k k (sgn fwd) (by unfold sgn; split <;> norm_num) _
    (fun i _ => by rw [twiddle_cs fwd hp0]; rfl) (fun i _ => rfl)
    (fun i _ => twiddle_pair fwd hp0 (by omega) k)

/-- Outputs `p/2 < k < p`: `X_k = A_{p-k} - i·(±S_{p-k})`. -/
theorem dft_odd_high (fwd : Bool) (hp : p % 2 = 1) (hx : ∀ j < p, (x j).Good m) {k : ℕ}
    (hk : k < p) :
    dftSum fwd p (fun j => (x j).toC env) k =
      evC env (oddA p (p - k) x) + I * (((-sgn fwd : ℝ) : ℂ) * evC env (oddS p (p - k) x)) := by
  have hp0 : 0 < p := by omega
  have hk0 : k = p - (p - k) := by omega
  have hsq := twiddle_cs_sq fwd
  refine dft_odd_AS env x fwd hp hx k (p - k) (-sgn fwd) (by unfold sgn; split <;> norm_num)
    (fun i => (twiddle fwd p ((i + 1) * (p - k)))⁻¹) ?_ ?_ ?_
  · intro i _
    rw [twiddle_cs fwd hp0, inv_cs _ _ (hsq _)]
    simp [ang]
  · intro i _
    rw [hk0, Nat.mul_comm, twiddle_pair fwd hp0 (by omega), ← hk0, Nat.mul_comm]
  · intro i _
    simp only [inv_inv]
    rw [hk0, Nat.mul_comm, twiddle_pair fwd hp0 (by omega), ← hk0, Nat.mul_comm,
      twiddle_pair fwd hp0 (by omega), inv_inv]

theorem oddLeaf_spec (fwd : Bool) (hp : p % 2 = 1) (hx : ∀ j < p, (x j).Good m) {k : ℕ}
    (hk : k < p) :
    (symOps.get (oddLeaf fwd p x) k).toC env = dftSum fwd p (fun j => (x j).toC env) k ∧
      (symOps.get (oddLeaf fwd p x) k).Good m := by
  have hp0 : 0 < p := by omega
  have hget : symOps.get (oddLeaf fwd p x) k =
      (if k = 0 then oddX0 p x
       else if k ≤ p / 2 then (if fwd then oddMinus p k x else oddPlus p k x)
       else (if fwd then oddPlus p (p - k) x else oddMinus p (p - k) x)) :=
    symOps_get_build p _ hk
  rw [hget]
  split_ifs with h0 hh hf hf
  · subst h0
    obtain ⟨v, g⟩ := oddX0_spec env x hp0 hx
    refine ⟨?_, g⟩
    rw [v, dft_odd_pairs fwd hp _ 0 (fun _ => 1) (fun i _ => by simp [twiddle])
      (fun i _ => by simp [twiddle])]
    simp
  · obtain ⟨v, g⟩ := oddMinus_spec env x k hp0 hx
    refine ⟨?_, g⟩
    rw [v, dft_odd_low env x fwd hp hx k, hf]; simp [sgn]; ring
  · obtain ⟨v, g⟩ := oddPlus_spec env x k hp0 hx
    refine ⟨?_, g⟩
    rw [v, dft_odd_low env x fwd hp hx k, show fwd = false by simpa using hf]; simp [sgn]
  · obtain ⟨v, g⟩ := oddPlus_spec env x (p - k) hp0 hx
    refine ⟨?_, g⟩
    rw [v, dft_odd_high env x fwd hp hx hk, hf]; simp [sgn]
  · obtain ⟨v, g⟩ := oddMinus_spec env x (p - k) hp0 hx
    refine ⟨?_, g⟩
    rw [v, dft_odd_high env x fwd hp hx hk, show fwd = false by simpa using hf]; simp [sgn]; ring

end OddLeaf

/-! ### Leaves and the mixed-radix recursion -/

theorem leafSym_spec (fwd : Bool) {p : ℕ} (hp : 0 < p) (x : ℕ → SC) (hx : ∀ j < p, (x j).Good m)
    {k : ℕ} (hk : k < p) :
    (symOps.get (leafSym fwd p x) k).toC env = dftSum fwd p (fun j => (x j).toC env) k ∧
      (symOps.get (leafSym fwd p x) k).Good m := by
  unfold leafSym
  split_ifs with hodd
  · exact oddLeaf_spec env x fwd hodd.1 hx hk
  · obtain ⟨h1, h2⟩ := direct_sym env fwd p hp x hx k hk
    refine ⟨?_, h2⟩
    rw [h1]
    have := exec_mkPlan_exact fwd [p] (by simpa using hp) (fun j => (x j).toC env) k (by simpa using hk)
    simpa [mkPlan] using this

/-- **The symbolic mixed-radix DFT denotes the DFT.** -/
theorem symDFT_spec (fwd : Bool) : ∀ (fs : List ℕ), (∀ f ∈ fs, 0 < f) → ∀ (x : ℕ → SC),
    (∀ j < fs.prod, (x j).Good m) → ∀ k < fs.prod,
      (symOps.get (symDFT fwd fs x) k).toC env = dftSum fwd fs.prod (fun j => (x j).toC env) k ∧
      (symOps.get (symDFT fwd fs x) k).Good m
  | [], _, x, hx, k, hk => by
    simp only [List.prod_nil] at hx hk ⊢
    exact leafSym_spec env fwd (by norm_num) x hx hk
  | [p], hpos, x, hx, k, hk => by
    simp only [List.prod_cons, List.prod_nil, mul_one] at hx hk ⊢
    exact leafSym_spec env fwd (hpos p (by simp)) x hx hk
  | r :: s :: rest, hpos, x, hx, k, hk => by
    have hr : 0 < r := hpos r (by simp)
    have hrest : ∀ f ∈ s :: rest, 0 < f := fun f hf => hpos f (List.mem_cons_of_mem _ hf)
    set M := (s :: rest).prod with hM
    have hm : 0 < M := List.prod_pos hrest
    have hprod : (r :: s :: rest).prod = r * M := List.prod_cons
    rw [hprod] at hk hx ⊢
    -- the sub-transforms
    have hsub : ∀ j1 < r, ∀ k1 < M,
        (symOps.get (symDFT fwd (s :: rest) (fun j2 => x (j1 + r * j2))) k1).toC env =
          dftSum fwd M (fun j2 => (x (j1 + r * j2)).toC env) k1 ∧
        (symOps.get (symDFT fwd (s :: rest) (fun j2 => x (j1 + r * j2))) k1).Good m :=
      fun j1 hj1 k1 hk1 => symDFT_spec fwd (s :: rest) hrest _ (fun j2 hj2 => hx _ (by nlinarith)) k1 hk1
    have hk1 : k % M < M := Nat.mod_lt _ hm
    have hk2 : k / M < r := by rw [Nat.div_lt_iff_lt_mul hm]; linarith
    -- unfold one level: output `k` is output `k / M` of the leaf of column `k % M`
    set ys : Array (Array SC) := (Array.range r).map fun j1 =>
      symDFT fwd (s :: rest) (fun j2 => x (j1 + r * j2)) with hys
    set z : ℕ → SC := fun j1 => SC.mul (.tw fwd (r * M) (j1 * (k % M)))
      (symOps.get (ys.getD j1 #[]) (k % M)) with hz
    have hget : symOps.get (symDFT fwd (r :: s :: rest) x) k = symOps.get (leafSym fwd r z) (k / M) := by
      simp only [symDFT, ← hM, ← hys]
      rw [show (Array.range (r * M)).map (fun k => symOps.get (((Array.range M).map fun k1 =>
          leafSym fwd r fun j1 => SC.mul (.tw fwd (r * M) (j1 * k1))
            (symOps.get (ys.getD j1 #[]) k1)).getD (k % M) #[]) (k / M)) =
          symOps.build (r * M) _ from rfl, symOps_get_build (r * M) _ hk]
      simp [Array.getD, hk1, hz]
    have hzv : ∀ j1 < r, (z j1).toC env = twiddle fwd (r * M) (j1 * (k % M)) *
          dftSum fwd M (fun j2 => (x (j1 + r * j2)).toC env) (k % M) ∧ (z j1).Good m := by
      intro j1 hj1
      have hy : ys.getD j1 #[] = symDFT fwd (s :: rest) (fun j2 => x (j1 + r * j2)) := by
        simp [hys, Array.getD, hj1]
      obtain ⟨y1, y2⟩ := hsub j1 hj1 (k % M) hk1
      obtain ⟨m1, m2⟩ := sc_mul env (m := m) (x := SC.tw fwd (r * M) (j1 * (k % M)))
        (y := symOps.get (ys.getD j1 #[]) (k % M)) (Nat.mul_pos hr hm) (by rw [hy]; exact y2)
      exact ⟨by rw [hz]; simp only; rw [m1, hy, y1]; rfl, m2⟩
    obtain ⟨l1, l2⟩ := leafSym_spec env fwd hr z (fun j1 hj1 => (hzv j1 hj1).2) hk2
    refine ⟨?_, by rw [hget]; exact l2⟩
    rw [hget, l1, dftSum_ct fwd hr hm, dftSum]
    refine Finset.sum_congr rfl (fun j1 hj1 => ?_)
    have hj1' := Finset.mem_range.mp hj1
    show _ * (z j1).toC env = _
    rw [(hzv j1 hj1').1, ← mul_assoc]
    congr 1
    -- `ω_r^{j₁ k₂} ω_n^{j₁ k₁} = ω_n^{j₁ k}` for `k = k₁ + M k₂`
    have hkk : j1 * k = j1 * (k % M) + M * (j1 * (k / M)) := by
      conv_lhs => rw [← Nat.mod_add_div k M]
      ring
    rw [hkk, twiddle_add, mul_comm (twiddle fwd (r * M) _), mul_comm r M,
      twiddle_scale fwd hm (j1 * (k / M))]

/-! ### Coprime factors: the prime factor algorithm -/

/-- The Good–Thomas index map `(j₁, j₂) ↦ (m j₁ + r j₂) mod rm` is a bijection
`[0, r) × [0, m) → [0, rm)` for coprime `r`, `m`. -/
theorem sum_pfa_index {β : Type*} [AddCommMonoid β] {r m : ℕ} (hcop : Nat.Coprime r m)
    (f : ℕ → β) :
    ∑ j1 ∈ range r, ∑ j2 ∈ range m, f ((m * j1 + r * j2) % (r * m)) = ∑ j ∈ range (r * m), f j := by
  rw [← Finset.sum_product' (f := fun j1 j2 => f ((m * j1 + r * j2) % (r * m)))]
  rcases Nat.eq_zero_or_pos (r * m) with h0 | hpos
  · rcases Nat.mul_eq_zero.mp h0 with h | h <;> simp [h]
  set φ : ℕ × ℕ → ℕ := fun p => (m * p.1 + r * p.2) % (r * m) with hφ
  have hmaps : Set.MapsTo φ ↑(range r ×ˢ range m) ↑(range (r * m)) := fun p _ => by
    simp only [coe_range, Set.mem_Iio, hφ]; exact Nat.mod_lt _ hpos
  have hinj : Set.InjOn φ ↑(range r ×ˢ range m) := by
    rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at ha hb
    have h' : m * a1 + r * a2 ≡ m * b1 + r * b2 [MOD r * m] := h
    have h1 : m * a1 ≡ m * b1 [MOD r] := by
      have := Nat.ModEq.of_mul_right m h'
      unfold Nat.ModEq at this ⊢
      simpa [Nat.add_mul_mod_self_left] using this
    have h2 : r * a2 ≡ r * b2 [MOD m] := by
      have := Nat.ModEq.of_mul_left r h'
      unfold Nat.ModEq at this ⊢
      rw [add_comm (m * a1), add_comm (m * b1)] at this
      simpa [Nat.add_mul_mod_self_left] using this
    have e1 := Nat.ModEq.cancel_left_of_coprime hcop h1
    have e2 := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcop) h2
    unfold Nat.ModEq at e1 e2
    rw [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at e1
    rw [Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2] at e2
    simp [e1, e2]
  have hsurj : Set.SurjOn φ ↑(range r ×ˢ range m) ↑(range (r * m)) :=
    Finset.surjOn_of_injOn_of_card_le φ hmaps hinj (by simp)
  exact Finset.sum_nbij φ (fun p hp => hmaps hp) hinj hsurj (fun _ _ => rfl)

/-- **Good–Thomas.** For coprime `r`, `m`, the DFT of size `rm` is a two-dimensional
`r × m` DFT without twiddle factors. -/
theorem dftSum_pfa (fwd : Bool) {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (hcop : Nat.Coprime r m)
    (x : ℕ → ℂ) (k : ℕ) :
    dftSum fwd (r * m) x k =
      ∑ j1 ∈ range r, twiddle fwd r (j1 * (k % r)) *
        dftSum fwd m (fun j2 => x ((m * j1 + r * j2) % (r * m))) (k % m) := by
  rw [dftSum, ← sum_pfa_index hcop]
  refine Finset.sum_congr rfl fun j1 _ => ?_
  rw [dftSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j2 _ => ?_
  have hn : 0 < r * m := Nat.mul_pos hr hm
  have t1 : twiddle fwd r (j1 * (k % r)) = twiddle fwd (r * m) (m * (j1 * k)) := by
    rw [← twiddle_mod fwd hr, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, twiddle_mod fwd hr,
      mul_comm r m, twiddle_scale fwd hm]
  have t2 : twiddle fwd m (j2 * (k % m)) = twiddle fwd (r * m) (r * (j2 * k)) := by
    rw [← twiddle_mod fwd hm, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, twiddle_mod fwd hm,
      twiddle_scale fwd hr]
  rw [t1, t2, ← mul_assoc, ← twiddle_add, ← twiddle_mod fwd hn,
    ← twiddle_mod fwd hn (m * (j1 * k) + r * (j2 * k))]
  congr 2
  rw [Nat.mod_mul_mod]
  congr 1
  ring

theorem symDFT_block (fwd : Bool) {b : ℕ} (hb : 0 < b) (x : ℕ → SC) (hx : ∀ j < b, (x j).Good m)
    {k : ℕ} (hk : k < b) :
    (symOps.get (symDFT fwd (primeFactors b) x) k).toC env = dftSum fwd b (fun j => (x j).toC env) k ∧
      (symOps.get (symDFT fwd (primeFactors b) x) k).Good m := by
  have hp := primeFactors_prod hb
  have := symDFT_spec env fwd (primeFactors b) (primeFactors_pos b) x (by rw [hp]; exact hx) k
    (by rw [hp]; exact hk)
  rwa [hp] at this

/-- **The prime factor algorithm denotes the DFT.** -/
theorem pfaDFT_spec (fwd : Bool) : ∀ (bs : List ℕ), (∀ b ∈ bs, 0 < b) → bs.Pairwise Nat.Coprime →
    ∀ (x : ℕ → SC), (∀ j < bs.prod, (x j).Good m) → ∀ k < bs.prod,
      (symOps.get (pfaDFT fwd bs x) k).toC env = dftSum fwd bs.prod (fun j => (x j).toC env) k ∧
      (symOps.get (pfaDFT fwd bs x) k).Good m
  | [], _, _, x, hx, k, hk => by
    simp only [pfaDFT]
    exact symDFT_spec env fwd [] (by simp) x hx k hk
  | [b], hpos, _, x, hx, k, hk => by
    simp only [List.prod_cons, List.prod_nil, mul_one] at hx hk ⊢
    exact symDFT_block env fwd (hpos b (by simp)) x hx hk
  | b :: c :: rest, hpos, hpw, x, hx, k, hk => by
    have hb : 0 < b := hpos b (by simp)
    have hrest : ∀ f ∈ c :: rest, 0 < f := fun f hf => hpos f (List.mem_cons_of_mem _ hf)
    have hpw' := List.pairwise_cons.mp hpw
    set M := (c :: rest).prod with hM
    have hm : 0 < M := List.prod_pos hrest
    have hcop : Nat.Coprime b M := Nat.coprime_list_prod_right_iff.mpr hpw'.1
    have hprod : (b :: c :: rest).prod = b * M := List.prod_cons
    rw [hprod] at hk hx ⊢
    have hn : 0 < b * M := Nat.mul_pos hb hm
    set ys : Array (Array SC) := (Array.range b).map fun j1 =>
      pfaDFT fwd (c :: rest) (fun j2 => x ((M * j1 + b * j2) % (b * M))) with hys
    have hsub : ∀ j1 < b, ∀ k2 < M,
        (symOps.get (ys.getD j1 #[]) k2).toC env =
          dftSum fwd M (fun j2 => (x ((M * j1 + b * j2) % (b * M))).toC env) k2 ∧
        (symOps.get (ys.getD j1 #[]) k2).Good m := by
      intro j1 hj1 k2 hk2
      have hy : ys.getD j1 #[] = pfaDFT fwd (c :: rest) (fun j2 => x ((M * j1 + b * j2) % (b * M))) := by
        simp [hys, Array.getD, hj1]
      rw [hy]
      exact pfaDFT_spec fwd (c :: rest) hrest hpw'.2 _ (fun j2 _ => hx _ (Nat.mod_lt _ hn)) k2 hk2
    have hk1 : k % M < M := Nat.mod_lt _ hm
    have hk2 : k % b < b := Nat.mod_lt _ hb
    set z : ℕ → SC := fun j1 => symOps.get (ys.getD j1 #[]) (k % M) with hz
    have hget : symOps.get (pfaDFT fwd (b :: c :: rest) x) k =
        symOps.get (symDFT fwd (primeFactors b) z) (k % b) := by
      simp only [pfaDFT, ← hM, ← hys]
      rw [show (Array.range (b * M)).map (fun k => symOps.get (((Array.range M).map fun k2 =>
          symDFT fwd (primeFactors b) fun j1 => symOps.get (ys.getD j1 #[]) k2).getD (k % M) #[])
            (k % b)) = symOps.build (b * M) _ from rfl, symOps_get_build (b * M) _ hk]
      simp [Array.getD, hk1, hz]
    obtain ⟨l1, l2⟩ := symDFT_block env fwd hb z (fun j1 hj1 => (hsub j1 hj1 (k % M) hk1).2) hk2
    refine ⟨?_, by rw [hget]; exact l2⟩
    rw [hget, l1, dftSum_pfa fwd hb hm hcop, dftSum]
    refine Finset.sum_congr rfl (fun j1 hj1 => ?_)
    rw [(hsub j1 (Finset.mem_range.mp hj1) (k % M) hk1).1]


/-! ## The generated butterfly kernels compute the DFT -/

/-- The complex value of butterfly input `r` (the input times its twiddle, if any) for
real input variables `v`. -/
noncomputable def bflyX (R : ℕ) (twiddled : Bool) (v : ℕ → ℝ) (r : ℕ) : ℂ :=
  (if twiddled && r ≥ 1 then (⟨v (2 * R + 2 * (r - 1)), v (2 * R + 2 * (r - 1) + 1)⟩ : ℂ)
    else 1) * ⟨v (2 * r), v (2 * r + 1)⟩

theorem bflyIn_spec (env : ℕ → ℝ) (R : ℕ) (twiddled : Bool) {r : ℕ} (hr : r < R) :
    (bflyIn R twiddled r).toC env = bflyX R twiddled env r ∧
      (bflyIn R twiddled r).Good (butterflyInputs R twiddled) := by
  have hval : ∀ a b, (SC.val (.input a) (.input b)).toC env = ⟨env a, env b⟩ := fun _ _ => rfl
  unfold bflyIn bflyX butterflyInputs
  by_cases ht : (twiddled && r ≥ 1) = true
  · have htw : twiddled = true := by simp_all
    have hr1 : r ≥ 1 := by simp_all
    subst htw
    simp only [ht, ite_true]
    obtain ⟨h1, h2⟩ := sc_mulGen env (m := 4 * R - 2)
      (x := .val (.input (2 * R + 2 * (r - 1))) (.input (2 * R + 2 * (r - 1) + 1)))
      (y := .val (.input (2 * r)) (.input (2 * r + 1)))
      (by simp only [SC.Good, SExpr.InputsLt]; omega) (by simp only [SC.Good, SExpr.InputsLt]; omega)
    exact ⟨by rw [h1, hval, hval], by simpa using h2⟩
  · simp only [ht, ite_false, Bool.false_eq_true, one_mul]
    refine ⟨rfl, ?_⟩
    split <;> simp only [SC.Good, SExpr.InputsLt] <;> omega

theorem dftSum_congr {fwd : Bool} {n : ℕ} {x y : ℕ → ℂ} (h : ∀ j < n, x j = y j) (k : ℕ) :
    dftSum fwd n x k = dftSum fwd n y k := by
  unfold dftSum
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

theorem bflySym_spec (env : ℕ → ℝ) (fwd : Bool) {R : ℕ} (hR : 0 < R) (twiddled : Bool)
    {k : ℕ} (hk : k < R) :
    (symOps.get (bflySym fwd R twiddled) k).toC env = dftSum fwd R (bflyX R twiddled env) k ∧
      (symOps.get (bflySym fwd R twiddled) k).Good (butterflyInputs R twiddled) := by
  have hprod := primeFactors_prod hR
  have hin : ∀ j < (primeFactors R).prod, (bflyIn R twiddled j).Good (butterflyInputs R twiddled) :=
    fun j hj => (bflyIn_spec env R twiddled (hprod ▸ hj)).2
  have hk' : k < (primeFactors R).prod := by rw [hprod]; exact hk
  unfold bflySym
  split
  · obtain ⟨h1, h2⟩ := exec_sym env fwd (primeFactors R) (primeFactors_pos R) (bflyIn R twiddled) hin k hk'
    refine ⟨?_, h2⟩
    rw [h1, exec_mkPlan_exact fwd _ (primeFactors_pos R) _ k hk', hprod]
    exact dftSum_congr (fun j hj => (bflyIn_spec env R twiddled hj).1) k
  · split
    · rename_i hok
      obtain ⟨hp, hpos, hpw⟩ := hok
      have hin' : ∀ j < (ppBlocks R).prod, (bflyIn R twiddled j).Good (butterflyInputs R twiddled) :=
        fun j hj => (bflyIn_spec env R twiddled (hp ▸ hj)).2
      obtain ⟨h1, h2⟩ := pfaDFT_spec env fwd (ppBlocks R) hpos hpw (bflyIn R twiddled) hin' k
        (by rw [hp]; exact hk)
      refine ⟨?_, h2⟩
      rw [h1, hp]
      exact dftSum_congr (fun j hj => (bflyIn_spec env R twiddled hj).1) k
    · obtain ⟨h1, h2⟩ := symDFT_spec env fwd (primeFactors R) (primeFactors_pos R) (bflyIn R twiddled) hin k hk'
      refine ⟨?_, h2⟩
      rw [h1, hprod]
      exact dftSum_congr (fun j hj => (bflyIn_spec env R twiddled hj).1) k

/-- **The generated butterfly kernels are correct.** Over exact real arithmetic, the kernel
that the C code of a radix-`R` butterfly is printed from maps the input variables `v` to the
real and imaginary parts of the length-`R` DFT (sign `fwd`) of the twiddled inputs
`bflyX R twiddled v`. -/
theorem butterflyK_correct (fwd : Bool) {R : ℕ} (hR : 0 < R) (twiddled : Bool)
    (inp : Array ℝ) (hinp : inp.size = butterflyInputs R twiddled) :
    (butterflyK fwd R twiddled).eval realArith inp =
      (Array.range (2 * R)).map fun i =>
        let y := dftSum fwd R (bflyX R twiddled fun j => inp.getD j 0) (i / 2)
        if i % 2 = 0 then y.re else y.im := by
  set env : ℕ → ℝ := fun j => inp.getD j default
  have hspec : ∀ i < 2 * R,
      (symOps.get (bflySym fwd R twiddled) (i / 2)).toC env =
        dftSum fwd R (bflyX R twiddled env) (i / 2) ∧
      (symOps.get (bflySym fwd R twiddled) (i / 2)).Good (butterflyInputs R twiddled) :=
    fun i hi => bflySym_spec env fwd hR twiddled (by omega)
  have hout : ∀ e ∈ butterfly fwd R twiddled, e.InputsLt (butterflyInputs R twiddled) := by
    intro e he
    simp only [butterfly, Array.mem_map, Array.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    obtain ⟨-, p1, p2⟩ := parts_spec env (hspec i hi).2
    split <;> exact il_contract (by assumption)
  unfold butterflyK
  rw [cse_correct realArith_comm _ hinp hout]
  apply Array.ext
  · simp [butterfly]
  · intro i h1 h2
    simp only [butterfly, Array.getElem_map, Array.getElem_range, Array.size_map,
      Array.size_range] at h1 ⊢
    obtain ⟨hs, hg⟩ := hspec i h1
    obtain ⟨p, -, -⟩ := parts_spec env hg
    rw [hs] at p
    have hre := congrArg Complex.re p
    have him := congrArg Complex.im p
    simp only [evC] at hre him
    split
    · exact (ev_contract env _).trans hre
    · exact (ev_contract env _).trans him

end Exec

end LeanFFTW.Gen
