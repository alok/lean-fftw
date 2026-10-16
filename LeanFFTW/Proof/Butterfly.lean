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
  · apply Complex.ext <;> simp [evC, ev_mkFmaSub, ev_mkFmaAdd, Cst.toReal] <;> ring
  · have hle : 4 * k ≤ n := by omega
    have hθ : 2 * Real.pi * ((n - 4 * k : ℕ) : ℝ) / ((4 * n : ℕ) : ℝ) =
        Real.pi / 2 - 2 * Real.pi * k / n := by
      push_cast [Nat.cast_sub hle]
      field_simp; ring
    apply Complex.ext <;>
      simp only [evC, ev_mkFmaSub, ev_mkFmaAdd, Cst.toReal, hθ, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub] <;> ring

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

theorem il_rotQ (k n : ℕ) {a b : SExpr} (ha : a.InputsLt m) (hb : b.InputsLt m) :
    (SC.rotQ k n a b).1.InputsLt m ∧ (SC.rotQ k n a b).2.InputsLt m := by
  unfold SC.rotQ
  split; · exact ⟨ha, hb⟩
  split; · exact ⟨il_mkMulC _ (il_mkSub ha hb), il_mkMulC _ (il_mkAdd ha hb)⟩
  split
  · exact ⟨il_mkFmaSub _ _ ha hb, il_mkFmaAdd _ _ hb ha⟩
  · exact ⟨il_mkFmaSub _ _ ha hb, il_mkFmaAdd _ _ hb ha⟩

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
  obtain ⟨h1, h2⟩ := exec_sym env fwd (primeFactors R) (primeFactors_pos R) (bflyIn R twiddled)
    (fun j hj => (bflyIn_spec env R twiddled (hprod ▸ hj)).2) k (by rw [hprod]; exact hk)
  refine ⟨?_, h2⟩
  unfold bflySym
  rw [h1, exec_mkPlan_exact fwd _ (primeFactors_pos R) _ k (by rw [hprod]; exact hk), hprod]
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
    split <;> assumption
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
    · exact hre
    · exact him

end Exec

end LeanFFTW.Gen
