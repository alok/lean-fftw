/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Proof.RoundError
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.MulDiv
import FloatLib.Floats.Formats.IEEE754.Native.AddSub

/-!
# Binary64 error bounds for the kernels and the Stockham schedule

Lean's `Float` operations are *defined* in Lean's logic through the logical model
`Float.Model` (Lean ≥ 4.33): `x + y = .ofModel (x.toModel + y.toModel)`, and likewise for
`-`, `*`, `-x` and `Float.fma`, each unpacking to `Float.Model.UnpackedFloat` and rounding
there. FloatLib (lean-dojo/FloatLib) proves that this model agrees with its independent
binary64 semantics: the real value of a finite result is the exact result rounded to
nearest-even on the binary64 grid (`Model.roundAt`). We read a `Float` as a real through
FloatLib (`toReal64`) and obtain the standard model for `floatArith`:

* `add`, `sub`: FloatLib's `toModel_ofFloat_add_of_isFinite` and
  `abs_toReal_add_sub_le_unitRoundoffAt` (relative error `≤ 2⁻⁵³`, no underflow term);
* `mul`: FloatLib's `toReal_ofModel_mul_toModel_eq_roundAt` and `roundAt_standardModel`
  (`|δ| ≤ 2⁻⁵³`, `|η| ≤ 2⁻¹⁰⁷⁵`);
* `fma` (and `fms = fma a b (-c)`, `fnma = fma (-a) b c`): proved here
  (`toReal_ofModel_fma_toModel_eq_roundAt`) from Lean's `UnpackedFloat.fma`, following
  FloatLib's proof for addition; one rounding of `a·b + c`;
* `neg`: exact (FloatLib's `toModel_neg_of_isFinite`, `toReal_neg`).

**Trust boundary.** The theorems are about Lean's logical `Float` semantics, which is
what `Kernel.eval floatArith` and `refTransform` denote. That compiled code (the C
operators `+ - * -x` and `fma` on `double`) implements this logical model is Lean's own
trusted assumption about its `@[extern]` floating-point primitives; nothing further is
assumed here. Constants (`Cst.toFloat`) and twiddle tables are computed by `Trig` code
whose accuracy is not proved; their accuracy enters as explicit hypotheses (`κ`, `τ`), as
does the absence of overflow (`StockhamSlotsOK … isFinite`: every intermediate value of
every butterfly is finite, which is checkable by running the transform).

Main results:
* `floatArith_stdModel`: `floatArith` satisfies `StdModel` with `u = 2⁻⁵³`, `ℓ = 2⁻¹⁰²²`;
* `Kernel.eval_float_error`: the kernel error bound over binary64;
* `stockhamWith_float_error_dft`: the schedule error bound against the exact DFT;
* `refTransform_error`: the bound for the binary64 reference transform `refTransform`.
-/

open FloatLib.Floats.Formats.BinaryInterchange

namespace LeanFFTW.Gen

open LeanFFTW

/-! ## Fused multiply-add in Lean's logical model -/

section Fma

open FloatLib.Floats.Formats.Flocq in
theorem decreaseExponent_value' (mantissa : ℕ) (exponent targetExponent : ℤ) :
    ((Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent).1 : ℝ) *
        bpow FloatLib.Numerics.binaryRadix
          (Float.Model.UnpackedFloat.decreaseExponent mantissa exponent targetExponent).2 =
      (mantissa : ℝ) * bpow FloatLib.Numerics.binaryRadix exponent := by
  by_cases hle : exponent ≤ targetExponent
  · have hshift : (exponent - targetExponent).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [Float.Model.UnpackedFloat.decreaseExponent, hshift]
  · let shift := (exponent - targetExponent).toNat
    simp only [Float.Model.UnpackedFloat.decreaseExponent]
    change ((mantissa <<< shift : ℕ) : ℝ) * bpow FloatLib.Numerics.binaryRadix
        (exponent - (shift : ℤ)) = (mantissa : ℝ) * bpow FloatLib.Numerics.binaryRadix exponent
    rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (2 : ℝ) ^ shift = bpow FloatLib.Numerics.binaryRadix (shift : ℤ) := by
      simp [bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    rw [hpow, mul_assoc, ← bpow.add_exp]
    congr 2
    omega

theorem decreaseExponent_min_left (m : ℕ) (e e' : ℤ) :
    (Float.Model.UnpackedFloat.decreaseExponent m e (min e e')).2 = min e e' := by
  unfold Float.Model.UnpackedFloat.decreaseExponent
  by_cases hle : e ≤ min e e'
  · have heq : e = min e e' := le_antisymm hle (min_le_left _ _)
    simp [← heq]
  · change e - (Int.ofNat (e - min e e').toNat) = min e e'
    have hshift : Int.ofNat (e - min e e').toNat = e - min e e' := Int.toNat_of_nonneg (by omega)
    rw [hshift]
    omega

theorem decreaseExponent_min_right (m : ℕ) (e e' : ℤ) :
    (Float.Model.UnpackedFloat.decreaseExponent m e' (min e e')).2 = min e e' := by
  rw [min_comm]; exact decreaseExponent_min_left m e' e

theorem cast_sign_apply' (sign : Float.Model.UnpackedFloat.Sign) (mantissa : ℕ) :
    ((sign.apply mantissa : ℤ) : ℝ) = (if Model.modelSignBit sign then (-1 : ℝ) else 1) * mantissa := by
  cases sign <;> simp [Float.Model.UnpackedFloat.Sign.apply, Model.modelSignBit]

theorem sign_mul_factor (s₁ s₂ : Float.Model.UnpackedFloat.Sign) :
    (if Model.modelSignBit (s₁ * s₂) then (-1 : ℝ) else 1) =
      (if Model.modelSignBit s₁ then (-1 : ℝ) else 1) *
        (if Model.modelSignBit s₂ then (-1 : ℝ) else 1) := by
  cases s₁ <;> cases s₂ <;> simp [Model.modelSignBit]

/-- **Fused multiply-add rounds once.** For a conventional IEEE descriptor, finite operands
and a finite result, Lean core's unpacked fused multiply-add of the values unpacked from three
format words is the exact `x * y + z` rounded once to nearest-even. -/
theorem toReal_ofModel_fma_toModel_eq_roundAt {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : (Model.toModel x).isFinite = true)
    (hy : (Model.toModel y).isFinite = true) (hz : (Model.toModel z).isFinite = true)
    (hfinite : Model.isFinite (Model.ofModel fmt (Float.Model.UnpackedFloat.fma
      (FloatFormat.toModel fmt) (Model.toModel x) (Model.toModel y) (Model.toModel z))) = true) :
    Model.toReal (Model.ofModel fmt (Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
        (Model.toModel x) (Model.toModel y) (Model.toModel z))) =
      Model.roundAt fmt (Model.toReal x * Model.toReal y + Model.toReal z) := by
  have hzfin : Model.isFinite z = true := by rwa [← Model.isFinite_toModel hfmt]
  -- `z` is a grid point, and repacking its unpacked value preserves its real value
  have hzgrid : Model.roundAt fmt (Model.toReal z) = Model.toReal z :=
    FloatLib.Floats.Formats.Flocq.round_preserves_generic _ _
      (Model.toReal_genericFormat_of_isFinite z hzfin)
  have hzback : Model.toReal (Model.ofModel fmt (Model.toModel z)) = Model.toReal z := by
    rw [Model.toReal_eq_unpackedToReal_toModel hfmt (Model.ofModel fmt (Model.toModel z)),
      Model.toReal_eq_unpackedToReal_toModel hfmt z]
    change Model.unpackedToReal (Model.toModel (Model.canonicalizeModel z)) = _
    rw [Model.toModel_canonicalizeModel]
  have hxr := Model.toReal_eq_unpackedToReal_toModel hfmt x
  have hyr := Model.toReal_eq_unpackedToReal_toModel hfmt y
  have hzr := Model.toReal_eq_unpackedToReal_toModel hfmt z
  obtain ⟨ux, hux⟩ : ∃ ux, Model.toModel x = ux := ⟨_, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ uy, Model.toModel y = uy := ⟨_, rfl⟩
  obtain ⟨uz, huz⟩ : ∃ uz, Model.toModel z = uz := ⟨_, rfl⟩
  rw [hux] at hx hxr
  rw [huy] at hy hyr
  rw [huz] at hz hzr hzback
  rw [hux, huy, huz] at hfinite ⊢
  rw [hxr, hyr]
  cases ux <;> cases uy <;> cases uz <;>
    simp only [Float.Model.UnpackedFloat.isFinite, Bool.false_eq_true] at hx hy hz
  -- zero · zero + zero
  case zero.zero.zero s₁ s₂ s₃ =>
    rw [hzr]
    simp only [Model.unpackedToReal_zero, mul_zero, add_zero, Model.roundAt_zero]
    simp only [Float.Model.UnpackedFloat.fma]
    split <;> exact Model.toReal_ofModel_zero fmt hfmt _
  case zero.finite.zero s₁ s₂ m₂ e₂ h₂ s₃ =>
    rw [hzr]
    simp only [Model.unpackedToReal_zero, zero_mul, add_zero, Model.roundAt_zero]
    simp only [Float.Model.UnpackedFloat.fma]
    split <;> exact Model.toReal_ofModel_zero fmt hfmt _
  case finite.zero.zero s₁ m₁ e₁ h₁ s₂ s₃ =>
    rw [hzr]
    simp only [Model.unpackedToReal_zero, mul_zero, add_zero, Model.roundAt_zero]
    simp only [Float.Model.UnpackedFloat.fma]
    split <;> exact Model.toReal_ofModel_zero fmt hfmt _
  -- a zero factor: the addend is returned
  case zero.zero.finite s₁ s₂ s₃ m₃ e₃ h₃ =>
    simp only [Model.unpackedToReal_zero, mul_zero, zero_add, hzgrid]
    exact hzback
  case zero.finite.finite s₁ s₂ m₂ e₂ h₂ s₃ m₃ e₃ h₃ =>
    simp only [Model.unpackedToReal_zero, zero_mul, zero_add, hzgrid]
    exact hzback
  case finite.zero.finite s₁ m₁ e₁ h₁ s₂ s₃ m₃ e₃ h₃ =>
    simp only [Model.unpackedToReal_zero, mul_zero, zero_add, hzgrid]
    exact hzback
  -- finite · finite + zero: one rounding of the exact product
  case finite.finite.zero s₁ m₁ e₁ h₁ s₂ m₂ e₂ h₂ s₃ =>
    rw [hzr, Model.unpackedToReal_zero, add_zero]
    change Model.toReal (Model.ofModel fmt (Float.Model.UnpackedFloat.mul
      (FloatFormat.toModel fmt) (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂))) = _
    exact Model.toReal_ofModel_mul_finite_eq_roundAt fmt hfmt s₁ s₂ m₁ m₂ e₁ e₂ h₁ h₂
      (Model.add_le_targetExponent_totalExponent_mul _ h₁ h₂
        (Model.le_targetExponent_totalExponent_of_toModel_eq_finite x hux)
        (Model.le_targetExponent_totalExponent_of_toModel_eq_finite y huy)) hfinite
  -- finite · finite + finite: exact alignment, one normalization
  case finite.finite.finite s₁ m₁ e₁ h₁ s₂ m₂ e₂ h₂ s₃ m₃ e₃ h₃ =>
    rw [hzr]
    let E := min (e₁ + e₂) e₃
    let d₁ := Float.Model.UnpackedFloat.decreaseExponent (m₁ * m₂) (e₁ + e₂) E
    let d₃ := Float.Model.UnpackedFloat.decreaseExponent m₃ e₃ E
    let M : ℤ := (s₁ * s₂).apply d₁.1 + s₃.apply d₃.1
    change Model.isFinite (Model.ofModel fmt (Float.Model.UnpackedFloat.normalize
      (FloatFormat.toModel fmt) M E .positive)) = true at hfinite
    change Model.toReal (Model.ofModel fmt (Float.Model.UnpackedFloat.normalize
      (FloatFormat.toModel fmt) M E .positive)) = _
    rw [Model.toReal_ofModel_normalize_eq_roundAt fmt hfmt M E .positive hfinite]
    congr 1
    have hd₁ := decreaseExponent_value' (m₁ * m₂) (e₁ + e₂) E
    have hd₃ := decreaseExponent_value' m₃ e₃ E
    rw [show d₁.2 = E from decreaseExponent_min_left _ _ _] at hd₁
    rw [show d₃.2 = E from decreaseExponent_min_right _ _ _] at hd₃
    simp only [M, Int.cast_add, cast_sign_apply', add_mul, Model.unpackedToReal_finite]
    rw [mul_assoc, hd₁, mul_assoc, hd₃, sign_mul_factor,
      FloatLib.Floats.Formats.Flocq.bpow.add_exp]
    push_cast
    ring

end Fma

/-! ## Lean `Float` as binary64 -/

section Binary64

/-- A Lean `Float` as a FloatLib binary64 word. -/
def toM64 (x : Float) : Model FloatFormat.binary64 := Model.ofFloatModel x.toModel

/-- The real value of a Lean `Float` (FloatLib's binary64 interpretation; NaN and infinities
denote `0`, which never matters below since all values are assumed finite). -/
noncomputable def toReal64 (x : Float) : ℝ := Model.toReal (toM64 x)

/-- The unit roundoff of binary64, `2⁻⁵³`. -/
noncomputable abbrev u64 : ℝ := Model.unitRoundoffAt FloatFormat.binary64

/-- The underflow floor of binary64: `η / u = 2⁻¹⁰⁷⁵ / 2⁻⁵³ = 2⁻¹⁰²²`. -/
noncomputable abbrev ℓ64 : ℝ :=
  Model.underflowErrorAt FloatFormat.binary64 / Model.unitRoundoffAt FloatFormat.binary64

theorem binary64_isIEEE : FloatFormat.binary64.isIEEE = true := by decide

theorem u64_eq : u64 = (2 : ℝ) ^ (-53 : ℤ) := by
  rw [u64, Model.unitRoundoffAt_eq]; norm_num [FloatFormat.binary64]

theorem ℓ64_eq : ℓ64 = (2 : ℝ) ^ (-1022 : ℤ) := by
  rw [ℓ64, Model.unitRoundoffAt_eq, Model.underflowErrorAt_eq,
    show FloatFormat.minSubnormalExponent FloatFormat.binary64 = -1074 by decide,
    ← zpow_sub₀ (by norm_num)]
  norm_num [FloatFormat.binary64]

theorem u64_pos : 0 < u64 := by rw [u64_eq]; positivity

theorem ℓ64_nonneg : 0 ≤ ℓ64 := by rw [ℓ64_eq]; positivity

theorem isFinite_eq_toM64 (x : Float) : x.isFinite = Model.isFinite (toM64 x) :=
  Model.isFinite_toModel binary64_isIEEE (toM64 x)

/-- Nearest-even rounding to binary64 satisfies the standard model with floor `ℓ64`. -/
theorem roundAt64_err (x : ℝ) :
    |Model.roundAt FloatFormat.binary64 x - x| ≤ u64 * (|x| + ℓ64) := by
  obtain ⟨δ, η, h, hδ, hη, -⟩ := Model.roundAt_standardModel FloatFormat.binary64 x
  have hu : u64 ≠ 0 := u64_pos.ne'
  have e : u64 * ℓ64 = Model.underflowErrorAt FloatFormat.binary64 := by
    rw [ℓ64]; field_simp
  rw [h, show x * (1 + δ) + η - x = x * δ + η by ring, mul_add, e]
  calc |x * δ + η| ≤ |x| * |δ| + |η| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ |x| * u64 + Model.underflowErrorAt FloatFormat.binary64 :=
        add_le_add (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)) hη
    _ = _ := by ring

theorem toM64_add {x y : Float} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toM64 (x + y) = Model.add (toM64 x) (toM64 y) :=
  FloatLib.Floats.ExecFloat.Binary.toModel_ofFloat_add_of_isFinite x y hx hy

theorem toM64_sub {x y : Float} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toM64 (x - y) = Model.sub (toM64 x) (toM64 y) :=
  FloatLib.Floats.ExecFloat.Binary.toModel_ofFloat_sub_of_isFinite x y hx hy

theorem toReal64_add {x y : Float} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x + y).isFinite = true) :
    |toReal64 (x + y) - (toReal64 x + toReal64 y)| ≤ u64 * (|toReal64 x + toReal64 y| + ℓ64) := by
  rw [isFinite_eq_toM64] at hx hy hr
  rw [toM64_add (by rwa [isFinite_eq_toM64]) (by rwa [isFinite_eq_toM64])] at hr
  have h := Model.abs_toReal_add_sub_le_unitRoundoffAt (toM64 x) (toM64 y) binary64_isIEEE hx hy hr
  rw [toReal64, toM64_add (by rwa [isFinite_eq_toM64]) (by rwa [isFinite_eq_toM64])]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ u64_pos.le)
  have := ℓ64_nonneg
  unfold toReal64
  linarith

theorem toReal64_sub {x y : Float} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x - y).isFinite = true) :
    |toReal64 (x - y) - (toReal64 x - toReal64 y)| ≤ u64 * (|toReal64 x - toReal64 y| + ℓ64) := by
  rw [isFinite_eq_toM64] at hx hy hr
  rw [toM64_sub (by rwa [isFinite_eq_toM64]) (by rwa [isFinite_eq_toM64])] at hr
  have h := Model.abs_toReal_sub_sub_le_unitRoundoffAt (toM64 x) (toM64 y) binary64_isIEEE hx hy hr
  rw [toReal64, toM64_sub (by rwa [isFinite_eq_toM64]) (by rwa [isFinite_eq_toM64])]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ u64_pos.le)
  have := ℓ64_nonneg
  unfold toReal64
  linarith

/-- Binary64 multiplication rounds the exact product once (FloatLib). -/
theorem toReal64_mul {x y : Float} (hr : (x * y).isFinite = true) :
    toReal64 (x * y) = Model.roundAt FloatFormat.binary64 (toReal64 x * toReal64 y) := by
  rw [isFinite_eq_toM64] at hr
  exact Model.toReal_ofModel_mul_toModel_eq_roundAt binary64_isIEEE (toM64 x) (toM64 y) hr

/-- Binary64 fused multiply-add rounds `x * y + z` once. -/
theorem toReal64_fma {x y z : Float} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (hr : (Float.fma x y z).isFinite = true) :
    toReal64 (Float.fma x y z) =
      Model.roundAt FloatFormat.binary64 (toReal64 x * toReal64 y + toReal64 z) := by
  rw [isFinite_eq_toM64] at hr
  exact toReal_ofModel_fma_toModel_eq_roundAt binary64_isIEEE (toM64 x) (toM64 y) (toM64 z)
    hx hy hz hr

theorem toM64_neg {x : Float} (hx : x.isFinite = true) :
    toM64 (-x) = Model.canonicalizeModel (Model.neg (toM64 x)) := by
  change Model.ofModel FloatFormat.binary64 (Float.Model.UnpackedFloat.neg (Model.toModel (toM64 x))) = _
  rw [← Model.toModel_neg_of_isFinite binary64_isIEEE (toM64 x) hx]
  rfl

theorem toReal_canonicalizeModel64 (y : Model FloatFormat.binary64) :
    Model.toReal (Model.canonicalizeModel y) = Model.toReal y := by
  rw [Model.toReal_eq_unpackedToReal_toModel binary64_isIEEE,
    Model.toReal_eq_unpackedToReal_toModel binary64_isIEEE, Model.toModel_canonicalizeModel]

theorem isFinite_canonicalizeModel64 (y : Model FloatFormat.binary64) :
    Model.isFinite (Model.canonicalizeModel y) = Model.isFinite y := by
  rw [← Model.isFinite_toModel binary64_isIEEE, ← Model.isFinite_toModel binary64_isIEEE,
    Model.toModel_canonicalizeModel]

theorem isFinite_neg64 {x : Float} (hx : x.isFinite = true) : (-x).isFinite = true := by
  rw [isFinite_eq_toM64, toM64_neg hx, isFinite_canonicalizeModel64, Model.isFinite_neg,
    ← isFinite_eq_toM64, hx]

theorem toReal64_neg {x : Float} (hx : x.isFinite = true) : toReal64 (-x) = -toReal64 x := by
  rw [toReal64, toM64_neg hx, toReal_canonicalizeModel64, Model.toReal_neg]
  · rfl
  · rwa [← isFinite_eq_toM64]

theorem toReal64_zero : toReal64 0.0 = 0 := by
  have h : (0.0 : Float).toModel = Float.Model.pack (.zero .positive) := by decide
  rw [toReal64, toM64, h]
  exact Model.toReal_ofModel_zero FloatFormat.binary64 binary64_isIEEE _

theorem toReal64_default : toReal64 default = 0 := by
  have h : (default : Float).toModel = Float.Model.pack (.zero .positive) := by decide
  rw [toReal64, toM64, h]
  exact Model.toReal_ofModel_zero FloatFormat.binary64 binary64_isIEEE _

theorem isFinite_default : (default : Float).isFinite = true := by decide

/-- A rounded value satisfies the standard model. -/
theorem round_step {r x : ℝ} (h : r = Model.roundAt FloatFormat.binary64 x) :
    |r - x| ≤ u64 * (|x| + ℓ64) := h ▸ roundAt64_err x

/-- **Lean's binary64 arithmetic satisfies the standard model** with `u = 2⁻⁵³` and
`ℓ = 2⁻¹⁰²²`, for every finite evaluation, given the accuracy `κ` of the constants. -/
theorem floatArith_stdModel (κ : ℝ)
    (hcst : ∀ c : Cst, c.toFloat.isFinite = true →
      |toReal64 c.toFloat - c.toReal| ≤ κ * (|c.toReal| + ℓ64)) :
    StdModel floatArith toReal64 (fun x => x.isFinite = true) u64 κ ℓ64 where
  add a b ha hb hr := toReal64_add ha hb hr
  sub a b ha hb hr := toReal64_sub ha hb hr
  mul a b _ _ hr := round_step (toReal64_mul hr)
  neg a ha _ := toReal64_neg ha
  fma a b c ha hb hc hr := round_step (toReal64_fma ha hb hc hr)
  fms a b c ha hb hc hr := by
    have h := toReal64_fma ha hb (isFinite_neg64 hc) hr
    rw [toReal64_neg hc, ← sub_eq_add_neg] at h
    exact round_step h
  fnma a b c ha hb hc hr := by
    have h := toReal64_fma (isFinite_neg64 ha) hb hc hr
    rw [toReal64_neg ha, show -toReal64 a * toReal64 b + toReal64 c =
      toReal64 c - toReal64 a * toReal64 b by ring] at h
    exact round_step h
  zero := toReal64_zero
  cst c hc := hcst c hc

end Binary64

/-! ## Binary64 error bounds -/

section Final

/-- **Kernel error bound over binary64.** For a kernel evaluated in Lean `Float` on inputs
`x̃` approximating real inputs `x` (`|x̃ᵢ - xᵢ| ≤ φᵢ mᵢ`, `|xᵢ| ≤ mᵢ`), with no intermediate
overflow, every output satisfies
`|x̃ₒ' - yₒ| ≤ (k.eval (errArith 2⁻⁵³ κ) φ)ₒ · (k.eval (magArith 2⁻¹⁰²²) m)ₒ`,
where `y = k.eval realArith x` is the exact result and `κ` bounds the constants' error. -/
theorem Kernel.eval_float_error (κ : ℝ) (hκ : 0 ≤ κ)
    (hcst : ∀ c : Cst, c.toFloat.isFinite = true →
      |toReal64 c.toFloat - c.toReal| ≤ κ * (|c.toReal| + ℓ64))
    (k : Kernel) (inp : Array Float) (x m φ : Array ℝ)
    (hx : x.size = inp.size) (hm : m.size = inp.size) (hφ : φ.size = inp.size)
    (hφ0 : ∀ i, 0 ≤ φ.getD i 0) (hxm : ∀ i, |x.getD i 0| ≤ m.getD i 0)
    (hin : ∀ i, |toReal64 (inp.getD i default) - x.getD i 0| ≤ φ.getD i 0 * m.getD i 0)
    (hfin : ∀ i, ((k.slots floatArith inp).getD i default).isFinite = true) (o : ℕ) :
    |toReal64 ((k.eval floatArith inp).getD o default) - (k.eval realArith x).getD o 0| ≤
      (k.eval (errArith u64 κ) φ).getD o 0 * (k.eval (magArith ℓ64) m).getD o 0 :=
  Kernel.eval_error (floatArith_stdModel κ hcst) u64_pos.le hκ ℓ64_nonneg toReal64_default k
    inp x m φ hx hm hφ hφ0 hxm hin hfin o

/-- **Kernel error bound over binary64, closed form**: with every input factor `φᵢ ∈ [0, t]`
and `κ ≤ t`, the error of output `o` is at most `((1+2⁻⁵³)^n (1+t)^p - 1) · Mₒ`, where
`(n, p)` are the rounding depth and input degree of `o` (`depthArith`). -/
theorem Kernel.eval_float_error_depth (κ t : ℝ) (hκ : 0 ≤ κ) (ht : 0 ≤ t) (hκt : κ ≤ t)
    (hcst : ∀ c : Cst, c.toFloat.isFinite = true →
      |toReal64 c.toFloat - c.toReal| ≤ κ * (|c.toReal| + ℓ64))
    (k : Kernel) (inp : Array Float) (x m φ : Array ℝ)
    (hx : x.size = inp.size) (hm : m.size = inp.size) (hφ : φ.size = inp.size)
    (hφt : ∀ i, 0 ≤ φ.getD i 0 ∧ φ.getD i 0 ≤ t) (hxm : ∀ i, |x.getD i 0| ≤ m.getD i 0)
    (hin : ∀ i, |toReal64 (inp.getD i default) - x.getD i 0| ≤ φ.getD i 0 * m.getD i 0)
    (hfin : ∀ i, ((k.slots floatArith inp).getD i default).isFinite = true) (o : ℕ) :
    |toReal64 ((k.eval floatArith inp).getD o default) - (k.eval realArith x).getD o 0| ≤
      ((1 + u64) ^ ((k.eval depthArith (φ.map fun _ => (0, 1))).getD o default).1 *
        (1 + t) ^ ((k.eval depthArith (φ.map fun _ => (0, 1))).getD o default).2 - 1) *
        (k.eval (magArith ℓ64) m).getD o 0 :=
  Kernel.eval_error_depth (floatArith_stdModel κ hcst) u64_pos.le hκ ℓ64_nonneg toReal64_default
    ht hκt k inp x m φ hx hm hφ hφt hxm hin hfin o

/-- **Stockham schedule error bound over binary64, against the exact DFT.** -/
theorem stockhamWith_float_error_dft (κ τ : ℝ) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hcst : ∀ c : Cst, c.toFloat.isFinite = true →
      |toReal64 c.toFloat - c.toReal| ≤ κ * (|c.toReal| + ℓ64))
    (fwd : Bool) (rs : Array ℕ) (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ) (hN : N = rs.toList.prod)
    (twC : ℕ → Array Float)
    (htwsz : ∀ t, (exactTwOf fwd N rs t).size = (twC t).size)
    (htw : ∀ t i, |toReal64 ((twC t).getD i default) - (exactTwOf fwd N rs t).getD i 0| ≤ τ)
    (zC : Array Float) (z m φ : Array ℝ) (hzN : zC.size = 2 * N)
    (hz : z.size = zC.size) (hm : m.size = zC.size) (hφ : φ.size = zC.size)
    (hφ0 : ∀ i, 0 ≤ φ.getD i 0) (hzm : ∀ i, |z.getD i 0| ≤ m.getD i 0)
    (hin : ∀ i, |toReal64 (zC.getD i default) - z.getD i 0| ≤ φ.getD i 0 * m.getD i 0)
    (hfin : StockhamSlotsOK floatArith (fun x => x.isFinite = true) fwd N rs twC zC)
    (i : ℕ) (hi : i < 2 * N) :
    |toReal64 ((stockhamWith floatArith fwd N rs twC zC).getD i default) -
        (let y := dftSum fwd N (fun j => ⟨z.getD (2 * j) 0, z.getD (2 * j + 1) 0⟩) (i / 2)
         if i % 2 = 0 then y.re else y.im)| ≤
      (stockhamWith (errArith u64 κ) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => τ) φ).getD i 0 *
        (stockhamWith (magArith ℓ64) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => 1) m).getD i 0 :=
  stockhamWith_error_dft (floatArith_stdModel κ hcst) u64_pos.le hκ ℓ64_nonneg toReal64_default
    isFinite_default fwd rs hrs N hN twC τ hτ htwsz htw zC z m φ hzN hz hm hφ hφ0 hzm hin hfin i hi

/-! ### The binary64 reference transform -/

/-- The binary64 twiddle tables of `refTransform`. -/
def refTwOf (fwd : Bool) (N : ℕ) (rs : Array ℕ) (t : ℕ) : Array Float :=
  (passTwiddles (Trig.cosSin2PiTable N) fwd N (rs.getD t 1) (passNs rs t)).data

theorem refTransform_data (fwd : Bool) (N : ℕ) (rs : Array ℕ) (inp : FloatArray) :
    (refTransform fwd N rs inp).data = stockhamWith floatArith fwd N rs (refTwOf fwd N rs) inp.data :=
  rfl

theorem floatArray_size_push' (t : FloatArray) (x : Float) : (t.push x).size = t.size + 1 := by
  cases t; simp [FloatArray.push, FloatArray.size]

theorem floatArray_foldl_push_size {β : Type} (f : β → Float) (l : List β) (t : FloatArray) :
    (l.foldl (fun b a => b.push (f a)) t).size = t.size + l.length := by
  induction l generalizing t with
  | nil => simp
  | cons a l ih => simp [ih, floatArray_size_push']; omega

theorem floatArray_foldl_push2_size (F G : ℕ → ℕ → Float) (L l : List ℕ) (t : FloatArray) :
    (l.foldl (fun b a => List.foldl (fun b a_1 => b.push (G a a_1))
      (List.foldl (fun b a_1 => b.push (F a a_1)) b L) L) t).size =
      t.size + l.length * (2 * L.length) := by
  induction l generalizing t with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, floatArray_foldl_push_size, floatArray_foldl_push_size]
    ring

theorem passTwiddles_size (tab : Array (Float × Float)) (fwd : Bool) (N R ns : ℕ) :
    (passTwiddles tab fwd N R ns).size = 2 * (R - 1) * ns := by
  simp only [passTwiddles, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Id.run, pure_bind]
  rw [show ∀ x : FloatArray, (pure x : Id FloatArray) = x from fun _ => rfl,
    floatArray_foldl_push2_size]
  simp [Std.Legacy.Range.size, FloatArray.size, FloatArray.emptyWithCapacity]
  ring

theorem refTwOf_size (fwd : Bool) (N : ℕ) (rs : Array ℕ) (t : ℕ) :
    (exactTwOf fwd N rs t).size = (refTwOf fwd N rs t).size := by
  have h := passTwiddles_size (Trig.cosSin2PiTable N) fwd N (rs.getD t 1) (passNs rs t)
  simp only [FloatArray.size] at h
  simp only [exactTwOf, exactTw, Array.size_map, Array.size_range, refTwOf, h]

/-- **Error bound for the binary64 reference transform.** `refTransform fwd N rs inp` (the
transform the generated C code is tested bit-identical against) is within `Φᵢ · Mᵢ` of the
exact DFT of its input values at every entry `i < 2N`, where `Φ` is the schedule run over
`errArith 2⁻⁵³ κ` from zero input factors with twiddle factors `τ`, and `M` the schedule run
over `magArith 2⁻¹⁰²²` from the input magnitudes with twiddle magnitudes `1`. Hypotheses:
the constants have error `≤ κ·(|c| + 2⁻¹⁰²²)`, the binary64 twiddle tables have entrywise
error `≤ τ`, and no intermediate value overflows. -/
theorem refTransform_error (fwd : Bool) (rs : Array ℕ) (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ)
    (hN : N = rs.toList.prod) (inp : FloatArray) (hinp : inp.size = 2 * N) (κ τ : ℝ)
    (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hcst : ∀ c : Cst, c.toFloat.isFinite = true →
      |toReal64 c.toFloat - c.toReal| ≤ κ * (|c.toReal| + ℓ64))
    (htw : ∀ t i, |toReal64 ((refTwOf fwd N rs t).getD i default) -
      (exactTwOf fwd N rs t).getD i 0| ≤ τ)
    (hfin : StockhamSlotsOK floatArith (fun x => x.isFinite = true) fwd N rs (refTwOf fwd N rs)
      inp.data)
    (i : ℕ) (hi : i < 2 * N) :
    |toReal64 ((refTransform fwd N rs inp).data.getD i default) -
        (let y := dftSum fwd N (fun j => ⟨toReal64 (inp.data.getD (2 * j) default),
            toReal64 (inp.data.getD (2 * j + 1) default)⟩) (i / 2)
         if i % 2 = 0 then y.re else y.im)| ≤
      (stockhamWith (errArith u64 κ) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => τ) (inp.data.map fun _ => 0)).getD i 0 *
        (stockhamWith (magArith ℓ64) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => 1)
          (inp.data.map fun x => |toReal64 x|)).getD i 0 := by
  have hz : ∀ j, (inp.data.map toReal64).getD j 0 = toReal64 (inp.data.getD j default) :=
    getD_map_of toReal64_default _
  have hm : ∀ j, (inp.data.map fun x => |toReal64 x|).getD j 0 =
      |toReal64 (inp.data.getD j default)| :=
    getD_map_of (by simp [toReal64_default]) _
  have hφ : ∀ j, (inp.data.map fun _ => (0 : ℝ)).getD j 0 = 0 :=
    fun j => getD_map_of (f := fun _ : Float => (0 : ℝ)) (d := default) rfl _ j
  have h := stockhamWith_float_error_dft κ τ hκ hτ hcst fwd rs hrs N hN (refTwOf fwd N rs)
    (refTwOf_size fwd N rs) htw inp.data (inp.data.map toReal64)
    (inp.data.map fun x => |toReal64 x|) (inp.data.map fun _ => 0) hinp (by simp) (by simp)
    (by simp) (fun j => by rw [hφ]) (fun j => by rw [hz, hm])
    (fun j => by rw [hz, hφ]; simp) hfin i hi
  simp only [hz] at h
  rw [refTransform_data]
  exact h

/-- **Error bound for the binary64 reference transform, closed form.** Under the hypotheses
of `refTransform_error`, with `t = max τ κ`, every entry `i < 2N` satisfies
`|refTransformᵢ - DFTᵢ| ≤ ((1 + 2⁻⁵³)^n (1 + t)^p - 1) · Mᵢ`, where `(n, p)` is entry `i` of
the schedule run over `depthArith` (the rounding depth and the degree in the inputs, twiddles
and constants) and `M` the magnitude bound of `refTransform_error`. -/
theorem refTransform_error_depth (fwd : Bool) (rs : Array ℕ) (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ)
    (hN : N = rs.toList.prod) (inp : FloatArray) (hinp : inp.size = 2 * N) (κ τ : ℝ)
    (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hcst : ∀ c : Cst, c.toFloat.isFinite = true →
      |toReal64 c.toFloat - c.toReal| ≤ κ * (|c.toReal| + ℓ64))
    (htw : ∀ t i, |toReal64 ((refTwOf fwd N rs t).getD i default) -
      (exactTwOf fwd N rs t).getD i 0| ≤ τ)
    (hfin : StockhamSlotsOK floatArith (fun x => x.isFinite = true) fwd N rs (refTwOf fwd N rs)
      inp.data)
    (i : ℕ) (hi : i < 2 * N) :
    |toReal64 ((refTransform fwd N rs inp).data.getD i default) -
        (let y := dftSum fwd N (fun j => ⟨toReal64 (inp.data.getD (2 * j) default),
            toReal64 (inp.data.getD (2 * j + 1) default)⟩) (i / 2)
         if i % 2 = 0 then y.re else y.im)| ≤
      ((1 + u64) ^ ((stockhamWith depthArith fwd N rs
            (fun t => (exactTwOf fwd N rs t).map fun _ => (0, 1))
            (inp.data.map fun _ => (0, 1))).getD i default).1 *
          (1 + max τ κ) ^ ((stockhamWith depthArith fwd N rs
            (fun t => (exactTwOf fwd N rs t).map fun _ => (0, 1))
            (inp.data.map fun _ => (0, 1))).getD i default).2 - 1) *
        (stockhamWith (magArith ℓ64) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => 1)
          (inp.data.map fun x => |toReal64 x|)).getD i 0 := by
  have h := refTransform_error fwd rs hrs N hN inp hinp κ τ hκ hτ hcst htw hfin i hi
  have hφ : ∀ j, 0 ≤ (inp.data.map fun _ => (0 : ℝ)).getD j 0 ∧
      (inp.data.map fun _ => (0 : ℝ)).getD j 0 ≤ max τ κ := by
    intro j
    rw [getD_map_of (f := fun _ : Float => (0 : ℝ)) (d := default) rfl]
    exact ⟨le_rfl, le_max_of_le_left hτ⟩
  have hd := stockhamWith_errArith_le_depth u64_pos.le (le_max_of_le_left hτ) hκ
    (le_max_right _ _) hτ (le_max_left _ _) fwd N rs (exactTwOf fwd N rs) _ hφ i
  have e : ((inp.data.map fun _ => (0 : ℝ)).map fun _ => ((0, 1) : ℕ × ℕ)) =
      inp.data.map fun _ => ((0, 1) : ℕ × ℕ) := by
    rw [Array.map_map]; rfl
  rw [e] at hd
  have hM := stockhamWith_magArith_nonneg ℓ64_nonneg fwd N rs
    (fun t => (exactTwOf fwd N rs t).map fun _ => 1)
    (fun t i => getD_map_const_nonneg _ zero_le_one i) (inp.data.map fun x => |toReal64 x|)
    (fun j => by
      rw [getD_map_of (f := fun x : Float => |toReal64 x|) (d := default)
        (by simp [toReal64_default])]
      exact abs_nonneg _) i
  exact h.trans (mul_le_mul_of_nonneg_right hd hM)

end Final

end LeanFFTW.Gen
