/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Proof.Stockham

/-!
# Forward error analysis of kernels and Stockham schedules (abstract rounding model)

This file proves forward error bounds for straight-line kernels (`Kernel.eval`) and for the
whole Stockham schedule (`stockhamWith`), for **any** arithmetic `A : Arith α` with a real
interpretation `v : α → ℝ` that satisfies the *standard model with an underflow floor*
(`StdModel`): every rounded operation (`add`, `sub`, `mul`, `fma`, `fms`, `fnma`) returns
`r` with

`|v r - x| ≤ u * (|x| + λ)`,  `x` = the exact result on the interpreted operands,

whenever the operands and the result are "finite" (a predicate `fin`); negation is exact and
constants have error at most `κ * (|c| + λ)`. (`λ = η/u` turns an absolute underflow
allowance `η` into a floor on the magnitudes; for binary64, `u = 2⁻⁵³` and `λ = 2⁻¹⁰²²`.)

The bounds are expressed by two auxiliary arithmetics evaluated on the same kernel:
* `magArith λ`: the *magnitude kernel*, every operation replaced by its absolute-value
  version (`a ± b ↦ a + b`, `a * b ↦ a * b`, `a * b ± c ↦ a * b + c`, `-a ↦ a`,
  `c ↦ |c|`), plus `λ` at every rounding;
* `errArith u κ`: the *relative error factors* `φ`, with `1 + φ` multiplied by `1 + u` at
  every rounding (`(1+u)(1+φa)(1+φb) - 1` for a product, `(1+u)·max(1+φa, 1+φb) - 1` for a
  sum).

Main results:
* `Kernel.eval_error`: for inputs `x̃` approximating exact inputs `x` with
  `|v x̃ᵢ - xᵢ| ≤ φᵢ·mᵢ`, `|xᵢ| ≤ mᵢ`, every output satisfies
  `|v (k.eval A x̃)ₒ - (k.eval realArith x)ₒ| ≤ (k.eval errArith φ)ₒ · (k.eval magArith m)ₒ`;
* `Kernel.eval_error_depth`: the closed form `(k.eval errArith φ)ₒ ≤ (1+u)^nₒ (1+t)^pₒ - 1`
  where `(nₒ, pₒ) = (k.eval depthArith _)ₒ` are the rounding depth and the input degree;
* `stockhamWith_error`: the same bound through all passes of a Stockham schedule, with
  twiddle tables having entrywise error `≤ τ`;
* `stockhamWith_error_dft`: with exact twiddles `exactTwOf`, the exact side is the DFT
  (`stockhamWith_exact`).

The proofs run every arithmetic at once on a product arithmetic (`Arith.prod`) and carry a
pointwise invariant (`ErrInv`); naturality lemmas (`stockhamWith_map`) project the product
run back onto its components.
-/

open Finset

namespace LeanFFTW.Gen

open LeanFFTW

/-! ## Arrays -/

section Arrays

variable {α β : Type}

theorem getD_push_gt (a : Array α) (x d : α) {i : ℕ} (h : a.size < i) :
    (a.push x).getD i d = d := by
  simp [Array.getD, show ¬ i < a.size + 1 by omega]

/-- A pointwise property of `a.push x` from properties of `a`, `x` and the default. -/
theorem getD_push_rec {Q : α → Prop} (a : Array α) (x d : α) (ha : ∀ i, Q (a.getD i d))
    (hx : Q x) (hd : Q d) (i : ℕ) : Q ((a.push x).getD i d) := by
  rcases lt_trichotomy i a.size with h | h | h
  · rw [getD_push_lt _ _ _ h]; exact ha i
  · subst h; rw [getD_push_eq]; exact hx
  · rw [getD_push_gt _ _ _ h]; exact hd

theorem getD_ge {a : Array α} {d : α} {i : ℕ} (h : ¬ i < a.size) : a.getD i d = d := by
  simp [Array.getD, h]

theorem getD_map_of {f : α → β} {d : α} {e : β} (hf : f d = e) (a : Array α) (i : ℕ) :
    (a.map f).getD i e = f (a.getD i d) := by
  by_cases h : i < a.size
  · simp [Array.getD, h]
  · simp [Array.getD, h, hf]

/-- The array of pairs of two arrays (of the length of the first). -/
def pairArr [Inhabited α] [Inhabited β] (a : Array α) (b : Array β) : Array (α × β) :=
  (Array.range a.size).map fun i => (a.getD i default, b.getD i default)

theorem pairArr_map_fst [Inhabited α] [Inhabited β] (a : Array α) (b : Array β) :
    (pairArr a b).map Prod.fst = a := by
  apply Array.ext
  · simp [pairArr]
  · intro i h1 h2
    simp [pairArr, Array.getD, h2]

theorem pairArr_map_snd [Inhabited α] [Inhabited β] (a : Array α) (b : Array β)
    (h : b.size = a.size) : (pairArr a b).map Prod.snd = b := by
  apply Array.ext
  · simp [pairArr, h]
  · intro i h1 h2
    simp [pairArr, Array.getD, h2]

theorem pairArr_size [Inhabited α] [Inhabited β] (a : Array α) (b : Array β) :
    (pairArr a b).size = a.size := by simp [pairArr]

theorem pairArr_getD [Inhabited α] [Inhabited β] (a : Array α) (b : Array β)
    (h : b.size = a.size) (i : ℕ) :
    (pairArr a b).getD i default = (a.getD i default, b.getD i default) := by
  by_cases hi : i < a.size
  · simp [pairArr, Array.getD, hi]
  · simp [pairArr, Array.getD, hi, h]
    rfl

end Arrays

/-! ## Products of arithmetics and naturality -/

section Naturality

variable {α β γ : Type}

/-- Two arithmetics run side by side. -/
def Arith.prod (A : Arith α) (B : Arith β) : Arith (α × β) where
  cst c := (A.cst c, B.cst c)
  zero := (A.zero, B.zero)
  add a b := (A.add a.1 b.1, B.add a.2 b.2)
  sub a b := (A.sub a.1 b.1, B.sub a.2 b.2)
  mul a b := (A.mul a.1 b.1, B.mul a.2 b.2)
  neg a := (A.neg a.1, B.neg a.2)
  fma a b c := (A.fma a.1 b.1 c.1, B.fma a.2 b.2 c.2)
  fms a b c := (A.fms a.1 b.1 c.1, B.fms a.2 b.2 c.2)
  fnma a b c := (A.fnma a.1 b.1 c.1, B.fnma a.2 b.2 c.2)

/-- `f` commutes with every kernel operation. -/
def Arith.IsHom (A : Arith α) (B : Arith β) (f : α → β) : Prop :=
  ∀ (op : KOp) (g : ℕ → α), op.eval B (fun i => f (g i)) = f (op.eval A g)

theorem Arith.isHom_fst (A : Arith α) (B : Arith β) : (A.prod B).IsHom A Prod.fst := by
  intro op g; cases op <;> rfl

theorem Arith.isHom_snd (A : Arith α) (B : Arith β) : (A.prod B).IsHom B Prod.snd := by
  intro op g; cases op <;> rfl

theorem Arith.IsHom.comp {A : Arith α} {B : Arith β} {C : Arith γ} {f : α → β} {g : β → γ}
    (hf : A.IsHom B f) (hg : B.IsHom C g) : A.IsHom C (g ∘ f) := by
  intro op h
  simp only [Function.comp]
  rw [hg op (fun i => f (h i)), hf]

theorem foldl_push2_map (f : α → β) (F G : ℕ → α) (l : List ℕ) (acc : Array α) :
    l.foldl (fun acc r => (acc.push (f (F r))).push (f (G r))) (acc.map f) =
      (l.foldl (fun acc r => (acc.push (F r)).push (G r)) acc).map f := by
  induction l generalizing acc with
  | nil => rfl
  | cons r l ih =>
    simp only [List.foldl_cons]
    rw [← ih, Array.map_push, Array.map_push]

variable [Inhabited α] [Inhabited β]

theorem Kernel.slots_eq_slotsL (A : Arith α) (k : Kernel) (inp : Array α) :
    k.slots A inp = slotsL A inp k.ops.toList := by
  simp [Kernel.slots, slotsL, Array.foldl_toList]

theorem slotsL_map {A : Arith α} {B : Arith β} {f : α → β} (hf0 : f default = default)
    (hf : A.IsHom B f) : ∀ (l : List KOp) (env : Array α),
      slotsL B (env.map f) l = (slotsL A env l).map f
  | [], env => rfl
  | op :: l, env => by
    show slotsL B ((env.map f).push (op.eval B fun i => (env.map f).getD i default)) l =
      (slotsL A (env.push (op.eval A fun i => env.getD i default)) l).map f
    rw [← slotsL_map hf0 hf l, Array.map_push, ← hf]
    simp only [getD_map_of hf0]

theorem Kernel.slots_map {A : Arith α} {B : Arith β} {f : α → β} (hf0 : f default = default)
    (hf : A.IsHom B f) (k : Kernel) (inp : Array α) :
    k.slots B (inp.map f) = (k.slots A inp).map f := by
  rw [Kernel.slots_eq_slotsL, Kernel.slots_eq_slotsL, slotsL_map hf0 hf]

theorem Kernel.eval_map {A : Arith α} {B : Arith β} {f : α → β} (hf0 : f default = default)
    (hf : A.IsHom B f) (k : Kernel) (inp : Array α) :
    k.eval B (inp.map f) = (k.eval A inp).map f := by
  simp only [Kernel.eval, Kernel.slots_map hf0 hf, Array.map_map]
  congr 1
  funext o
  simp [getD_map_of hf0]

theorem bflyInputs_map {f : α → β} (hf0 : f default = default) (R ns N : ℕ)
    (tw : Option (Array α)) (z : Array α) (j : ℕ) :
    bflyInputs R ns N (tw.map (Array.map f)) (z.map f) j =
      (bflyInputs R ns N tw z j).map f := by
  have hxs := foldl_push2_map f (fun r => z.getD (2 * (j + r * (N / R))) default)
    (fun r => z.getD (2 * (j + r * (N / R)) + 1) default) (List.range R) #[]
  simp only [Array.map_empty] at hxs
  cases tw with
  | none =>
    simp only [bflyInputs, Option.map_none]
    rw [← hxs]
    simp only [getD_map_of hf0]
  | some t =>
    simp only [bflyInputs, Option.map_some]
    rw [← foldl_push2_map, ← hxs]
    simp only [getD_map_of hf0]

theorem passWith_map {A : Arith α} {B : Arith β} {f : α → β} (hf0 : f default = default)
    (hf : A.IsHom B f) (k : Kernel) (R ns N : ℕ) (tw : Option (Array α)) (z : Array α) :
    passWith B k R ns N (tw.map (Array.map f)) (z.map f) = (passWith A k R ns N tw z).map f := by
  simp only [passWith, bflyInputs_map hf0, Kernel.eval_map hf0 hf, Array.map_map]
  congr 1
  funext i
  simp only [Function.comp]
  have h1 : ∀ (a : Array (Array α)) (j : ℕ),
      (a.map (Array.map f)).getD j #[] = (a.getD j #[]).map f :=
    fun a j => getD_map_of (f := Array.map f) (d := #[]) (e := #[]) (by simp) a j
  rw [show ((Array.range (N / R)).map fun j => (k.eval A (bflyInputs R ns N tw z j)).map f) =
      ((Array.range (N / R)).map fun j => k.eval A (bflyInputs R ns N tw z j)).map
        (Array.map f) by simp [Array.map_map, Function.comp_def], h1, getD_map_of hf0]

/-- The arrays before pass `t` of the schedule. -/
def stockhamPre {δ : Type} [Inhabited δ] (A : Arith δ) (fwd : Bool) (N : ℕ) (rs : Array ℕ)
    (twOf : ℕ → Array δ) (z : Array δ) (t : ℕ) : Array δ :=
  (List.range t).foldl (fun z t => passWith A (butterflyK fwd (rs.getD t 1) (t ≥ 1))
    (rs.getD t 1) (passNs rs t) N (if t ≥ 1 then some (twOf t) else none) z) z

theorem stockhamWith_eq_pre {δ : Type} [Inhabited δ] (A : Arith δ) (fwd : Bool) (N : ℕ)
    (rs : Array ℕ) (twOf : ℕ → Array δ) (z : Array δ) :
    stockhamWith A fwd N rs twOf z = stockhamPre A fwd N rs twOf z rs.size :=
  stockhamWith_eq_foldl A fwd N rs twOf z

theorem stockhamPre_succ {δ : Type} [Inhabited δ] (A : Arith δ) (fwd : Bool) (N : ℕ)
    (rs : Array ℕ) (twOf : ℕ → Array δ) (z : Array δ) (t : ℕ) :
    stockhamPre A fwd N rs twOf z (t + 1) =
      passWith A (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1) (passNs rs t) N
        (if t ≥ 1 then some (twOf t) else none) (stockhamPre A fwd N rs twOf z t) := by
  simp only [stockhamPre, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem stockhamPre_map {A : Arith α} {B : Arith β} {f : α → β} (hf0 : f default = default)
    (hf : A.IsHom B f) (fwd : Bool) (N : ℕ) (rs : Array ℕ) (twOf : ℕ → Array α)
    (z : Array α) (t : ℕ) :
    stockhamPre B fwd N rs (fun t => (twOf t).map f) (z.map f) t =
      (stockhamPre A fwd N rs twOf z t).map f := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [stockhamPre_succ, stockhamPre_succ, ih, ← passWith_map hf0 hf]
    congr 1
    split <;> rfl

theorem stockhamWith_map {A : Arith α} {B : Arith β} {f : α → β} (hf0 : f default = default)
    (hf : A.IsHom B f) (fwd : Bool) (N : ℕ) (rs : Array ℕ) (twOf : ℕ → Array α)
    (z : Array α) :
    stockhamWith B fwd N rs (fun t => (twOf t).map f) (z.map f) =
      (stockhamWith A fwd N rs twOf z).map f := by
  rw [stockhamWith_eq_pre, stockhamWith_eq_pre, stockhamPre_map hf0 hf]

end Naturality

/-! ## Pointwise invariants -/

section Invariants

variable {γ : Type} [Inhabited γ] (C : Arith γ) (P Q : γ → Prop)

/-- Every operation preserves `Q`, when its operands and its result satisfy `P`. -/
def Arith.Preserves : Prop :=
  ∀ (op : KOp) (g : ℕ → γ), (∀ j, P (g j)) → (∀ j, Q (g j)) → P (op.eval C g) → Q (op.eval C g)

variable {C P Q}

theorem slotsL_inv (hP0 : P default) (hQ0 : Q default) (hC : C.Preserves P Q) :
    ∀ (l : List KOp) (env : Array γ), (∀ i, Q (env.getD i default)) →
      (∀ i, P ((slotsL C env l).getD i default)) → ∀ i, Q ((slotsL C env l).getD i default)
  | [], env, hQ, _ => hQ
  | op :: l, env, hQ, hP => by
    have hP' : ∀ i, P ((slotsL C (env.push (op.eval C fun i => env.getD i default)) l).getD i
        default) := hP
    refine slotsL_inv hP0 hQ0 hC l _ ?_ hP'
    have hpre : ∀ i < env.size + 1,
        (slotsL C (env.push (op.eval C fun i => env.getD i default)) l).getD i default =
          (env.push (op.eval C fun i => env.getD i default)).getD i default :=
      fun i hi => slotsL_getD C _ l i (by simpa using hi)
    have hPenv : ∀ j, P (env.getD j default) := by
      intro j
      by_cases hj : j < env.size
      · have := hP' j
        rwa [hpre j (by omega), getD_push_lt _ _ _ hj] at this
      · rw [getD_ge hj]; exact hP0
    have hPx : P (op.eval C fun i => env.getD i default) := by
      have := hP' env.size
      rwa [hpre _ (by omega), getD_push_eq] at this
    exact getD_push_rec _ _ _ hQ (hC op _ hPenv hQ hPx) hQ0

theorem Kernel.slots_inv (hP0 : P default) (hQ0 : Q default) (hC : C.Preserves P Q)
    (k : Kernel) (inp : Array γ) (hinp : ∀ i, Q (inp.getD i default))
    (hP : ∀ i, P ((k.slots C inp).getD i default)) : ∀ i, Q ((k.slots C inp).getD i default) := by
  rw [Kernel.slots_eq_slotsL] at hP ⊢
  exact slotsL_inv hP0 hQ0 hC _ inp hinp hP

theorem Kernel.eval_inv (hP0 : P default) (hQ0 : Q default) (hC : C.Preserves P Q)
    (k : Kernel) (inp : Array γ) (hinp : ∀ i, Q (inp.getD i default))
    (hP : ∀ i, P ((k.slots C inp).getD i default)) : ∀ o, Q ((k.eval C inp).getD o default) := by
  intro o
  have hs := Kernel.slots_inv hP0 hQ0 hC k inp hinp hP
  simp only [Kernel.eval]
  by_cases ho : o < k.outs.size
  · simp [Array.getD, ho]
    simpa [Array.getD] using hs k.outs[o]
  · simp [Array.getD, ho, hQ0]

theorem foldl_push2_inv {Q : γ → Prop} (hQ0 : Q default) (F G : ℕ → γ) (hF : ∀ r, Q (F r))
    (hG : ∀ r, Q (G r)) : ∀ (l : List ℕ) (acc : Array γ), (∀ i, Q (acc.getD i default)) →
      ∀ i, Q ((l.foldl (fun acc r => (acc.push (F r)).push (G r)) acc).getD i default)
  | [], acc, h => h
  | r :: l, acc, h => by
    exact foldl_push2_inv hQ0 F G hF hG l _
      (getD_push_rec _ _ _ (getD_push_rec _ _ _ h (hF r) hQ0) (hG r) hQ0)

theorem bflyInputs_inv {Q : γ → Prop} (hQ0 : Q default) (R ns N : ℕ) (tw : Option (Array γ))
    (z : Array γ) (j : ℕ) (hz : ∀ i, Q (z.getD i default))
    (htw : ∀ t, tw = some t → ∀ i, Q (t.getD i default)) :
    ∀ i, Q ((bflyInputs R ns N tw z j).getD i default) := by
  have hxs := foldl_push2_inv hQ0 (fun r => z.getD (2 * (j + r * (N / R))) default)
    (fun r => z.getD (2 * (j + r * (N / R)) + 1) default) (fun _ => hz _) (fun _ => hz _)
    (List.range R) #[] (fun i => by simpa [Array.getD] using hQ0)
  cases tw with
  | none => exact hxs
  | some t =>
    exact foldl_push2_inv hQ0 _ _ (fun _ => htw t rfl _) (fun _ => htw t rfl _) _ _ hxs

/-- `P` holds for all slots of all butterflies of a pass. -/
def PassSlotsOK {δ : Type} [Inhabited δ] (A : Arith δ) (P : δ → Prop) (k : Kernel)
    (R ns N : ℕ) (tw : Option (Array δ)) (z : Array δ) : Prop :=
  ∀ j < N / R, ∀ i, P ((k.slots A (bflyInputs R ns N tw z j)).getD i default)

/-- `P` holds for all slots of all butterflies of all passes of a schedule. -/
def StockhamSlotsOK {δ : Type} [Inhabited δ] (A : Arith δ) (P : δ → Prop) (fwd : Bool) (N : ℕ)
    (rs : Array ℕ) (twOf : ℕ → Array δ) (z : Array δ) : Prop :=
  ∀ t < rs.size, PassSlotsOK A P (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1)
    (passNs rs t) N (if t ≥ 1 then some (twOf t) else none) (stockhamPre A fwd N rs twOf z t)

theorem passWith_inv (hP0 : P default) (hQ0 : Q default) (hC : C.Preserves P Q)
    (k : Kernel) (R ns N : ℕ) (tw : Option (Array γ)) (z : Array γ)
    (hz : ∀ i, Q (z.getD i default)) (htw : ∀ t, tw = some t → ∀ i, Q (t.getD i default))
    (hP : PassSlotsOK C P k R ns N tw z) : ∀ i, Q ((passWith C k R ns N tw z).getD i default) := by
  intro i
  simp only [passWith]
  by_cases hi : i < 2 * N
  · rw [getD_map_range _ _ _ hi]
    by_cases hj : i / 2 / (ns * R) * ns + i / 2 % ns < N / R
    · rw [getD_map_range _ _ _ hj]
      exact Kernel.eval_inv hP0 hQ0 hC k _ (bflyInputs_inv hQ0 R ns N tw z _ hz htw)
        (hP _ hj) _
    · have h0 : ((Array.range (N / R)).map fun j => k.eval C (bflyInputs R ns N tw z j)).getD
          (i / 2 / (ns * R) * ns + i / 2 % ns) #[] = #[] := getD_ge (by simpa using hj)
      rw [h0]
      simpa [Array.getD] using hQ0
  · rw [getD_ge (by simpa using hi)]
    exact hQ0

theorem stockhamWith_inv (hP0 : P default) (hQ0 : Q default) (hC : C.Preserves P Q)
    (fwd : Bool) (N : ℕ) (rs : Array ℕ) (twOf : ℕ → Array γ) (z : Array γ)
    (hz : ∀ i, Q (z.getD i default)) (htw : ∀ t i, Q ((twOf t).getD i default))
    (hP : StockhamSlotsOK C P fwd N rs twOf z) :
    ∀ i, Q ((stockhamWith C fwd N rs twOf z).getD i default) := by
  rw [stockhamWith_eq_pre]
  have : ∀ t ≤ rs.size, ∀ i, Q ((stockhamPre C fwd N rs twOf z t).getD i default) := by
    intro t ht
    induction t with
    | zero => exact hz
    | succ t ih =>
      rw [stockhamPre_succ]
      refine passWith_inv hP0 hQ0 hC _ _ _ _ _ _ (ih (by omega)) ?_ (hP t (by omega))
      intro tb htb
      split at htb
      · cases htb; exact htw t
      · cases htb
  exact this _ le_rfl

end Invariants

/-! ## The rounding model and the bound arithmetics -/

section Model

variable {α : Type}

/-- **The standard model with an underflow floor.** Every rounded operation of `A`, read
through `v`, has error at most `u · (|exact| + ℓ)` when its operands and result satisfy `fin`
(no overflow); negation is exact, `zero` is `0`, and constants have error at most
`κ · (|c| + ℓ)`. An absolute underflow allowance `η` is covered by `ℓ = η / u`. -/
structure StdModel (A : Arith α) (v : α → ℝ) (fin : α → Prop) (u κ ℓ : ℝ) : Prop where
  add : ∀ a b, fin a → fin b → fin (A.add a b) →
    |v (A.add a b) - (v a + v b)| ≤ u * (|v a + v b| + ℓ)
  sub : ∀ a b, fin a → fin b → fin (A.sub a b) →
    |v (A.sub a b) - (v a - v b)| ≤ u * (|v a - v b| + ℓ)
  mul : ∀ a b, fin a → fin b → fin (A.mul a b) →
    |v (A.mul a b) - v a * v b| ≤ u * (|v a * v b| + ℓ)
  neg : ∀ a, fin a → fin (A.neg a) → v (A.neg a) = -v a
  fma : ∀ a b c, fin a → fin b → fin c → fin (A.fma a b c) →
    |v (A.fma a b c) - (v a * v b + v c)| ≤ u * (|v a * v b + v c| + ℓ)
  fms : ∀ a b c, fin a → fin b → fin c → fin (A.fms a b c) →
    |v (A.fms a b c) - (v a * v b - v c)| ≤ u * (|v a * v b - v c| + ℓ)
  fnma : ∀ a b c, fin a → fin b → fin c → fin (A.fnma a b c) →
    |v (A.fnma a b c) - (v c - v a * v b)| ≤ u * (|v c - v a * v b| + ℓ)
  zero : v A.zero = 0
  cst : ∀ c, fin (A.cst c) → |v (A.cst c) - c.toReal| ≤ κ * (|c.toReal| + ℓ)

/-- The magnitude kernel: every operation replaced by its absolute-value version, plus the
underflow floor `ℓ` at every rounding. -/
noncomputable def magArith (ℓ : ℝ) : Arith ℝ where
  cst c := |c.toReal| + ℓ
  zero := 0
  add a b := a + b + ℓ
  sub a b := a + b + ℓ
  mul a b := a * b + ℓ
  neg a := a
  fma a b c := a * b + c + ℓ
  fms a b c := a * b + c + ℓ
  fnma a b c := c + a * b + ℓ

/-- Relative error factors: `1 + φ` gains a factor `1 + u` at every rounding. -/
noncomputable def errArith (u κ : ℝ) : Arith ℝ where
  cst _ := κ
  zero := 0
  add a b := (1 + u) * max (1 + a) (1 + b) - 1
  sub a b := (1 + u) * max (1 + a) (1 + b) - 1
  mul a b := (1 + u) * ((1 + a) * (1 + b)) - 1
  neg a := a
  fma a b c := (1 + u) * max ((1 + a) * (1 + b)) (1 + c) - 1
  fms a b c := (1 + u) * max ((1 + a) * (1 + b)) (1 + c) - 1
  fnma a b c := (1 + u) * max (1 + c) ((1 + a) * (1 + b)) - 1

/-- The error invariant: computed `ĝ`, exact `g`, magnitude bound `M`, relative factor `φ`. -/
def Err (ĝ g M φ : ℝ) : Prop := 0 ≤ φ ∧ |g| ≤ M ∧ |ĝ - g| ≤ φ * M

/-- An intermediate (unrounded) bound: `|xh| ≤ Q S`, `|xh - x| ≤ (Q - 1) S`, `|x| ≤ S`. -/
def Bnd (xh x Q S : ℝ) : Prop := 1 ≤ Q ∧ 0 ≤ S ∧ |xh| ≤ Q * S ∧ |xh - x| ≤ (Q - 1) * S ∧ |x| ≤ S

theorem Err.bnd {ĝ g M φ : ℝ} (h : Err ĝ g M φ) : Bnd ĝ g (1 + φ) M := by
  obtain ⟨h1, h2, h3⟩ := h
  have hM : 0 ≤ M := (abs_nonneg _).trans h2
  refine ⟨by linarith, hM, ?_, by simpa using h3, h2⟩
  calc |ĝ| = |(ĝ - g) + g| := by ring_nf
    _ ≤ |ĝ - g| + |g| := abs_add_le _ _
    _ ≤ φ * M + M := add_le_add h3 h2
    _ = (1 + φ) * M := by ring

theorem Bnd.neg {xh x Q S : ℝ} (h : Bnd xh x Q S) : Bnd (-xh) (-x) Q S := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, by rwa [abs_neg], ?_, by rwa [abs_neg]⟩
  rw [show -xh - -x = -(xh - x) by ring, abs_neg]; exact h4

theorem Bnd.add {xh x Q S yh y Q' S' : ℝ} (h : Bnd xh x Q S) (h' : Bnd yh y Q' S') :
    Bnd (xh + yh) (x + y) (max Q Q') (S + S') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨h1', h2', h3', h4', h5'⟩ := h'
  have hm : Q ≤ max Q Q' := le_max_left _ _
  have hm' : Q' ≤ max Q Q' := le_max_right _ _
  refine ⟨h1.trans hm, by linarith, ?_, ?_, ?_⟩
  · calc |xh + yh| ≤ |xh| + |yh| := abs_add_le _ _
      _ ≤ Q * S + Q' * S' := add_le_add h3 h3'
      _ ≤ max Q Q' * S + max Q Q' * S' :=
        add_le_add (mul_le_mul_of_nonneg_right hm h2) (mul_le_mul_of_nonneg_right hm' h2')
      _ = max Q Q' * (S + S') := by ring
  · calc |xh + yh - (x + y)| = |(xh - x) + (yh - y)| := by ring_nf
      _ ≤ |xh - x| + |yh - y| := abs_add_le _ _
      _ ≤ (Q - 1) * S + (Q' - 1) * S' := add_le_add h4 h4'
      _ ≤ (max Q Q' - 1) * S + (max Q Q' - 1) * S' :=
        add_le_add (mul_le_mul_of_nonneg_right (by linarith) h2)
          (mul_le_mul_of_nonneg_right (by linarith) h2')
      _ = (max Q Q' - 1) * (S + S') := by ring
  · exact (abs_add_le _ _).trans (add_le_add h5 h5')

theorem Bnd.sub {xh x Q S yh y Q' S' : ℝ} (h : Bnd xh x Q S) (h' : Bnd yh y Q' S') :
    Bnd (xh - yh) (x - y) (max Q Q') (S + S') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

theorem Bnd.mul {xh x Q S yh y Q' S' : ℝ} (h : Bnd xh x Q S) (h' : Bnd yh y Q' S') :
    Bnd (xh * yh) (x * y) (Q * Q') (S * S') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨h1', h2', h3', h4', h5'⟩ := h'
  have hQ0 : 0 ≤ Q := by linarith
  have hQ0' : 0 ≤ Q' := by linarith
  refine ⟨by nlinarith, mul_nonneg h2 h2', ?_, ?_, ?_⟩
  · rw [abs_mul]
    calc |xh| * |yh| ≤ (Q * S) * (Q' * S') :=
          mul_le_mul h3 h3' (abs_nonneg _) (mul_nonneg hQ0 h2)
      _ = Q * Q' * (S * S') := by ring
  · have e : xh * yh - x * y = (xh - x) * yh + x * (yh - y) := by ring
    rw [e]
    calc |(xh - x) * yh + x * (yh - y)| ≤ |xh - x| * |yh| + |x| * |yh - y| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ ((Q - 1) * S) * (Q' * S') + S * ((Q' - 1) * S') :=
          add_le_add (mul_le_mul h4 h3' (abs_nonneg _) (mul_nonneg (by linarith) h2))
            (mul_le_mul h5 h4' (abs_nonneg _) h2)
      _ = (Q * Q' - 1) * (S * S') := by ring
  · rw [abs_mul]; exact mul_le_mul h5 h5' (abs_nonneg _) h2

theorem Bnd.round {xh x Q S u ℓ r : ℝ} (h : Bnd xh x Q S) (hu : 0 ≤ u) (hℓ : 0 ≤ ℓ)
    (hr : |r - xh| ≤ u * (|xh| + ℓ)) : Err r x (S + ℓ) ((1 + u) * Q - 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by nlinarith, by linarith, ?_⟩
  calc |r - x| = |(r - xh) + (xh - x)| := by ring_nf
    _ ≤ |r - xh| + |xh - x| := abs_add_le _ _
    _ ≤ u * (Q * S + ℓ) + (Q - 1) * S := by
        refine add_le_add ((hr).trans ?_) h4
        exact mul_le_mul_of_nonneg_left (by linarith) hu
    _ ≤ ((1 + u) * Q - 1) * (S + ℓ) := by
        have : 0 ≤ (Q - 1) * ℓ := mul_nonneg (by linarith) hℓ
        have : 0 ≤ u * ((Q - 1) * ℓ) := mul_nonneg hu this
        nlinarith

/-- The product of the arithmetic under analysis with the exact, magnitude and error-factor
arithmetics. -/
noncomputable abbrev errProd (A : Arith α) (u κ ℓ : ℝ) : Arith (α × ℝ × ℝ × ℝ) :=
  A.prod (realArith.prod ((magArith ℓ).prod (errArith u κ)))

/-- The invariant on the product. -/
def ErrInv (v : α → ℝ) (p : α × ℝ × ℝ × ℝ) : Prop := Err (v p.1) p.2.1 p.2.2.1 p.2.2.2

theorem errProd_preserves {A : Arith α} {v : α → ℝ} {fin : α → Prop} {u κ ℓ : ℝ}
    (hA : StdModel A v fin u κ ℓ) (hu : 0 ≤ u) (hκ : 0 ≤ κ) (hℓ : 0 ≤ ℓ) :
    (errProd A u κ ℓ).Preserves (fun p => fin p.1) (ErrInv v) := by
  intro op g hP hQ hPr
  have hB : ∀ j, Bnd (v (g j).1) (g j).2.1 (1 + (g j).2.2.2) (g j).2.2.1 := fun j => (hQ j).bnd
  cases op with
  | cst c =>
    refine ⟨hκ, ?_, hA.cst c hPr⟩
    show |c.toReal| ≤ |c.toReal| + ℓ
    linarith
  | zero =>
    show Err (v A.zero) 0 0 0
    rw [hA.zero]; exact ⟨le_rfl, by simp, by simp⟩
  | add a b => exact ((hB a).add (hB b)).round hu hℓ (hA.add _ _ (hP a) (hP b) hPr)
  | sub a b => exact ((hB a).sub (hB b)).round hu hℓ (hA.sub _ _ (hP a) (hP b) hPr)
  | mul a b => exact ((hB a).mul (hB b)).round hu hℓ (hA.mul _ _ (hP a) (hP b) hPr)
  | neg a =>
    obtain ⟨h1, h2, h3⟩ := hQ a
    show Err (v (A.neg (g a).1)) (-(g a).2.1) (g a).2.2.1 (g a).2.2.2
    rw [hA.neg _ (hP a) hPr]
    refine ⟨h1, by rwa [abs_neg], ?_⟩
    rw [show -v (g a).1 - -(g a).2.1 = -(v (g a).1 - (g a).2.1) by ring, abs_neg]; exact h3
  | fma a b c =>
    exact (((hB a).mul (hB b)).add (hB c)).round hu hℓ (hA.fma _ _ _ (hP a) (hP b) (hP c) hPr)
  | fms a b c =>
    exact (((hB a).mul (hB b)).sub (hB c)).round hu hℓ (hA.fms _ _ _ (hP a) (hP b) (hP c) hPr)
  | fnma a b c =>
    exact ((hB c).sub ((hB a).mul (hB b))).round hu hℓ
      (hA.fnma _ _ _ (hP a) (hP b) (hP c) hPr)

end Model

/-! ## Main theorems -/

section Main

variable {α : Type}

theorem errProd_hom_fst (A : Arith α) (u κ ℓ : ℝ) : (errProd A u κ ℓ).IsHom A Prod.fst :=
  Arith.isHom_fst _ _

theorem errProd_hom_exact (A : Arith α) (u κ ℓ : ℝ) :
    (errProd A u κ ℓ).IsHom realArith (fun p => p.2.1) := by
  intro op g; cases op <;> rfl

theorem errProd_hom_mag (A : Arith α) (u κ ℓ : ℝ) :
    (errProd A u κ ℓ).IsHom (magArith ℓ) (fun p => p.2.2.1) := by
  intro op g; cases op <;> rfl

theorem errProd_hom_err (A : Arith α) (u κ ℓ : ℝ) :
    (errProd A u κ ℓ).IsHom (errArith u κ) (fun p => p.2.2.2) := by
  intro op g; cases op <;> rfl

variable [Inhabited α]

theorem getD_slots_map {β : Type} [Inhabited β] {A : Arith α} {B : Arith β} {f : α → β}
    (hf0 : f default = default) (hf : A.IsHom B f) (k : Kernel) (q : Array α) (i : ℕ) :
    f ((k.slots A q).getD i default) = (k.slots B (q.map f)).getD i default := by
  rw [Kernel.slots_map hf0 hf, getD_map_of hf0]

theorem getD_eval_map {β : Type} [Inhabited β] {A : Arith α} {B : Arith β} {f : α → β}
    (hf0 : f default = default) (hf : A.IsHom B f) (k : Kernel) (q : Array α) (i : ℕ) :
    f ((k.eval A q).getD i default) = (k.eval B (q.map f)).getD i default := by
  rw [Kernel.eval_map hf0 hf, getD_map_of hf0]

theorem getD_stockhamWith_map {β : Type} [Inhabited β] {A : Arith α} {B : Arith β}
    {f : α → β} (hf0 : f default = default) (hf : A.IsHom B f) (fwd : Bool) (N : ℕ)
    (rs : Array ℕ) (twOf : ℕ → Array α) (z : Array α) (i : ℕ) :
    f ((stockhamWith A fwd N rs twOf z).getD i default) =
      (stockhamWith B fwd N rs (fun t => (twOf t).map f) (z.map f)).getD i default := by
  rw [stockhamWith_map hf0 hf, getD_map_of hf0]

/-- Four arrays of equal length as one array of tuples. -/
def quadArr (a : Array α) (x m φ : Array ℝ) : Array (α × ℝ × ℝ × ℝ) :=
  pairArr a (pairArr x (pairArr m φ))

theorem quadArr_fst (a : Array α) (x m φ : Array ℝ) : (quadArr a x m φ).map Prod.fst = a :=
  pairArr_map_fst _ _

theorem quadArr_exact {a : Array α} {x : Array ℝ} (m φ : Array ℝ) (hx : x.size = a.size) :
    (quadArr a x m φ).map (fun p => p.2.1) = x := by
  rw [show (fun p : α × ℝ × ℝ × ℝ => p.2.1) = Prod.fst ∘ Prod.snd from rfl, ← Array.map_map,
    quadArr, pairArr_map_snd _ _ (by simp [pairArr_size, hx]), pairArr_map_fst]

theorem quadArr_mag {a : Array α} {x m : Array ℝ} (φ : Array ℝ) (hx : x.size = a.size)
    (hm : m.size = a.size) : (quadArr a x m φ).map (fun p => p.2.2.1) = m := by
  rw [show (fun p : α × ℝ × ℝ × ℝ => p.2.2.1) = Prod.fst ∘ Prod.snd ∘ Prod.snd from rfl,
    ← Array.map_map, ← Array.map_map, quadArr, pairArr_map_snd _ _ (by simp [pairArr_size, hx]),
    pairArr_map_snd _ _ (by simp [pairArr_size, hx, hm]), pairArr_map_fst]

theorem quadArr_err {a : Array α} {x m φ : Array ℝ} (hx : x.size = a.size)
    (hm : m.size = a.size) (hφ : φ.size = a.size) :
    (quadArr a x m φ).map (fun p => p.2.2.2) = φ := by
  rw [show (fun p : α × ℝ × ℝ × ℝ => p.2.2.2) = Prod.snd ∘ Prod.snd ∘ Prod.snd from rfl,
    ← Array.map_map, ← Array.map_map, quadArr, pairArr_map_snd _ _ (by simp [pairArr_size, hx]),
    pairArr_map_snd _ _ (by simp [pairArr_size, hx, hm]),
    pairArr_map_snd _ _ (by simp [hm, hφ])]

theorem quadArr_inv {a : Array α} {x m φ : Array ℝ} (hx : x.size = a.size)
    (hm : m.size = a.size) (hφ : φ.size = a.size) (v : α → ℝ) (i : ℕ) :
    ErrInv v ((quadArr a x m φ).getD i default) ↔
      Err (v (a.getD i default)) (x.getD i 0) (m.getD i 0) (φ.getD i 0) := by
  rw [quadArr, pairArr_getD _ _ (by simp [pairArr_size, hx]),
    pairArr_getD _ _ (by simp [pairArr_size, hx, hm]), pairArr_getD _ _ (by simp [hm, hφ])]
  rfl

variable {A : Arith α} {v : α → ℝ} {fin : α → Prop} {u κ ℓ : ℝ}

theorem errInv_default (hv0 : v default = 0) : ErrInv v default := by
  show Err (v default) 0 0 0
  rw [hv0]; exact ⟨le_rfl, by simp, by simp⟩

/-- **Error bound for a kernel** (invariant form): if every input `x̃ᵢ` approximates `xᵢ`
with `|v x̃ᵢ - xᵢ| ≤ φᵢ mᵢ` and `|xᵢ| ≤ mᵢ`, and no slot of the evaluation over `A`
leaves `fin` (no overflow), then every output `o` satisfies
`|v (k.eval A x̃)ₒ - (k.eval realArith x)ₒ| ≤ (k.eval errArith φ)ₒ · (k.eval magArith m)ₒ`
and `|(k.eval realArith x)ₒ| ≤ (k.eval magArith m)ₒ`. -/
theorem Kernel.eval_err (hA : StdModel A v fin u κ ℓ) (hu : 0 ≤ u) (hκ : 0 ≤ κ) (hℓ : 0 ≤ ℓ)
    (hv0 : v default = 0) (k : Kernel) (inp : Array α) (x m φ : Array ℝ)
    (hx : x.size = inp.size) (hm : m.size = inp.size) (hφ : φ.size = inp.size)
    (hin : ∀ i, Err (v (inp.getD i default)) (x.getD i 0) (m.getD i 0) (φ.getD i 0))
    (hfin : ∀ i, fin ((k.slots A inp).getD i default)) (o : ℕ) :
    Err (v ((k.eval A inp).getD o default)) ((k.eval realArith x).getD o 0)
      ((k.eval (magArith ℓ) m).getD o 0) ((k.eval (errArith u κ) φ).getD o 0) := by
  set p := quadArr inp x m φ
  have hfin0 : fin default := by
    have := hfin (k.slots A inp).size
    rwa [getD_ge (lt_irrefl _)] at this
  have hP : ∀ i, fin ((k.slots (errProd A u κ ℓ) p).getD i default).1 := by
    intro i
    rw [getD_slots_map (f := Prod.fst) rfl (errProd_hom_fst A u κ ℓ), quadArr_fst]
    exact hfin i
  have hinv := Kernel.eval_inv (P := fun q => fin q.1) hfin0 (errInv_default hv0)
    (errProd_preserves hA hu hκ hℓ) k p (fun i => (quadArr_inv hx hm hφ v i).2 (hin i)) hP o
  have e1 := getD_eval_map (f := Prod.fst) rfl (errProd_hom_fst A u κ ℓ) k p o
  have e2 := getD_eval_map (f := fun p => p.2.1) rfl (errProd_hom_exact A u κ ℓ) k p o
  have e3 := getD_eval_map (f := fun p => p.2.2.1) rfl (errProd_hom_mag A u κ ℓ) k p o
  have e4 := getD_eval_map (f := fun p => p.2.2.2) rfl (errProd_hom_err A u κ ℓ) k p o
  rw [quadArr_fst] at e1
  rw [quadArr_exact _ _ hx] at e2
  rw [quadArr_mag _ hx hm] at e3
  rw [quadArr_err hx hm hφ] at e4
  have h2 : (default : ℝ) = 0 := rfl
  rw [h2] at e2 e3 e4
  rw [← e1, ← e2, ← e3, ← e4]
  exact hinv

/-- **Error bound for a kernel.** For inputs `x̃` (over `A`) approximating exact inputs `x`
with `|v x̃ᵢ - xᵢ| ≤ φᵢ · mᵢ` and `|xᵢ| ≤ mᵢ` (`φᵢ ≥ 0`), if no slot of the evaluation
over `A` leaves `fin`, every output satisfies
`|v (k.eval A x̃)ₒ - (k.eval realArith x)ₒ| ≤ (k.eval (errArith u κ) φ)ₒ · (k.eval (magArith ℓ) m)ₒ`. -/
theorem Kernel.eval_error (hA : StdModel A v fin u κ ℓ) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hℓ : 0 ≤ ℓ) (hv0 : v default = 0) (k : Kernel) (inp : Array α) (x m φ : Array ℝ)
    (hx : x.size = inp.size) (hm : m.size = inp.size) (hφ : φ.size = inp.size)
    (hφ0 : ∀ i, 0 ≤ φ.getD i 0) (hxm : ∀ i, |x.getD i 0| ≤ m.getD i 0)
    (hin : ∀ i, |v (inp.getD i default) - x.getD i 0| ≤ φ.getD i 0 * m.getD i 0)
    (hfin : ∀ i, fin ((k.slots A inp).getD i default)) (o : ℕ) :
    |v ((k.eval A inp).getD o default) - (k.eval realArith x).getD o 0| ≤
      (k.eval (errArith u κ) φ).getD o 0 * (k.eval (magArith ℓ) m).getD o 0 :=
  (Kernel.eval_err hA hu hκ hℓ hv0 k inp x m φ hx hm hφ
    (fun i => ⟨hφ0 i, hxm i, hin i⟩) hfin o).2.2

/-- **Error bound for the Stockham schedule** (invariant form). Run the passes of the plan
`rs` over `A` with twiddle tables `twC t`, and exactly with tables `twE t` (same sizes) whose
entries have modulus `≤ 1` and are approximated with absolute error `≤ τ`. If the input `zC`
approximates `z` (`|v zCᵢ - zᵢ| ≤ φᵢ mᵢ`, `|zᵢ| ≤ mᵢ`) and no slot of any butterfly of any
pass leaves `fin`, then every output entry satisfies the invariant `Err` with the magnitude
bounds `M` and relative factors `Φ` obtained by running the *same schedule* over
`magArith ℓ` (inputs `m`, twiddles `1`) and over `errArith u κ` (inputs `φ`, twiddles `τ`). -/
theorem stockhamWith_err (hA : StdModel A v fin u κ ℓ) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hℓ : 0 ≤ ℓ) (hv0 : v default = 0) (hfin0 : fin default) (fwd : Bool) (N : ℕ)
    (rs : Array ℕ) (twC : ℕ → Array α) (twE : ℕ → Array ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (htwsz : ∀ t, (twE t).size = (twC t).size)
    (htw1 : ∀ t i, |(twE t).getD i 0| ≤ 1)
    (htw : ∀ t i, |v ((twC t).getD i default) - (twE t).getD i 0| ≤ τ)
    (zC : Array α) (z m φ : Array ℝ)
    (hz : z.size = zC.size) (hm : m.size = zC.size) (hφ : φ.size = zC.size)
    (hin : ∀ i, Err (v (zC.getD i default)) (z.getD i 0) (m.getD i 0) (φ.getD i 0))
    (hfin : StockhamSlotsOK A fin fwd N rs twC zC) (i : ℕ) :
    Err (v ((stockhamWith A fwd N rs twC zC).getD i default))
      ((stockhamWith realArith fwd N rs twE z).getD i 0)
      ((stockhamWith (magArith ℓ) fwd N rs (fun t => (twE t).map fun _ => 1) m).getD i 0)
      ((stockhamWith (errArith u κ) fwd N rs (fun t => (twE t).map fun _ => τ) φ).getD i 0) := by
  set p := quadArr zC z m φ
  set twM : ℕ → Array ℝ := fun t => (twE t).map fun _ => 1 with htwM
  set twF : ℕ → Array ℝ := fun t => (twE t).map fun _ => τ with htwF
  set twP : ℕ → Array (α × ℝ × ℝ × ℝ) := fun t => quadArr (twC t) (twE t) (twM t) (twF t)
  have hsM : ∀ t, (twM t).size = (twC t).size := fun t => by simp [twM, htwsz]
  have hsF : ∀ t, (twF t).size = (twC t).size := fun t => by simp [twF, htwsz]
  have hPfst : (fun t => (twP t).map Prod.fst) = twC := funext fun t => quadArr_fst _ _ _ _
  have hPex : (fun t => (twP t).map (fun q => q.2.1)) = twE :=
    funext fun t => quadArr_exact _ _ (htwsz t)
  have hPmag : (fun t => (twP t).map (fun q => q.2.2.1)) = twM :=
    funext fun t => quadArr_mag _ (htwsz t) (hsM t)
  have hPerr : (fun t => (twP t).map (fun q => q.2.2.2)) = twF :=
    funext fun t => quadArr_err (htwsz t) (hsM t) (hsF t)
  have htwinv : ∀ t i, ErrInv v ((twP t).getD i default) := by
    intro t i
    rw [quadArr_inv (htwsz t) (hsM t) (hsF t)]
    by_cases hi : i < (twE t).size
    · have hM : (twM t).getD i 0 = 1 := by simp [twM, Array.getD, hi]
      have hF : (twF t).getD i 0 = τ := by simp [twF, Array.getD, hi]
      rw [hM, hF]
      exact ⟨hτ, htw1 t i, by simpa using htw t i⟩
    · have hM : (twM t).getD i 0 = 0 := getD_ge (by simpa [twM] using hi)
      have hF : (twF t).getD i 0 = 0 := getD_ge (by simpa [twF] using hi)
      have hC : (twC t).getD i default = default := getD_ge (by rw [← htwsz t]; exact hi)
      have hE : (twE t).getD i 0 = 0 := getD_ge hi
      rw [hM, hF, hC, hE, hv0]
      exact ⟨le_rfl, by simp, by simp⟩
  have hopt : ∀ t : ℕ, (if t ≥ 1 then some (twP t) else none).map (Array.map Prod.fst) =
      (if t ≥ 1 then some (twC t) else none) := by
    intro t
    split
    · simp only [Option.map_some]
      exact congrArg some (congrFun hPfst t)
    · rfl
  have hP : StockhamSlotsOK (errProd A u κ ℓ) (fun q => fin q.1) fwd N rs twP p := by
    intro t ht j hj i
    rw [getD_slots_map (f := Prod.fst) rfl (errProd_hom_fst A u κ ℓ),
      ← bflyInputs_map (f := (Prod.fst : α × ℝ × ℝ × ℝ → α)) rfl,
      ← stockhamPre_map (f := (Prod.fst : α × ℝ × ℝ × ℝ → α)) rfl (errProd_hom_fst A u κ ℓ), hPfst, quadArr_fst, hopt]
    exact hfin t ht j hj i
  have hinv := stockhamWith_inv (P := fun q => fin q.1) hfin0 (errInv_default hv0)
    (errProd_preserves hA hu hκ hℓ) fwd N rs twP p
    (fun i => (quadArr_inv hz hm hφ v i).2 (hin i)) htwinv hP i
  have e1 := getD_stockhamWith_map (f := Prod.fst) rfl (errProd_hom_fst A u κ ℓ) fwd N rs twP p i
  have e2 := getD_stockhamWith_map (f := fun q => q.2.1) rfl (errProd_hom_exact A u κ ℓ)
    fwd N rs twP p i
  have e3 := getD_stockhamWith_map (f := fun q => q.2.2.1) rfl (errProd_hom_mag A u κ ℓ)
    fwd N rs twP p i
  have e4 := getD_stockhamWith_map (f := fun q => q.2.2.2) rfl (errProd_hom_err A u κ ℓ)
    fwd N rs twP p i
  rw [hPfst, quadArr_fst] at e1
  rw [hPex, quadArr_exact _ _ hz] at e2
  rw [hPmag, quadArr_mag _ hz hm] at e3
  rw [hPerr, quadArr_err hz hm hφ] at e4
  have h2 : (default : ℝ) = 0 := rfl
  rw [h2] at e2 e3 e4
  rw [← e1, ← e2, ← e3, ← e4]
  exact hinv

/-! ### The exact twiddles and the DFT -/

theorem norm_twiddle (fwd : Bool) (n k : ℕ) : ‖twiddle fwd n k‖ = 1 := by
  unfold twiddle
  have e : ((if fwd then -1 else 1) * (2 * Real.pi * Complex.I * k / n) : ℂ) =
      (((if fwd then -1 else 1 : ℝ) * (2 * Real.pi * k / n) : ℝ) : ℂ) * Complex.I := by
    split <;> push_cast <;> ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

theorem abs_exactTw_le_one (fwd : Bool) (N R ns i : ℕ) :
    |(exactTw fwd N R ns).getD i 0| ≤ 1 := by
  by_cases hi : i < 2 * (R - 1) * ns
  · rw [exactTw, getD_map_range _ _ _ hi]
    simp only
    split
    · exact (Complex.abs_re_le_norm _).trans (norm_twiddle _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (norm_twiddle _ _ _).le
  · rw [getD_ge (by simpa [exactTw] using hi)]
    simp

/-- **Error bound for the Stockham schedule against the DFT.** With twiddle tables `twC t`
approximating the exact tables `exactTwOf` entrywise within `τ`, and input `zC`
approximating `z` (`|v zCᵢ - zᵢ| ≤ φᵢ mᵢ`, `|zᵢ| ≤ mᵢ`), if no slot of any butterfly
leaves `fin`, the computed transform differs from the exact DFT of `z` (interleaved
real/imaginary parts) by at most `Φᵢ · Mᵢ` at every entry `i < 2N`, where `Φ` and `M` run the
same schedule over `errArith u κ` and `magArith ℓ`. -/
theorem stockhamWith_error_dft (hA : StdModel A v fin u κ ℓ) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hℓ : 0 ≤ ℓ) (hv0 : v default = 0) (hfin0 : fin default) (fwd : Bool) (rs : Array ℕ)
    (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ) (hN : N = rs.toList.prod)
    (twC : ℕ → Array α) (τ : ℝ) (hτ : 0 ≤ τ)
    (htwsz : ∀ t, (exactTwOf fwd N rs t).size = (twC t).size)
    (htw : ∀ t i, |v ((twC t).getD i default) - (exactTwOf fwd N rs t).getD i 0| ≤ τ)
    (zC : Array α) (z m φ : Array ℝ) (hzN : zC.size = 2 * N)
    (hz : z.size = zC.size) (hm : m.size = zC.size) (hφ : φ.size = zC.size)
    (hφ0 : ∀ i, 0 ≤ φ.getD i 0) (hzm : ∀ i, |z.getD i 0| ≤ m.getD i 0)
    (hin : ∀ i, |v (zC.getD i default) - z.getD i 0| ≤ φ.getD i 0 * m.getD i 0)
    (hfin : StockhamSlotsOK A fin fwd N rs twC zC) (i : ℕ) (hi : i < 2 * N) :
    |v ((stockhamWith A fwd N rs twC zC).getD i default) -
        (let y := dftSum fwd N (fun j => ⟨z.getD (2 * j) 0, z.getD (2 * j + 1) 0⟩) (i / 2)
         if i % 2 = 0 then y.re else y.im)| ≤
      (stockhamWith (errArith u κ) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => τ) φ).getD i 0 *
        (stockhamWith (magArith ℓ) fwd N rs
          (fun t => (exactTwOf fwd N rs t).map fun _ => 1) m).getD i 0 := by
  have h := (stockhamWith_err hA hu hκ hℓ hv0 hfin0 fwd N rs twC (exactTwOf fwd N rs) τ hτ htwsz
    (fun t i => abs_exactTw_le_one _ _ _ _ _) htw zC z m φ hz hm hφ
    (fun i => ⟨hφ0 i, hzm i, hin i⟩) hfin i).2.2
  rwa [stockhamWith_exact fwd rs hrs N hN z (by omega), getD_map_range _ _ _ hi] at h

/-! ### Closed form: rounding depth and input degree -/

/-- Rounding depth `n` and input degree `p` of every slot: `1 + φ ≤ (1+u)^n (1+t)^p` when
every input and constant carries a relative error factor `≤ t`. -/
def depthArith : Arith (ℕ × ℕ) where
  cst _ := (0, 1)
  zero := (0, 0)
  add a b := (max a.1 b.1 + 1, max a.2 b.2)
  sub a b := (max a.1 b.1 + 1, max a.2 b.2)
  mul a b := (a.1 + b.1 + 1, a.2 + b.2)
  neg a := a
  fma a b c := (max (a.1 + b.1) c.1 + 1, max (a.2 + b.2) c.2)
  fms a b c := (max (a.1 + b.1) c.1 + 1, max (a.2 + b.2) c.2)
  fnma a b c := (max c.1 (a.1 + b.1) + 1, max c.2 (a.2 + b.2))

/-- `0 ≤ φ` and `1 + φ ≤ (1+u)^n (1+t)^p`. -/
def DepthInv (u t : ℝ) (q : ℝ × ℕ × ℕ) : Prop :=
  0 ≤ q.1 ∧ 1 + q.1 ≤ (1 + u) ^ q.2.1 * (1 + t) ^ q.2.2

theorem depth_mono {u t X : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) {n p n' p' : ℕ} (hn : n ≤ n')
    (hp : p ≤ p') (h : X ≤ (1 + u) ^ n * (1 + t) ^ p) : X ≤ (1 + u) ^ n' * (1 + t) ^ p' :=
  h.trans (mul_le_mul (pow_le_pow_right₀ (by linarith) hn) (pow_le_pow_right₀ (by linarith) hp)
    (by positivity) (by positivity))

theorem depth_preserves {u κ t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hκ : 0 ≤ κ) (hκt : κ ≤ t) :
    ((errArith u κ).prod depthArith).Preserves (fun _ => True) (DepthInv u t) := by
  intro op g _ hQ _
  have h1 : ∀ j, 1 ≤ 1 + (g j).1 := fun j => by linarith [(hQ j).1]
  have hu1 : (1 : ℝ) ≤ 1 + u := by linarith
  have hpos : ∀ j, 0 ≤ 1 + (g j).1 := fun j => by linarith [(hQ j).1]
  -- the rounding step
  have rnd : ∀ (X : ℝ) (n p : ℕ), 1 ≤ X → X ≤ (1 + u) ^ n * (1 + t) ^ p →
      DepthInv u t ((1 + u) * X - 1, n + 1, p) := by
    intro X n p hX h
    refine ⟨by nlinarith, ?_⟩
    simp only [add_sub_cancel, pow_succ]
    calc (1 + u) * X ≤ (1 + u) * ((1 + u) ^ n * (1 + t) ^ p) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = (1 + u) ^ n * (1 + u) * (1 + t) ^ p := by ring
  have prod : ∀ a b : ℕ, (1 + (g a).1) * (1 + (g b).1) ≤
      (1 + u) ^ ((g a).2.1 + (g b).2.1) * (1 + t) ^ ((g a).2.2 + (g b).2.2) := by
    intro a b
    rw [pow_add, pow_add]
    calc (1 + (g a).1) * (1 + (g b).1) ≤
          ((1 + u) ^ (g a).2.1 * (1 + t) ^ (g a).2.2) * ((1 + u) ^ (g b).2.1 * (1 + t) ^ (g b).2.2) :=
          mul_le_mul (hQ a).2 (hQ b).2 (hpos b) (by positivity)
      _ = _ := by ring
  cases op with
  | cst c =>
    refine ⟨hκ, ?_⟩
    show 1 + κ ≤ (1 + u) ^ 0 * (1 + t) ^ 1
    rw [pow_zero, pow_one, one_mul]; linarith
  | zero =>
    refine ⟨le_rfl, ?_⟩
    show (1 : ℝ) + 0 ≤ (1 + u) ^ 0 * (1 + t) ^ 0
    simp
  | add a b | sub a b =>
    refine rnd _ _ _ ((h1 a).trans (le_max_left _ _)) (max_le ?_ ?_)
    · exact depth_mono hu ht (le_max_left _ _) (le_max_left _ _) (hQ a).2
    · exact depth_mono hu ht (le_max_right _ _) (le_max_right _ _) (hQ b).2
  | mul a b =>
    exact rnd _ _ _ (one_le_mul_of_one_le_of_one_le (h1 a) (h1 b)) (prod a b)
  | neg a => exact hQ a
  | fma a b c | fms a b c =>
    refine rnd _ _ _ ((one_le_mul_of_one_le_of_one_le (h1 a) (h1 b)).trans (le_max_left _ _))
      (max_le ?_ ?_)
    · exact depth_mono hu ht (le_max_left _ _) (le_max_left _ _) (prod a b)
    · exact depth_mono hu ht (le_max_right _ _) (le_max_right _ _) (hQ c).2
  | fnma a b c =>
    refine rnd _ _ _ ((h1 c).trans (le_max_left _ _)) (max_le ?_ ?_)
    · exact depth_mono hu ht (le_max_left _ _) (le_max_left _ _) (hQ c).2
    · exact depth_mono hu ht (le_max_right _ _) (le_max_right _ _) (prod a b)

/-- **Closed form of the relative error factors.** If every input factor is in `[0, t]` and
`κ ≤ t`, output `o` has `(k.eval errArith φ)ₒ ≤ (1+u)^n (1+t)^p - 1`, where
`(n, p) = (k.eval depthArith (0, 1)…)ₒ` are its rounding depth (counted along products) and
its degree in the inputs. -/
theorem Kernel.errArith_le_depth {u κ t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hκ : 0 ≤ κ)
    (hκt : κ ≤ t) (k : Kernel) (φ : Array ℝ) (hφ : ∀ i, 0 ≤ φ.getD i 0 ∧ φ.getD i 0 ≤ t)
    (o : ℕ) :
    (k.eval (errArith u κ) φ).getD o 0 ≤
      (1 + u) ^ ((k.eval depthArith (φ.map fun _ => (0, 1))).getD o default).1 *
        (1 + t) ^ ((k.eval depthArith (φ.map fun _ => (0, 1))).getD o default).2 - 1 := by
  set d := φ.map fun _ => ((0, 1) : ℕ × ℕ)
  have hd : d.size = φ.size := by simp [d]
  set p := pairArr φ d
  have h0 : DepthInv u t default := ⟨le_rfl, by simp [default]⟩
  have hp : ∀ i, DepthInv u t (p.getD i default) := by
    intro i
    rw [pairArr_getD _ _ hd]
    by_cases hi : i < φ.size
    · have : d.getD i default = (0, 1) := by simp [d, Array.getD, hi]
      rw [this]
      refine ⟨(hφ i).1, ?_⟩
      show 1 + φ.getD i default ≤ (1 + u) ^ 0 * (1 + t) ^ 1
      rw [pow_zero, pow_one, one_mul]; linarith [(hφ i).2, show φ.getD i default = φ.getD i 0 from rfl]
    · rw [getD_ge hi, getD_ge (by rwa [hd])]
      exact h0
  have hinv := Kernel.eval_inv (P := fun _ => True) trivial h0 (depth_preserves hu ht hκ hκt)
    k p hp (fun _ => trivial) o
  have e1 := getD_eval_map (f := Prod.fst) rfl (Arith.isHom_fst (errArith u κ) depthArith) k p o
  have e2 := getD_eval_map (f := Prod.snd) rfl (Arith.isHom_snd (errArith u κ) depthArith) k p o
  rw [pairArr_map_fst] at e1
  rw [pairArr_map_snd _ _ hd] at e2
  have h2 : (default : ℝ) = 0 := rfl
  rw [h2] at e1
  rw [← e1, ← e2]
  linarith [hinv.2]

/-- **Kernel error bound, closed form.** Under the hypotheses of `Kernel.eval_error`, with
every input factor `φᵢ ∈ [0, t]` and `κ ≤ t`,
`|v (k.eval A x̃)ₒ - (k.eval realArith x)ₒ| ≤ ((1+u)^n (1+t)^p - 1) · (k.eval (magArith ℓ) m)ₒ`
with `(n, p)` the rounding depth and input degree of output `o` (`depthArith`). -/
theorem Kernel.eval_error_depth (hA : StdModel A v fin u κ ℓ) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (hℓ : 0 ≤ ℓ) (hv0 : v default = 0) {t : ℝ} (ht : 0 ≤ t) (hκt : κ ≤ t) (k : Kernel)
    (inp : Array α) (x m φ : Array ℝ)
    (hx : x.size = inp.size) (hm : m.size = inp.size) (hφ : φ.size = inp.size)
    (hφt : ∀ i, 0 ≤ φ.getD i 0 ∧ φ.getD i 0 ≤ t) (hxm : ∀ i, |x.getD i 0| ≤ m.getD i 0)
    (hin : ∀ i, |v (inp.getD i default) - x.getD i 0| ≤ φ.getD i 0 * m.getD i 0)
    (hfin : ∀ i, fin ((k.slots A inp).getD i default)) (o : ℕ) :
    |v ((k.eval A inp).getD o default) - (k.eval realArith x).getD o 0| ≤
      ((1 + u) ^ ((k.eval depthArith (φ.map fun _ => (0, 1))).getD o default).1 *
        (1 + t) ^ ((k.eval depthArith (φ.map fun _ => (0, 1))).getD o default).2 - 1) *
        (k.eval (magArith ℓ) m).getD o 0 := by
  have h := Kernel.eval_err hA hu hκ hℓ hv0 k inp x m φ hx hm hφ
    (fun i => ⟨(hφt i).1, hxm i, hin i⟩) hfin o
  have hM : 0 ≤ (k.eval (magArith ℓ) m).getD o 0 := (abs_nonneg _).trans h.2.1
  exact h.2.2.trans (mul_le_mul_of_nonneg_right
    (Kernel.errArith_le_depth hu ht hκ hκt k φ hφt o) hM)

/-- **Closed form of the schedule's relative error factors.** If every input factor is in
`[0, t]`, the twiddle factor `τ ∈ [0, t]` and `κ ≤ t`, entry `i` of the schedule run over
`errArith u κ` is at most `(1+u)^n (1+t)^p - 1`, where `(n, p)` is entry `i` of the same
schedule run over `depthArith` (every input and twiddle `(0, 1)`). -/
theorem stockhamWith_errArith_le_depth {u κ t τ : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hκ : 0 ≤ κ)
    (hκt : κ ≤ t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (fwd : Bool) (N : ℕ) (rs : Array ℕ)
    (tw : ℕ → Array ℝ) (φ : Array ℝ) (hφ : ∀ i, 0 ≤ φ.getD i 0 ∧ φ.getD i 0 ≤ t) (i : ℕ) :
    (stockhamWith (errArith u κ) fwd N rs (fun t => (tw t).map fun _ => τ) φ).getD i 0 ≤
      (1 + u) ^ ((stockhamWith depthArith fwd N rs (fun t => (tw t).map fun _ => (0, 1))
          (φ.map fun _ => (0, 1))).getD i default).1 *
        (1 + t) ^ ((stockhamWith depthArith fwd N rs (fun t => (tw t).map fun _ => (0, 1))
          (φ.map fun _ => (0, 1))).getD i default).2 - 1 := by
  have h0 : DepthInv u t default := ⟨le_rfl, by simp [default]⟩
  have hpair : ∀ (a : Array ℝ), (∀ i, 0 ≤ a.getD i 0 ∧ a.getD i 0 ≤ t) →
      ∀ i, DepthInv u t ((pairArr a (a.map fun _ => ((0, 1) : ℕ × ℕ))).getD i default) := by
    intro a ha i
    rw [pairArr_getD _ _ (by simp)]
    by_cases hi : i < a.size
    · have : (a.map fun _ => ((0, 1) : ℕ × ℕ)).getD i default = (0, 1) := by
        simp [Array.getD, hi]
      rw [this]
      refine ⟨(ha i).1, ?_⟩
      show 1 + a.getD i default ≤ (1 + u) ^ 0 * (1 + t) ^ 1
      rw [pow_zero, pow_one, one_mul]
      linarith [(ha i).2, show a.getD i default = a.getD i 0 from rfl]
    · rw [getD_ge hi, getD_ge (by simpa using hi)]
      exact h0
  set tF : ℕ → Array ℝ := fun t => (tw t).map fun _ => τ
  set twP : ℕ → Array (ℝ × ℕ × ℕ) := fun t => pairArr (tF t) ((tF t).map fun _ => (0, 1))
  set p := pairArr φ (φ.map fun _ => ((0, 1) : ℕ × ℕ))
  have htwP : ∀ t' i, DepthInv u t ((twP t').getD i default) := by
    intro t' i
    refine hpair _ (fun j => ?_) i
    by_cases hj : j < (tw t').size
    · have : (tF t').getD j 0 = τ := by simp [tF, Array.getD, hj]
      rw [this]; exact ⟨hτ, hτt⟩
    · rw [getD_ge (by simpa [tF] using hj)]; exact ⟨le_rfl, ht⟩
  have hinv := stockhamWith_inv (P := fun _ => True) trivial h0 (depth_preserves hu ht hκ hκt)
    fwd N rs twP p (hpair φ hφ) htwP (fun _ _ _ _ _ => trivial) i
  have e1 := getD_stockhamWith_map (f := Prod.fst) rfl (Arith.isHom_fst (errArith u κ) depthArith)
    fwd N rs twP p i
  have e2 := getD_stockhamWith_map (f := Prod.snd) rfl (Arith.isHom_snd (errArith u κ) depthArith)
    fwd N rs twP p i
  have hf1 : (fun t => (twP t).map Prod.fst) = tF := funext fun t => pairArr_map_fst _ _
  have hf2 : (fun t => (twP t).map Prod.snd) = fun t => (tw t).map fun _ => ((0, 1) : ℕ × ℕ) :=
    funext fun t => by
      rw [pairArr_map_snd _ _ (by simp), Array.map_map]
      rfl
  rw [hf1, pairArr_map_fst] at e1
  rw [hf2, pairArr_map_snd _ _ (by simp)] at e2
  have h2 : (default : ℝ) = 0 := rfl
  rw [h2] at e1
  rw [← e1, ← e2]
  linarith [hinv.2]

theorem magArith_preserves {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (magArith ℓ).Preserves (fun _ => True) (fun x => 0 ≤ x) := by
  intro op g _ hQ _
  cases op with
  | cst c => exact add_nonneg (abs_nonneg _) hℓ
  | zero => exact le_rfl
  | add a b | sub a b => exact add_nonneg (add_nonneg (hQ a) (hQ b)) hℓ
  | mul a b => exact add_nonneg (mul_nonneg (hQ a) (hQ b)) hℓ
  | neg a => exact hQ a
  | fma a b c | fms a b c => exact add_nonneg (add_nonneg (mul_nonneg (hQ a) (hQ b)) (hQ c)) hℓ
  | fnma a b c => exact add_nonneg (add_nonneg (hQ c) (mul_nonneg (hQ a) (hQ b))) hℓ

/-- The magnitude bounds of a schedule are nonnegative. -/
theorem stockhamWith_magArith_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (fwd : Bool) (N : ℕ) (rs : Array ℕ)
    (tw : ℕ → Array ℝ) (htw : ∀ t i, 0 ≤ (tw t).getD i 0) (m : Array ℝ)
    (hm : ∀ i, 0 ≤ m.getD i 0) (i : ℕ) :
    0 ≤ (stockhamWith (magArith ℓ) fwd N rs tw m).getD i 0 :=
  stockhamWith_inv (P := fun _ => True) (Q := fun x : ℝ => 0 ≤ x) trivial le_rfl
    (magArith_preserves hℓ) fwd N rs tw m hm htw (fun _ _ _ _ _ => trivial) i

theorem getD_map_const_nonneg {β : Type} (a : Array β) {c : ℝ} (hc : 0 ≤ c) (i : ℕ) :
    0 ≤ (a.map fun _ => c).getD i 0 := by
  by_cases hi : i < a.size
  · simp [Array.getD, hi, hc]
  · rw [getD_ge (by simpa using hi)]

end Main

end LeanFFTW.Gen
