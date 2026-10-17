/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Proof.Butterfly

/-!
# The Stockham pass schedule computes the DFT (exact arithmetic)

The fast engine (`LeanFFTW/Gen/Stockham.lean`) runs, for a plan `rs = [R₀, …, R_{s-1}]` of
size `N = R₀ ⋯ R_{s-1}`, the passes `passWith` of `stockhamWith`. Here they are evaluated
over exact real arithmetic (`realArith`), with the exact twiddle tables `exactTw` (the same
layout and exponents as `passTwiddles`: entry `(r, k)` of pass `(R, ns)` is
`ω_N^{r·k·N/(ns·R)}`), and shown to compute `dftSum`.

The proof is the Stockham invariant `StockInv`: before a pass with `ns` (`ns ∣ N`), the
complex number at position `b·ns + k` (`k < ns`, `b < N/ns`) is the length-`ns` DFT of the
decimated subsequence `m ↦ x (b + (N/ns)·m)` at frequency `k`. A pass of radix `R` maps it to
the invariant for `ns·R` (`stockInv_pass`), by `butterflyK_correct` and the Cooley–Tukey
step `dftSum_ct`. Initially (`ns = 1`) the invariant holds trivially, and after all passes
(`ns = N`) it states that the array is the DFT of the input.

Main results:
* `LeanFFTW.Gen.stockInv_pass`: one pass;
* `LeanFFTW.Gen.stockhamWith_exact`: the whole schedule computes `dftSum`.
-/

open Complex Finset

namespace LeanFFTW.Gen

open LeanFFTW

/-- The complex number at position `c` of interleaved data. -/
noncomputable def cx (z : Array ℝ) (c : ℕ) : ℂ := ⟨z.getD (2 * c) 0, z.getD (2 * c + 1) 0⟩

/-- The exact twiddle table of a pass `(R, ns)` of a plan of size `N`, in the layout of
`passTwiddles`: for `1 ≤ r < R` and `k < ns`, entry `2(r-1)·ns + k` is the real part and
entry `(2(r-1)+1)·ns + k` the imaginary part of `ω_N^{r·k·N/(ns·R)}`. -/
noncomputable def exactTw (fwd : Bool) (N R ns : ℕ) : Array ℝ :=
  (Array.range (2 * (R - 1) * ns)).map fun i =>
    let w := twiddle fwd N ((i / (2 * ns) + 1) * (i % ns) * (N / (ns * R)))
    if i / ns % 2 = 0 then w.re else w.im

/-- **The Stockham invariant** for `ns`: position `b·ns + k` holds the length-`ns` DFT of
the subsequence `m ↦ x (b + (N/ns)·m)` at frequency `k`. -/
def StockInv (fwd : Bool) (N ns : ℕ) (x : ℕ → ℂ) (z : Array ℝ) : Prop :=
  z.size = 2 * N ∧ ∀ b k, b < N / ns → k < ns →
    cx z (b * ns + k) = dftSum fwd ns (fun m => x (b + N / ns * m)) k

/-! ### Arrays built by pushing pairs -/

section Push2

variable {α : Type} (f g : ℕ → α)

theorem getD_push_lt (a : Array α) (u d : α) {i : ℕ} (h : i < a.size) :
    (a.push u).getD i d = a.getD i d := by
  simp [Array.getD, Array.getElem_push, h, Nat.lt_succ_of_lt h]

theorem getD_push_eq (a : Array α) (u d : α) : (a.push u).getD a.size d = u := by
  simp [Array.getD]

theorem foldl_push2_size (acc : Array α) (n : ℕ) :
    ((List.range n).foldl (fun acc r => (acc.push (f r)).push (g r)) acc).size =
      acc.size + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp [ih]; omega

theorem foldl_push2_getD_lt (acc : Array α) (n : ℕ) (d : α) {i : ℕ} (hi : i < acc.size) :
    ((List.range n).foldl (fun acc r => (acc.push (f r)).push (g r)) acc).getD i d =
      acc.getD i d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      getD_push_lt _ _ _ (by simp [foldl_push2_size]; omega),
      getD_push_lt _ _ _ (by simp [foldl_push2_size]; omega), ih]

theorem foldl_push2_getD_fst (acc : Array α) (n : ℕ) (d : α) {r : ℕ} (hr : r < n) :
    ((List.range n).foldl (fun acc r => (acc.push (f r)).push (g r)) acc).getD
      (acc.size + 2 * r) d = f r := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | rfl
    · rw [getD_push_lt _ _ _ (by simp [foldl_push2_size]; omega),
        getD_push_lt _ _ _ (by simp [foldl_push2_size]; omega), ih h]
    · rw [getD_push_lt _ _ _ (by simp [foldl_push2_size]),
        show acc.size + 2 * r = ((List.range r).foldl (fun acc r => (acc.push (f r)).push (g r)) acc).size
          by simp [foldl_push2_size], getD_push_eq]

theorem foldl_push2_getD_snd (acc : Array α) (n : ℕ) (d : α) {r : ℕ} (hr : r < n) :
    ((List.range n).foldl (fun acc r => (acc.push (f r)).push (g r)) acc).getD
      (acc.size + 2 * r + 1) d = g r := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | rfl
    · rw [getD_push_lt _ _ _ (by simp [foldl_push2_size]; omega),
        getD_push_lt _ _ _ (by simp [foldl_push2_size]; omega), ih h]
    · rw [show acc.size + 2 * r + 1 = (((List.range r).foldl (fun acc r => (acc.push (f r)).push (g r)) acc).push (f r)).size
          by simp [foldl_push2_size], getD_push_eq]

end Push2

theorem foldl_push2_getD_fst0 {α : Type} (f g : ℕ → α) (n : ℕ) (d : α) {r : ℕ} (hr : r < n) :
    ((List.range n).foldl (fun acc r => (acc.push (f r)).push (g r)) #[]).getD (2 * r) d = f r := by
  simpa using foldl_push2_getD_fst f g #[] n d hr

theorem foldl_push2_getD_snd0 {α : Type} (f g : ℕ → α) (n : ℕ) (d : α) {r : ℕ} (hr : r < n) :
    ((List.range n).foldl (fun acc r => (acc.push (f r)).push (g r)) #[]).getD (2 * r + 1) d =
      g r := by
  simpa using foldl_push2_getD_snd f g #[] n d hr

theorem getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  simp [Array.getD, hi]

/-! ### Exact twiddle tables -/

theorem twiddle_zero_exp (fwd : Bool) (n : ℕ) : twiddle fwd n 0 = 1 := by simp [twiddle]

theorem exactTw_bound {R ns q kk : ℕ} (hq : q + 1 < R) (hk : kk < ns) :
    (2 * q + 1) * ns + kk < 2 * (R - 1) * ns := by
  have h1 : (2 * q + 2) * ns ≤ 2 * (R - 1) * ns := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem exactTw_getD_re (fwd : Bool) {N R ns q kk : ℕ} (hq : q + 1 < R) (hk : kk < ns) :
    (exactTw fwd N R ns).getD (2 * q * ns + kk) 0 =
      (twiddle fwd N ((q + 1) * kk * (N / (ns * R)))).re := by
  have hns : 0 < ns := by omega
  have hb := exactTw_bound (R := R) hq hk
  rw [exactTw, getD_map_range _ _ _ (by nlinarith)]
  have e1 : (2 * q * ns + kk) / (2 * ns) = q := by
    rw [show 2 * q * ns + kk = kk + q * (2 * ns) by ring, Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  have e2 : (2 * q * ns + kk) % ns = kk := by
    rw [show 2 * q * ns + kk = kk + (2 * q) * ns by ring, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hk]
  have e3 : (2 * q * ns + kk) / ns = 2 * q := by
    rw [show 2 * q * ns + kk = kk + (2 * q) * ns by ring, Nat.add_mul_div_right _ _ hns,
      Nat.div_eq_of_lt hk, zero_add]
  simp only [e1, e2, e3, Nat.mul_mod_right, ite_true]

theorem exactTw_getD_im (fwd : Bool) {N R ns q kk : ℕ} (hq : q + 1 < R) (hk : kk < ns) :
    (exactTw fwd N R ns).getD ((2 * q + 1) * ns + kk) 0 =
      (twiddle fwd N ((q + 1) * kk * (N / (ns * R)))).im := by
  have hns : 0 < ns := by omega
  have hb := exactTw_bound (R := R) hq hk
  rw [exactTw, getD_map_range _ _ _ hb]
  have e1 : ((2 * q + 1) * ns + kk) / (2 * ns) = q := by
    rw [show (2 * q + 1) * ns + kk = (kk + ns) + q * (2 * ns) by ring,
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have e2 : ((2 * q + 1) * ns + kk) % ns = kk := by
    rw [show (2 * q + 1) * ns + kk = kk + (2 * q + 1) * ns by ring, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hk]
  have e3 : ((2 * q + 1) * ns + kk) / ns = 2 * q + 1 := by
    rw [show (2 * q + 1) * ns + kk = kk + (2 * q + 1) * ns by ring,
      Nat.add_mul_div_right _ _ hns, Nat.div_eq_of_lt hk, zero_add]
  have e4 : (2 * q + 1) % 2 = 1 := by omega
  simp only [e1, e2, e3, e4, one_ne_zero, ite_false]

theorem twiddle_pass (fwd : Bool) {N R ns M : ℕ} (hM : 0 < M) (hN : N = M * (ns * R)) (a : ℕ) :
    twiddle fwd N (a * (N / (ns * R))) = twiddle fwd (ns * R) a := by
  rcases Nat.eq_zero_or_pos (ns * R) with h | h
  · rw [h, mul_zero] at hN; subst hN; simp [h, twiddle]
  rw [hN, Nat.mul_div_cancel _ h, mul_comm a M, twiddle_scale fwd hM]


/-! ### One pass -/

/-- The butterfly inputs of a pass, as complex numbers with their twiddles. -/
theorem bflyX_bflyInputs (fwd tw : Bool) {N R ns M : ℕ} (hR : 0 < R) (hns : 0 < ns) (hM : 0 < M)
    (hN : N = M * (ns * R)) (hTw : tw = false → ns = 1) (z : Array ℝ) {j r : ℕ} (hr : r < R) :
    bflyX R tw (fun i => (bflyInputs R ns N (if tw then some (exactTw fwd N R ns) else none)
      z j).getD i 0) r = twiddle fwd (ns * R) (r * (j % ns)) * cx z (j + r * (N / R)) := by
  cases tw
  · simp only [bflyInputs, bflyX, Bool.false_eq_true, ite_false, Bool.false_and]
    rw [foldl_push2_getD_fst0 _ _ _ _ hr, foldl_push2_getD_snd0 _ _ _ _ hr, hTw rfl, Nat.mod_one,
      mul_zero, twiddle_zero_exp]
    rfl
  · simp only [bflyInputs, bflyX, ite_true, Bool.true_and]
    set xs := List.foldl (fun acc r => (acc.push (z.getD (2 * (j + r * (N / R))) default)).push
      (z.getD (2 * (j + r * (N / R)) + 1) default)) #[] (List.range R) with hxs
    have hxsz : xs.size = 2 * R := by rw [hxs, foldl_push2_size]; simp
    rw [foldl_push2_getD_lt _ _ xs _ _ (show 2 * r < xs.size by omega),
      foldl_push2_getD_lt _ _ xs _ _ (show 2 * r + 1 < xs.size by omega)]
    rcases Nat.eq_zero_or_pos r with h0 | h1
    · subst h0
      rw [hxs, foldl_push2_getD_fst0 _ _ _ _ hr, foldl_push2_getD_snd0 _ _ _ _ hr]
      simp only [ge_iff_le, Nat.le_zero, one_ne_zero, decide_false, Bool.false_eq_true, ite_false,
        zero_mul, twiddle_zero_exp, one_mul]
      rfl
    · have hd : decide (r ≥ 1) = true := decide_eq_true (show r ≥ 1 from h1)
      simp only [hd, ↓reduceIte]
      rw [show 2 * R + 2 * (r - 1) = xs.size + 2 * (r - 1) by omega,
        foldl_push2_getD_fst _ _ xs _ _ (show r - 1 < R - 1 by omega),
        foldl_push2_getD_snd _ _ xs _ _ (show r - 1 < R - 1 by omega), hxs,
        foldl_push2_getD_fst0 _ _ _ _ hr, foldl_push2_getD_snd0 _ _ _ _ hr]
      have hk : j % ns < ns := Nat.mod_lt _ hns
      have hq : r - 1 + 1 < R := by omega
      have h2 : (default : ℝ) = 0 := rfl
      rw [h2, exactTw_getD_re fwd hq hk, exactTw_getD_im fwd hq hk, Nat.sub_add_cancel h1,
        twiddle_pass fwd hM hN]
      rfl

theorem bflyInputs_size (fwd tw : Bool) (N R ns : ℕ) (hR : 0 < R) (z : Array ℝ) (j : ℕ) :
    (bflyInputs R ns N (if tw then some (exactTw fwd N R ns) else none) z j).size =
      butterflyInputs R tw := by
  cases tw <;> simp only [bflyInputs, butterflyInputs, Bool.false_eq_true, ite_false, ite_true] <;>
    simp only [foldl_push2_size, Array.size_empty] <;> omega

/-- The entries of a pass: position `c = b·ns·R + k + r·ns` holds output `r` of butterfly
`j = b·ns + k`, which by `butterflyK_correct` is a length-`R` DFT. -/
theorem passWith_getD (fwd tw : Bool) {N R ns M : ℕ} (hR : 0 < R) (hns : 0 < ns)
    (hN : N = M * (ns * R)) (z : Array ℝ) {b kk r p : ℕ} (hb : b < M) (hk : kk < ns)
    (hr : r < R) (hp : p < 2) :
    (passWith realArith (butterflyK fwd R tw) R ns N
        (if tw then some (exactTw fwd N R ns) else none) z).getD
        (2 * (b * (ns * R) + kk + r * ns) + p) 0 =
      let y := dftSum fwd R (bflyX R tw fun i => (bflyInputs R ns N
        (if tw then some (exactTw fwd N R ns) else none) z (b * ns + kk)).getD i 0) r
      if p = 0 then y.re else y.im := by
  have hkr : kk + r * ns < ns * R := by nlinarith
  have hcN : b * (ns * R) + kk + r * ns < N := by rw [hN]; nlinarith
  have h1 : (b * (ns * R) + kk + r * ns) % ns = kk := by
    rw [show b * (ns * R) + kk + r * ns = kk + (b * R + r) * ns by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have h2 : (b * (ns * R) + kk + r * ns) / ns % R = r := by
    rw [show b * (ns * R) + kk + r * ns = kk + (b * R + r) * ns by ring,
      Nat.add_mul_div_right _ _ hns, Nat.div_eq_of_lt hk, zero_add,
      show b * R + r = r + b * R by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have h3 : (b * (ns * R) + kk + r * ns) / (ns * R) = b := by
    rw [show b * (ns * R) + kk + r * ns = (kk + r * ns) + b * (ns * R) by ring,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hkr, zero_add]
  have hNR : N / R = M * ns := by
    rw [hN, show M * (ns * R) = M * ns * R by ring, Nat.mul_div_cancel _ hR]
  have hj : b * ns + kk < N / R := by rw [hNR]; nlinarith
  simp only [passWith]
  rw [getD_map_range _ _ _ (by omega)]
  simp only [show (2 * (b * (ns * R) + kk + r * ns) + p) / 2 = b * (ns * R) + kk + r * ns by omega,
    show (2 * (b * (ns * R) + kk + r * ns) + p) % 2 = p by omega, h1, h2, h3]
  rw [getD_map_range _ _ _ hj, butterflyK_correct fwd hR tw _ (bflyInputs_size fwd tw N R ns hR z _),
    getD_map_range _ _ _ (by omega)]
  simp only [show (2 * r + p) / 2 = r by omega, show (2 * r + p) % 2 = p by omega]

/-- **One Stockham pass.** If the data satisfy the invariant for `ns`, a radix-`R` pass
(twiddled, with the exact table, unless `ns = 1`) establishes the invariant for `ns·R`. -/
theorem stockInv_pass (fwd tw : Bool) {N R ns M : ℕ} (hR : 0 < R) (hns : 0 < ns) (hM : 0 < M)
    (hN : N = M * (ns * R)) (hTw : tw = false → ns = 1) {x : ℕ → ℂ} {z : Array ℝ}
    (hz : StockInv fwd N ns x z) :
    StockInv fwd N (ns * R) x
      (passWith realArith (butterflyK fwd R tw) R ns N
        (if tw then some (exactTw fwd N R ns) else none) z) := by
  obtain ⟨-, hinv⟩ := hz
  refine ⟨by simp [passWith], ?_⟩
  intro b k' hb hk'
  have hM' : N / (ns * R) = M := by rw [hN, Nat.mul_div_cancel _ (by positivity)]
  have hNns : N / ns = M * R := by
    rw [hN, show M * (ns * R) = M * R * ns by ring, Nat.mul_div_cancel _ hns]
  have hNR : N / R = M * ns := by
    rw [hN, show M * (ns * R) = M * ns * R by ring, Nat.mul_div_cancel _ hR]
  rw [hM'] at hb ⊢
  have hkk : k' % ns < ns := Nat.mod_lt _ hns
  have hr : k' / ns < R := Nat.div_lt_of_lt_mul hk'
  have hk'eq : k' = k' % ns + k' / ns * ns := by
    have := Nat.mod_add_div k' ns; linarith [mul_comm ns (k' / ns)]
  have e0 := passWith_getD fwd tw hR hns hN z hb hkk hr (p := 0) (by norm_num)
  have e1 := passWith_getD fwd tw hR hns hN z hb hkk hr (p := 1) (by norm_num)
  simp only [Nat.add_zero, ↓reduceIte, one_ne_zero] at e0 e1
  have hY : dftSum fwd R (bflyX R tw fun i => (bflyInputs R ns N
      (if tw then some (exactTw fwd N R ns) else none) z (b * ns + k' % ns)).getD i 0) (k' / ns) =
      dftSum fwd (ns * R) (fun m => x (b + M * m)) k' := by
    rw [mul_comm ns R, dftSum_ct fwd hR hns, dftSum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq : q < R := Finset.mem_range.mp hq
    have hmod : (b * ns + k' % ns) % ns = k' % ns := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hkk]
    rw [bflyX_bflyInputs fwd tw hR hns hM hN hTw z hq, hNR, hmod,
      show b * ns + k' % ns + q * (M * ns) = (b + q * M) * ns + k' % ns by ring,
      hinv _ _ (by rw [hNns]; nlinarith) hkk, hNns]
    have hf : (fun j2 => x (b + M * (q + R * j2))) = (fun m => x (b + q * M + M * R * m)) := by
      funext m; congr 1; ring
    have htw : twiddle fwd (R * ns) (q * k') =
        twiddle fwd (ns * R) (q * (k' % ns)) * twiddle fwd R (q * (k' / ns)) := by
      conv_lhs => rw [hk'eq]
      rw [show q * (k' % ns + k' / ns * ns) = q * (k' % ns) + ns * (q * (k' / ns)) by ring,
        twiddle_add, mul_comm R ns, twiddle_scale fwd hns]
    rw [hf, htw]
    ring
  have hc : b * (ns * R) + k' = b * (ns * R) + k' % ns + k' / ns * ns := by omega
  rw [cx, hc, e0, e1, ← hY]

/-! ### The whole schedule -/

theorem passNs_eq (rs : Array ℕ) (t : ℕ) : passNs rs t = (rs.toList.take t).prod := by
  rw [passNs, ← Array.foldl_toList, List.prod_eq_foldl]
  simp

theorem stockhamWith_eq_foldl {α : Type} [Inhabited α] (A : Arith α) (fwd : Bool) (N : ℕ)
    (rs : Array ℕ) (twOf : ℕ → Array α) (z : Array α) :
    stockhamWith A fwd N rs twOf z =
      (List.range rs.size).foldl (fun z t => passWith A (butterflyK fwd (rs.getD t 1) (t ≥ 1))
        (rs.getD t 1) (passNs rs t) N (if t ≥ 1 then some (twOf t) else none) z) z := by
  simp only [stockhamWith, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, List.range_eq_range']
  simp

/-- The exact twiddle tables of a plan. -/
noncomputable def exactTwOf (fwd : Bool) (N : ℕ) (rs : Array ℕ) (t : ℕ) : Array ℝ :=
  exactTw fwd N (rs.getD t 1) (passNs rs t)

/-- **The Stockham schedule computes the DFT.** Over exact real arithmetic with the exact
twiddle tables, the passes of the plan `rs` (positive radices, `N = R₀ ⋯ R_{s-1}`) map
interleaved data `z` to the interleaved DFT (sign `fwd`) of the complex numbers it holds. -/
theorem stockhamWith_exact (fwd : Bool) (rs : Array ℕ) (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ)
    (hN : N = rs.toList.prod) (z : Array ℝ) (hz : z.size = 2 * N) :
    stockhamWith realArith fwd N rs (exactTwOf fwd N rs) z =
      (Array.range (2 * N)).map fun i =>
        let y := dftSum fwd N (fun j => ⟨z.getD (2 * j) 0, z.getD (2 * j + 1) 0⟩) (i / 2)
        if i % 2 = 0 then y.re else y.im := by
  set L := rs.toList with hL
  have hpos : ∀ r ∈ L, 0 < r := fun r hr => hrs r (by simpa [hL] using hr)
  have hNpos : 0 < N := hN ▸ List.prod_pos hpos
  set x : ℕ → ℂ := fun j => ⟨z.getD (2 * j) 0, z.getD (2 * j + 1) 0⟩ with hx
  have inv : ∀ t ≤ rs.size, StockInv fwd N (passNs rs t) x ((List.range t).foldl
      (fun z t => passWith realArith (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1)
        (passNs rs t) N (if t ≥ 1 then some (exactTwOf fwd N rs t) else none) z) z) := by
    intro t ht
    induction t with
    | zero =>
      have h0 : passNs rs 0 = 1 := by simp [passNs_eq]
      rw [h0]
      refine ⟨hz, fun b k _ hk => ?_⟩
      have : k = 0 := by omega
      subst this
      simp [dftSum, twiddle_zero_exp, cx, x]
    | succ t ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ht' : t < rs.size := ht
      have hLt : t < L.length := by simpa [hL] using ht'
      have hget : rs.getD t 1 = L[t] := by simp [hL, Array.getD, ht']
      have hR : 0 < rs.getD t 1 := by rw [hget]; exact hpos _ (List.getElem_mem hLt)
      have hns : 0 < passNs rs t := by
        rw [passNs_eq]; exact List.prod_pos fun r hr => hpos r (List.mem_of_mem_take hr)
      have hM : 0 < (L.drop (t + 1)).prod :=
        List.prod_pos fun r hr => hpos r (List.mem_of_mem_drop hr)
      have hsucc : passNs rs (t + 1) = passNs rs t * rs.getD t 1 := by
        rw [passNs_eq, passNs_eq, ← hL, List.prod_take_succ _ _ hLt, hget]
      have hN' : N = (L.drop (t + 1)).prod * (passNs rs t * rs.getD t 1) := by
        rw [← hsucc, passNs_eq, ← hL, mul_comm, List.prod_take_mul_prod_drop, hN]
      have hTw : decide (t ≥ 1) = false → passNs rs t = 1 := by
        intro h
        have : t = 0 := by simpa using h
        subst this
        simp [passNs_eq]
      have h := stockInv_pass fwd (decide (t ≥ 1)) hR hns hM hN' hTw (ih (by omega))
      have e : (if t ≥ 1 then some (exactTwOf fwd N rs t) else none) =
          (if decide (t ≥ 1) = true then some (exactTw fwd N (rs.getD t 1) (passNs rs t))
            else none) := by simp [exactTwOf]
      rw [hsucc, e]
      exact h
  have hfin := inv rs.size le_rfl
  have hsN : passNs rs rs.size = N := by
    rw [passNs_eq, hN, hL, List.take_of_length_le (by simp)]
  rw [hsN] at hfin
  obtain ⟨hsz, hval⟩ := hfin
  rw [stockhamWith_eq_foldl]
  set out := (List.range rs.size).foldl
      (fun z t => passWith realArith (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1)
        (passNs rs t) N (if t ≥ 1 then some (exactTwOf fwd N rs t) else none) z) z
  have key : ∀ c < N, cx out c = dftSum fwd N x c := by
    intro c hc
    have := hval 0 c (by rw [Nat.div_self hNpos]; norm_num) hc
    simpa [Nat.div_self hNpos] using this
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have hc := key (i / 2) (by omega)
    have hre := congrArg Complex.re hc
    have him := congrArg Complex.im hc
    simp only [cx] at hre him
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · simp only [h, ↓reduceIte]
      rw [← hre, show 2 * (i / 2) = i by omega]
      simp [Array.getD, h1]
    · simp only [h, one_ne_zero, ↓reduceIte]
      rw [← him, show 2 * (i / 2) + 1 = i by omega]
      simp [Array.getD, h1]

end LeanFFTW.Gen
