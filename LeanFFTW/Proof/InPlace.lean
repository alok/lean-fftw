/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.InPlace
import LeanFFTW.Proof.Stockham

/-!
# The in-place schedule computes what the Stockham schedule computes

`inplaceWith_eq_stockhamWith`: for **every** arithmetic `A` (binary64, exact reals, symbolic
expressions, …), the in-place schedule of a plan returns exactly the array that the
Stockham schedule returns. The two schedules apply the same kernels to the same values; only
where values are stored differs, and the digit reversal `digitRev` relates the two layouts.

Proof: after `t` passes, position `β(b)·ns + k` of the in-place array holds the value at
position `b·ns + k` of the Stockham array, where `ns = R₀⋯R_{t-1}` and `β` reverses the
digits of `b` in the remaining radices `R_t, …, R_{s-1}` (`IPInv`). The leaf pass
establishes this for `t = 1`; each in-place pass preserves it, because
`β(b + r·m) = β'(b)·R + r` (`digitRev_cons_split`): butterfly `(β'(b), q)` of the in-place
pass reads the inputs that butterfly `b·ns + q` of the Stockham pass reads. After the last
pass no radices remain, `β = 0`, and the arrays are equal.

With `stockhamWith_exact`, the in-place schedule computes the DFT (`inplaceWith_exact`).
-/

namespace LeanFFTW.Gen

open LeanFFTW

theorem radixProd_eq (L : List ℕ) : radixProd L = L.prod := by
  rw [radixProd, List.prod_eq_foldl]

/-! ## Digit reversal -/

theorem digitRev_lt : ∀ (L : List ℕ), (∀ R ∈ L, 0 < R) → ∀ i, i < L.prod → digitRev L i < L.prod
  | [], _, _, _ => by simp [digitRev]
  | R :: L, hp, i, hi => by
    have hR : 0 < R := hp R (by simp)
    have hL : ∀ R ∈ L, 0 < R := fun r hr => hp r (by simp [hr])
    have hm : 0 < L.prod := List.prod_pos hL
    simp only [List.prod_cons] at hi ⊢
    simp only [digitRev, radixProd_eq]
    have h1 := digitRev_lt L hL (i % L.prod) (Nat.mod_lt _ hm)
    have h2 : i / L.prod < R := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
    nlinarith

theorem digitRevInv_digitRev : ∀ (L : List ℕ), (∀ R ∈ L, 0 < R) → ∀ i, i < L.prod →
    digitRevInv L (digitRev L i) = i
  | [], _, _, h => by simp at h; simp [digitRevInv, h]
  | R :: L, hp, i, hi => by
    have hR : 0 < R := hp R (by simp)
    have hL : ∀ R ∈ L, 0 < R := fun r hr => hp r (by simp [hr])
    have hm : 0 < L.prod := List.prod_pos hL
    simp only [List.prod_cons] at hi
    have h2 : i / L.prod < R := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
    simp only [digitRev, digitRevInv, radixProd_eq]
    rw [Nat.add_comm (digitRev L (i % L.prod) * R), Nat.add_mul_div_right _ _ hR,
      Nat.div_eq_of_lt h2, zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2,
      digitRevInv_digitRev L hL _ (Nat.mod_lt _ hm)]
    exact Nat.mod_add_div' i L.prod

/-- The step of the digit reversal that the in-place pass uses. -/
theorem digitRev_cons_split (R : ℕ) (L : List ℕ) {b r : ℕ} (hb : b < L.prod) :
    digitRev (R :: L) (b + r * L.prod) = digitRev L b * R + r := by
  have hm : 0 < L.prod := by omega
  simp only [digitRev, radixProd_eq]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb, Nat.add_mul_div_right _ _ hm,
    Nat.div_eq_of_lt hb, zero_add]

/-! ## Reading the passes -/

section Read

variable {α : Type} [Inhabited α]

/-- The common output layout of `passWith` and `ipPass`: position `b·ns·R + k + r·ns` holds
entry `2r + p` of butterfly `b·ns + k`. -/
theorem assemble_getD (bfs : Array (Array α)) {N R ns M : ℕ} (hR : 0 < R) (hns : 0 < ns)
    (hN : N = M * (ns * R)) {b kk r p : ℕ} (hb : b < M) (hk : kk < ns) (hr : r < R) (hp : p < 2) :
    ((Array.range (2 * N)).map fun i =>
        (bfs.getD (i / 2 / (ns * R) * ns + i / 2 % ns) #[]).getD (2 * (i / 2 / ns % R) + i % 2)
          default).getD (2 * (b * (ns * R) + kk + r * ns) + p) default =
      (bfs.getD (b * ns + kk) #[]).getD (2 * r + p) default := by
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
  rw [getD_map_range _ _ _ (by omega)]
  simp only [show (2 * (b * (ns * R) + kk + r * ns) + p) / 2 = b * (ns * R) + kk + r * ns by omega,
    show (2 * (b * (ns * R) + kk + r * ns) + p) % 2 = p by omega, h1, h2, h3]

theorem passWith_getD' (A : Arith α) (k : Kernel) {N R ns M : ℕ} (hR : 0 < R) (hns : 0 < ns)
    (hN : N = M * (ns * R)) (tw : Option (Array α)) (z : Array α) {b kk r p : ℕ} (hb : b < M)
    (hk : kk < ns) (hr : r < R) (hp : p < 2) :
    (passWith A k R ns N tw z).getD (2 * (b * (ns * R) + kk + r * ns) + p) default =
      (k.eval A (bflyInputs R ns N tw z (b * ns + kk))).getD (2 * r + p) default := by
  have hNR : N / R = M * ns := by
    rw [hN, show M * (ns * R) = M * ns * R by ring, Nat.mul_div_cancel _ hR]
  have hj : b * ns + kk < N / R := by rw [hNR]; nlinarith
  simp only [passWith]
  rw [assemble_getD _ hR hns hN hb hk hr hp, getD_map_range _ _ _ hj]

theorem ipPass_getD (A : Arith α) (k : Kernel) {N R ns M : ℕ} (hR : 0 < R) (hns : 0 < ns)
    (hN : N = M * (ns * R)) (tw : Option (Array α)) (y : Array α) {B kk r p : ℕ} (hB : B < M)
    (hk : kk < ns) (hr : r < R) (hp : p < 2) :
    (ipPass A k R ns N tw y).getD (2 * (B * (ns * R) + kk + r * ns) + p) default =
      (k.eval A (ipInputs R ns tw y (B * ns * R + kk) kk)).getD (2 * r + p) default := by
  have hNR : N / R = M * ns := by
    rw [hN, show M * (ns * R) = M * ns * R by ring, Nat.mul_div_cancel _ hR]
  have hj : B * ns + kk < N / R := by rw [hNR]; nlinarith
  have e1 : (B * ns + kk) / ns = B := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hns, Nat.div_eq_of_lt hk, zero_add]
  have e2 : (B * ns + kk) % ns = kk := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [ipPass]
  rw [assemble_getD _ hR hns hN hB hk hr hp, getD_map_range _ _ _ hj, e1, e2]

theorem ipLeaf_getD (A : Arith α) (k : Kernel) {N R : ℕ} (L : List ℕ) (hR : 0 < R)
    (hN : N = L.prod * R) (x : Array α) {P kk p : ℕ} (hP : P < L.prod) (hk : kk < R) (hp : p < 2) :
    (ipLeaf A k R N L x).getD (2 * (P * R + kk) + p) default =
      (k.eval A (bflyInputs R 1 N none x (digitRevInv L P))).getD (2 * kk + p) default := by
  have hNR : N / R = L.prod := by rw [hN, Nat.mul_div_cancel _ hR]
  have hc : P * R + kk < N := by rw [hN]; nlinarith
  have e1 : (P * R + kk) / R = P := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hk, zero_add]
  have e2 : (P * R + kk) % R = kk := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [ipLeaf]
  rw [getD_map_range _ _ _ (by omega)]
  simp only [show (2 * (P * R + kk) + p) / 2 = P * R + kk by omega,
    show (2 * (P * R + kk) + p) % 2 = p by omega, e1, e2]
  rw [getD_map_range _ _ _ (by omega)]

/-- **What the C leaf pass does.** Leaf `d` of the in-place schedule writes the outputs of the
DFT of `x[d + i·N/R]` at positions `leafOffsets[d] + r = digitRev L d · R + r`: the scatter
that the C executor performs with the table `leafOffsets`, read off the gather form of
`ipLeaf`. -/
theorem ipLeaf_scatter (A : Arith α) (k : Kernel) {N R : ℕ} (L : List ℕ) (hR : 0 < R)
    (hL : ∀ R ∈ L, 0 < R) (hN : N = L.prod * R) (x : Array α) {d r p : ℕ} (hd : d < L.prod)
    (hr : r < R) (hp : p < 2) :
    (ipLeaf A k R N L x).getD (2 * (digitRev L d * R + r) + p) default =
      (k.eval A (bflyInputs R 1 N none x d)).getD (2 * r + p) default := by
  rw [ipLeaf_getD A k L hR hN x (digitRev_lt L hL d hd) hr hp, digitRevInv_digitRev L hL d hd]

end Read

/-! ## The layout invariant -/

section Inv

variable {α : Type} [Inhabited α]

/-- After the passes with `ns = R₀⋯R_{t-1}` (remaining radices `L`), position
`β_L(b)·ns + k` of the in-place array `y` holds the entry of position `b·ns + k` of the
Stockham array `z`. -/
def IPInv (N ns : ℕ) (L : List ℕ) (y z : Array α) : Prop :=
  y.size = 2 * N ∧ z.size = 2 * N ∧ ∀ b k p, b < L.prod → k < ns → p < 2 →
    y.getD (2 * (digitRev L b * ns + k) + p) default = z.getD (2 * (b * ns + k) + p) default

theorem ipInputs_eq {N R ns : ℕ} {L : List ℕ} (hR : 0 < R)
    (hN : N = L.prod * (ns * R)) (tw : Option (Array α)) {y z : Array α}
    (hinv : IPInv N ns (R :: L) y z) {b kk : ℕ} (hb : b < L.prod) (hk : kk < ns) :
    ipInputs R ns tw y (digitRev L b * ns * R + kk) kk = bflyInputs R ns N tw z (b * ns + kk) := by
  obtain ⟨-, -, h⟩ := hinv
  have hNR : N / R = L.prod * ns := by
    rw [hN, show L.prod * (ns * R) = L.prod * ns * R by ring, Nat.mul_div_cancel _ hR]
  have hdata : ∀ r < R, ∀ p < 2,
      y.getD (2 * (digitRev L b * ns * R + kk + r * ns) + p) default =
        z.getD (2 * (b * ns + kk + r * (N / R)) + p) default := by
    intro r hr p hp
    have hb' : b + r * L.prod < (R :: L).prod := by
      simp only [List.prod_cons]; nlinarith
    have := h (b + r * L.prod) kk p hb' hk hp
    rw [digitRev_cons_split R L hb] at this
    rw [show digitRev L b * ns * R + kk + r * ns = (digitRev L b * R + r) * ns + kk by ring, this,
      hNR, show (b + r * L.prod) * ns + kk = b * ns + kk + r * (L.prod * ns) by ring]
  have hmod : (b * ns + kk) % ns = kk := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have hxs : (List.range R).foldl (fun acc r =>
      (acc.push (y.getD (2 * (digitRev L b * ns * R + kk + r * ns)) default)).push
        (y.getD (2 * (digitRev L b * ns * R + kk + r * ns) + 1) default)) #[] =
      (List.range R).foldl (fun acc r =>
      (acc.push (z.getD (2 * (b * ns + kk + r * (N / R))) default)).push
        (z.getD (2 * (b * ns + kk + r * (N / R)) + 1) default)) #[] := by
    apply List.foldl_ext
    intro acc r hr
    have hr' : r < R := List.mem_range.mp hr
    rw [show 2 * (digitRev L b * ns * R + kk + r * ns) = 2 * (digitRev L b * ns * R + kk + r * ns) + 0
      by ring, hdata r hr' 0 (by norm_num), hdata r hr' 1 (by norm_num)]
    simp
  cases tw with
  | none => simp only [ipInputs, bflyInputs]; exact hxs
  | some t => simp only [ipInputs, bflyInputs, hmod]; rw [hxs]

/-- **One in-place pass** preserves the invariant (with one radix fewer remaining). -/
theorem ipInv_pass (A : Arith α) (k : Kernel) {N R ns : ℕ} {L : List ℕ} (hR : 0 < R)
    (hns : 0 < ns) (hL : ∀ R ∈ L, 0 < R) (hN : N = L.prod * (ns * R)) (tw : Option (Array α))
    {y z : Array α} (hinv : IPInv N ns (R :: L) y z) :
    IPInv N (ns * R) L (ipPass A k R ns N tw y) (passWith A k R ns N tw z) := by
  refine ⟨by simp [ipPass], by simp [passWith], ?_⟩
  intro b k' p hb hk' hp
  have hBlt := digitRev_lt L hL b hb
  -- k' = kk + r·ns
  set kk := k' % ns with hkk
  set r := k' / ns with hr
  have hkk' : kk < ns := Nat.mod_lt _ hns
  have hr' : r < R := Nat.div_lt_of_lt_mul hk'
  have hk'eq : k' = kk + r * ns := by rw [hkk, hr]; exact (Nat.mod_add_div' k' ns).symm
  rw [show digitRev L b * (ns * R) + k' = digitRev L b * (ns * R) + kk + r * ns by omega,
    show b * (ns * R) + k' = b * (ns * R) + kk + r * ns by omega,
    ipPass_getD A k hR hns hN tw y hBlt hkk' hr' hp, passWith_getD' A k hR hns hN tw z hb hkk' hr' hp,
    ipInputs_eq hR hN tw hinv hb hkk']

/-- **The leaf pass** establishes the invariant after the first pass. -/
theorem ipInv_leaf (A : Arith α) (k : Kernel) {N R : ℕ} {L : List ℕ} (hR : 0 < R)
    (hL : ∀ R ∈ L, 0 < R) (hN : N = L.prod * R) (x : Array α) :
    IPInv N R L (ipLeaf A k R N L x) (passWith A k R 1 N none x) := by
  refine ⟨by simp [ipLeaf], by simp [passWith], ?_⟩
  intro b kk p hb hk hp
  have hBlt := digitRev_lt L hL b hb
  have hN1 : N = L.prod * (1 * R) := by rw [one_mul]; exact hN
  rw [ipLeaf_getD A k L hR hN x hBlt hk hp, digitRevInv_digitRev L hL b hb,
    show b * R + kk = b * (1 * R) + 0 + kk * 1 by ring,
    passWith_getD' A k hR Nat.one_pos hN1 none x hb Nat.one_pos hk hp]
  simp

/-- With no radices left, the invariant says the arrays are equal. -/
theorem ipInv_done {N : ℕ} {y z : Array α} (h : IPInv N N [] y z) : y = z := by
  obtain ⟨hy, hz, h⟩ := h
  apply Array.ext (by rw [hy, hz])
  intro i hi1 hi2
  have := h 0 (i / 2) (i % 2) (by simp) (by omega) (Nat.mod_lt _ (by norm_num))
  simp only [digitRev, zero_mul, zero_add] at this
  rw [show 2 * (i / 2) + i % 2 = i by omega] at this
  simpa [Array.getD, hi1, hi2] using this

end Inv

/-! ## The whole schedule -/

/-- **The in-place schedule equals the Stockham schedule**, for every arithmetic: for a plan
of positive radices with `N = R₀ ⋯ R_{s-1}`, `inplaceWith A = stockhamWith A` on data of
`2N` entries. -/
theorem inplaceWith_eq_stockhamWith {α : Type} [Inhabited α] (A : Arith α) (fwd : Bool)
    (rs : Array ℕ) (hne : 0 < rs.size) (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ) (hN : N = rs.toList.prod)
    (twOf : ℕ → Array α) (x : Array α) :
    inplaceWith A fwd N rs twOf x = stockhamWith A fwd N rs twOf x := by
  set L := rs.toList with hLdef
  have hpos : ∀ r ∈ L, 0 < r := fun r hr => hrs r (by simpa [hLdef] using hr)
  have hdrop : ∀ t, ∀ R ∈ L.drop t, 0 < R := fun t R hR => hpos R (List.mem_of_mem_drop hR)
  have hget : ∀ t (ht : t < rs.size), rs.getD t 1 = L[t]'(by simpa [hLdef] using ht) := by
    intro t ht; simp [hLdef, Array.getD, ht]
  have hNt : ∀ t, N = (L.drop t).prod * passNs rs t := by
    intro t
    rw [passNs_eq, ← hLdef, mul_comm, List.prod_take_mul_prod_drop, hN]
  have hsucc : ∀ t < rs.size, passNs rs (t + 1) = passNs rs t * rs.getD t 1 := by
    intro t ht
    rw [passNs_eq, passNs_eq, ← hLdef, List.prod_take_succ _ _ (by simpa [hLdef] using ht), hget t ht]
  have hdropcons : ∀ t < rs.size, L.drop t = rs.getD t 1 :: L.drop (t + 1) := by
    intro t ht
    rw [hget t ht]; exact List.drop_eq_getElem_cons _
  have hns : ∀ t, 0 < passNs rs t := by
    intro t; rw [passNs_eq]
    exact List.prod_pos fun r hr => hpos r (List.mem_of_mem_take hr)
  -- the invariant after the leaf and `u` more passes
  have key : ∀ u, u + 1 ≤ rs.size → IPInv N (passNs rs (u + 1)) (L.drop (u + 1))
      ((List.range u).foldl (fun y u =>
        ipPass A (butterflyK fwd (rs.getD (u + 1) 1) true) (rs.getD (u + 1) 1) (passNs rs (u + 1)) N
          (some (twOf (u + 1))) y)
        (ipLeaf A (butterflyK fwd (rs.getD 0 1) false) (rs.getD 0 1) N (L.drop 1) x))
      ((List.range (u + 1)).foldl (fun z t => passWith A (butterflyK fwd (rs.getD t 1) (t ≥ 1))
        (rs.getD t 1) (passNs rs t) N (if t ≥ 1 then some (twOf t) else none) z) x) := by
    intro u hu
    induction u with
    | zero =>
      have h1 : passNs rs 1 = rs.getD 0 1 := by rw [hsucc 0 hne]; simp [passNs]
      have hR : 0 < rs.getD 0 1 := by rw [← h1]; exact hns 1
      have hN0 : N = (L.drop 1).prod * rs.getD 0 1 := by rw [← h1]; exact hNt 1
      simp only [List.range_zero, List.foldl_nil]
      rw [h1]
      simpa [passNs] using ipInv_leaf A (butterflyK fwd (rs.getD 0 1) false) hR (hdrop 1) hN0 x
    | succ u ih =>
      have ih := ih (by omega)
      have ht : u + 1 < rs.size := by omega
      have hR : 0 < rs.getD (u + 1) 1 := by
        rw [hget _ ht]; exact hpos _ (List.getElem_mem _)
      rw [hdropcons (u + 1) ht] at ih
      have hN' : N = (L.drop (u + 2)).prod * (passNs rs (u + 1) * rs.getD (u + 1) 1) := by
        rw [← hsucc _ ht]; exact hNt (u + 2)
      have step := ipInv_pass A (butterflyK fwd (rs.getD (u + 1) 1) true) hR (hns (u + 1))
        (hdrop (u + 2)) hN' (some (twOf (u + 1))) ih
      rw [← hsucc _ ht] at step
      rw [List.range_succ (n := u), List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.range_succ (n := u + 1), List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hd : decide (u + 1 ≥ 1) = true := by simp
      simpa [hd] using step
  have hfin := key (rs.size - 1) (by omega)
  have hsN : passNs rs rs.size = N := by
    rw [passNs_eq, hN, hLdef, List.take_of_length_le (by simp)]
  have hdN : L.drop rs.size = [] := List.drop_of_length_le (by simp [hLdef])
  rw [show rs.size - 1 + 1 = rs.size by omega, hsN, hdN] at hfin
  rw [stockhamWith_eq_foldl]
  exact ipInv_done hfin

/-- Over the reals with the exact twiddles, the in-place schedule computes the DFT. -/
theorem inplaceWith_exact (fwd : Bool) (rs : Array ℕ) (hne : 0 < rs.size) (hrs : ∀ r ∈ rs, 0 < r)
    (N : ℕ) (hN : N = rs.toList.prod) (z : Array ℝ) (hz : z.size = 2 * N) :
    inplaceWith realArith fwd N rs (exactTwOf fwd N rs) z =
      (Array.range (2 * N)).map fun i =>
        let y := dftSum fwd N (fun j => ⟨z.getD (2 * j) 0, z.getD (2 * j + 1) 0⟩) (i / 2)
        if i % 2 = 0 then y.re else y.im := by
  rw [inplaceWith_eq_stockhamWith realArith fwd rs hne hrs N hN _ z,
    stockhamWith_exact fwd rs hrs N hN z hz]

end LeanFFTW.Gen
