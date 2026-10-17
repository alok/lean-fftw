/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.FloatOps

/-!
# A fast executor for the binary64 generic engine, proved equal to the spec

`execFloat p x = exec floatOps p x` is the generic algorithm of `Alg.lean` run on binary64
values. As written it is slow when compiled: every complex value is a heap-allocated `FC`,
every sum goes through closures, and the input of a sub-transform is a view that composes
one closure per Cooley–Tukey level.

`execFloatFast` computes the same function with array indexing and unboxed loops: the input
is materialized once, a sub-transform reads it at an offset and stride, and each output
is one tail-recursive loop over `Float` accumulators. It performs the same binary64
operations in the same order (the same products `w·x`, summed left to right from `0`), so
the results are bit-identical, and `execFloat_eq_fast` proves the two functions equal.
`@[csimp]` then makes the compiler run `execFloatFast` wherever `execFloat` is called.
-/

namespace LeanFFTW

/-- The binary64 generic engine (the specification of `execFloatFast`). -/
def execFloat (p : Plan CArr) (x : Nat → FC) : CArr := exec floatOps p x

namespace Fast

/-- `⟨ar, ai⟩ + Σ_{i ≤ j < i + c} w[(j·k) % n] · X[off + st·j]`, summed left to right. -/
def dotDirect (w X : CArr) (n k off st : Nat) : (c i : Nat) → (ar ai : Float) → FC
  | 0, _, ar, ai => ⟨ar, ai⟩
  | c + 1, i, ar, ai =>
      let t := i * k % n
      let wr := w.re.get! t
      let wi := w.im.get! t
      let q := off + st * i
      let xr := X.re.get! q
      let xi := X.im.get! q
      dotDirect w X n k off st c (i + 1) (ar + (wr * xr - wi * xi)) (ai + (wr * xi + wi * xr))

/-- `⟨ar, ai⟩ + Σ_{i ≤ j < i + c} w[(j·k) % n] · ys[j][k % m]`, summed left to right. -/
def dotCt (w : CArr) (ys : Array CArr) (n m k : Nat) : (c i : Nat) → (ar ai : Float) → FC
  | 0, _, ar, ai => ⟨ar, ai⟩
  | c + 1, i, ar, ai =>
      let t := i * k % n
      let wr := w.re.get! t
      let wi := w.im.get! t
      let y := ys.getD i default
      let q := k % m
      let yr := y.re.get! q
      let yi := y.im.get! q
      dotCt w ys n m k c (i + 1) (ar + (wr * yr - wi * yi)) (ai + (wr * yi + wi * yr))

/-- `exec floatOps p` on the view `j ↦ X[off + st·j]`. -/
def execArr : Plan CArr → CArr → Nat → Nat → CArr
  | .direct n w, X, off, st => CArr.ofFn n fun k => dotDirect w X n k off st n 0 0.0 0.0
  | .ct r w sub, X, off, st =>
      let m := sub.size
      let n := r * m
      let ys := (Array.range r).map fun j1 => execArr sub X (off + st * j1) (st * r)
      CArr.ofFn n fun k => dotCt w ys n m k r 0 0.0 0.0

end Fast

/-- The fast executor: materialize the input, then run `Fast.execArr`. -/
def execFloatFast (p : Plan CArr) (x : Nat → FC) : CArr :=
  Fast.execArr p (CArr.ofFn p.size x) 0 1

/-! ## Proof of equality -/

namespace Fast

/-- The left fold that `sumRange` computes, stepped forward from `i` for `c` terms. -/
def foldFrom (f : Nat → FC) : (c i : Nat) → FC → FC
  | 0, _, acc => acc
  | c + 1, i, acc => foldFrom f c (i + 1) (floatOps.add acc (f i))

theorem fold_eq_foldFrom (f : Nat → FC) (z : FC) :
    ∀ c i, Nat.fold (i + c) (fun j _ acc => floatOps.add acc (f j)) z =
      foldFrom f c i (Nat.fold i (fun j _ acc => floatOps.add acc (f j)) z)
  | 0, i => rfl
  | c + 1, i => by
    rw [show i + (c + 1) = (i + 1) + c by omega, fold_eq_foldFrom f z c (i + 1), Nat.fold_succ]
    rfl

theorem sumRange_eq_foldFrom (f : Nat → FC) (n : Nat) :
    sumRange floatOps n f = foldFrom f n 0 ⟨0.0, 0.0⟩ := by
  have h := fold_eq_foldFrom f floatOps.zero n 0
  rw [Nat.zero_add] at h
  exact h

theorem dotDirect_eq (w X : CArr) (n k off st : Nat) :
    ∀ c i (ar ai : Float), dotDirect w X n k off st c i ar ai =
      foldFrom (fun j => FC.mul (w.get (j * k % n)) (X.get (off + st * j))) c i ⟨ar, ai⟩
  | 0, _, _, _ => rfl
  | c + 1, i, ar, ai => by
    rw [dotDirect, foldFrom, dotDirect_eq w X n k off st c (i + 1)]
    rfl

theorem dotCt_eq (w : CArr) (ys : Array CArr) (n m k : Nat) :
    ∀ c i (ar ai : Float), dotCt w ys n m k c i ar ai =
      foldFrom (fun j => FC.mul (w.get (j * k % n)) ((ys.getD j default).get (k % m))) c i
        ⟨ar, ai⟩
  | 0, _, _, _ => rfl
  | c + 1, i, ar, ai => by
    rw [dotCt, foldFrom, dotCt_eq w ys n m k c (i + 1)]
    rfl

/-- `execArr` is `exec floatOps` on a strided view of an array. -/
theorem execArr_eq : ∀ (p : Plan CArr) (X : CArr) (off st : Nat),
    execArr p X off st = exec floatOps p (fun j => X.get (off + st * j))
  | .direct n w, X, off, st => by
    simp only [execArr, exec]
    congr 1
    funext k
    rw [dotDirect_eq, sumRange_eq_foldFrom]
    rfl
  | .ct r w sub, X, off, st => by
    simp only [execArr, exec]
    have hys : ((Array.range r).map fun j1 => execArr sub X (off + st * j1) (st * r)) =
        (Array.range r).map fun j1 =>
          exec floatOps sub (fun j2 => X.get (off + st * (j1 + r * j2))) := by
      congr 1
      funext j1
      rw [execArr_eq sub X]
      congr 1
      funext j2
      rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    rw [hys]
    congr 1
    funext k
    rw [dotCt_eq, sumRange_eq_foldFrom]
    rfl

end Fast

/-! ### `exec` reads its input only below the transform size -/

theorem sumRange_congr' {C V : Type} (O : Ops C V) (n : Nat) (f g : Nat → C)
    (h : ∀ j < n, f j = g j) : sumRange O n f = sumRange O n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, Nat.fold_succ] at ih ⊢
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem exec_congr {C V : Type} [Inhabited V] (O : Ops C V) :
    ∀ (p : Plan V) (x y : Nat → C), (∀ j < p.size, x j = y j) → exec O p x = exec O p y
  | .direct n w, x, y, h => by
    simp only [exec]
    congr 1
    funext k
    exact sumRange_congr' O n _ _ fun j hj => by rw [h j hj]
  | .ct r w sub, x, y, h => by
    simp only [exec]
    have hys : ((Array.range r).map fun j1 => exec O sub (fun j2 => x (j1 + r * j2))) =
        (Array.range r).map fun j1 => exec O sub (fun j2 => y (j1 + r * j2)) := by
      apply Array.ext (by simp)
      intro i hi _
      simp only [Array.getElem_map, Array.getElem_range]
      simp only [Array.size_map, Array.size_range] at hi
      apply exec_congr O sub
      intro j2 hj2
      apply h
      simp only [Plan.size]
      have : r * j2 + r ≤ r * sub.size := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left r hj2
      omega
    rw [hys]

/-! ### Materializing a view -/

theorem floatArray_get!_push_lt (a : FloatArray) (v : Float) {i : Nat} (hi : i < a.size) :
    (a.push v).get! i = a.get! i := by
  cases a with
  | mk ds =>
    simp only [FloatArray.push, FloatArray.get!, FloatArray.size] at hi ⊢
    rw [getElem!_pos (ds.push v) i (by simp; omega), getElem!_pos ds i hi, Array.getElem_push_lt]

theorem floatArray_get!_push_eq (a : FloatArray) (v : Float) :
    (a.push v).get! a.size = v := by
  cases a with
  | mk ds =>
    simp only [FloatArray.push, FloatArray.get!, FloatArray.size]
    rw [getElem!_pos (ds.push v) ds.size (by simp), Array.getElem_push_eq]

/-- The step of the loop of `CArr.ofFn`. -/
def pushStep (f : Nat → FC) (b : FloatArray × FloatArray) (i : Nat) : FloatArray × FloatArray :=
  (b.1.push (f i).re, b.2.push (f i).im)

theorem floatArray_size_push (a : FloatArray) (v : Float) : (a.push v).size = a.size + 1 := by
  cases a; simp [FloatArray.push, FloatArray.size]

/-- The loop of `CArr.ofFn`, as a fold over a list of indices. -/
theorem ofFn_loop (f : Nat → FC) :
    ∀ (l : List Nat) (re im : FloatArray),
      (l.foldl (pushStep f) (re, im)).1.size = re.size + l.length ∧
      (l.foldl (pushStep f) (re, im)).2.size = im.size + l.length ∧
      (∀ j < re.size, (l.foldl (pushStep f) (re, im)).1.get! j = re.get! j) ∧
      (∀ j < im.size, (l.foldl (pushStep f) (re, im)).2.get! j = im.get! j) ∧
      (∀ t (ht : t < l.length), (l.foldl (pushStep f) (re, im)).1.get! (re.size + t) = (f l[t]).re ∧
        (l.foldl (pushStep f) (re, im)).2.get! (im.size + t) = (f l[t]).im)
  | [], re, im => by simp
  | i :: l, re, im => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := ofFn_loop f l (re.push (f i).re) (im.push (f i).im)
    have hs1 := floatArray_size_push re (f i).re
    have hs2 := floatArray_size_push im (f i).im
    simp only [List.foldl_cons, List.length_cons]
    rw [show pushStep f (re, im) i = (re.push (f i).re, im.push (f i).im) from rfl]
    refine ⟨by rw [h1, hs1]; omega, by rw [h2, hs2]; omega, ?_, ?_, ?_⟩
    · intro j hj
      rw [h3 j (by omega), floatArray_get!_push_lt _ _ hj]
    · intro j hj
      rw [h4 j (by omega), floatArray_get!_push_lt _ _ hj]
    · intro t ht
      cases t with
      | zero =>
        refine ⟨?_, ?_⟩
        · rw [Nat.add_zero, h3 re.size (by omega)]
          exact floatArray_get!_push_eq re _
        · rw [Nat.add_zero, h4 im.size (by omega)]
          exact floatArray_get!_push_eq im _
      | succ t =>
        have := h5 t (by omega)
        rw [hs1, hs2] at this
        simp only [List.getElem_cons_succ]
        rw [show re.size + (t + 1) = re.size + 1 + t by omega,
          show im.size + (t + 1) = im.size + 1 + t by omega]
        exact this

theorem CArr.get_ofFn (n : Nat) (f : Nat → FC) {j : Nat} (hj : j < n) :
    (CArr.ofFn n f).get j = f j := by
  simp only [CArr.ofFn, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Id.run]
  have hsz : [:n].size = n := by simp [Std.Legacy.Range.size]
  rw [hsz]
  obtain ⟨-, -, -, -, h5⟩ := ofFn_loop f (List.range' 0 n)
    (FloatArray.emptyWithCapacity n) (FloatArray.emptyWithCapacity n)
  have h0 : (FloatArray.emptyWithCapacity n).size = 0 := rfl
  have := h5 j (by simpa using hj)
  rw [h0, Nat.zero_add] at this
  simp only [List.getElem_range', Nat.zero_add, Nat.one_mul] at this
  show (⟨_, _⟩ : FC) = f j
  calc _ = (⟨(f j).re, (f j).im⟩ : FC) := by
        congr 1
        · exact this.1
        · exact this.2
    _ = f j := rfl

/-- **The fast executor computes the generic engine's function.** -/
@[csimp] theorem execFloat_eq_fast : @execFloat = @execFloatFast := by
  funext p x
  rw [execFloat, execFloatFast, Fast.execArr_eq]
  apply exec_congr
  intro j hj
  simp only [Nat.zero_add, Nat.one_mul]
  exact (CArr.get_ofFn _ _ hj).symm

end LeanFFTW
