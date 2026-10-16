/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Emit

/-!
# Correctness of common-subexpression elimination

`cse_correct`: evaluating the kernel `cse nIn outs` on inputs `inp` (over any `Arith`
whose commutative operations are commutative) gives exactly the values of the expressions
`outs`. Together with the symbolic correctness of the butterflies this shows that the
kernels the C code is printed from compute DFTs in exact arithmetic.
-/

namespace LeanFFTW.Gen

variable {α : Type} [Inhabited α] (A : Arith α)

set_option linter.unusedSectionVars false

/-- The commutativity laws CSE's operand ordering relies on. -/
structure Arith.Comm : Prop where
  add : ∀ a b, A.add a b = A.add b a
  mul : ∀ a b, A.mul a b = A.mul b a
  fma : ∀ a b c, A.fma a b c = A.fma b a c
  fms : ∀ a b c, A.fms a b c = A.fms b a c
  fnma : ∀ a b c, A.fnma a b c = A.fnma b a c

/-- All operands of an operation are below `n`. -/
def KOp.Bounded (n : Nat) : KOp → Prop
  | .cst _ => True
  | .zero => True
  | .add a b => a < n ∧ b < n
  | .sub a b => a < n ∧ b < n
  | .mul a b => a < n ∧ b < n
  | .neg a => a < n
  | .fma a b c => a < n ∧ b < n ∧ c < n
  | .fms a b c => a < n ∧ b < n ∧ c < n
  | .fnma a b c => a < n ∧ b < n ∧ c < n

/-- All inputs of an expression are below `n`. -/
def SExpr.InputsLt (n : Nat) : SExpr → Prop
  | .input i => i < n
  | .zero => True
  | .cst _ => True
  | .add a b => a.InputsLt n ∧ b.InputsLt n
  | .sub a b => a.InputsLt n ∧ b.InputsLt n
  | .mul a b => a.InputsLt n ∧ b.InputsLt n
  | .neg a => a.InputsLt n
  | .fma a b c => a.InputsLt n ∧ b.InputsLt n ∧ c.InputsLt n
  | .fms a b c => a.InputsLt n ∧ b.InputsLt n ∧ c.InputsLt n
  | .fnma a b c => a.InputsLt n ∧ b.InputsLt n ∧ c.InputsLt n

theorem KOp.Bounded.mono {op : KOp} {n m : Nat} (h : op.Bounded n) (hnm : n ≤ m) :
    op.Bounded m := by
  cases op <;> simp only [KOp.Bounded] at h ⊢ <;> omega

theorem KOp.eval_congr {op : KOp} {n : Nat} (h : op.Bounded n) {g g' : Nat → α}
    (hg : ∀ i < n, g i = g' i) : op.eval A g = op.eval A g' := by
  cases op <;> simp only [KOp.Bounded] at h <;> simp only [KOp.eval] <;>
    (try rw [hg _ h.1, hg _ h.2]) <;> (try rw [hg _ h]) <;>
    (try rw [hg _ h.1, hg _ h.2.1, hg _ h.2.2])

/-! ### Slot values -/

/-- Slot values of a list of operations over the initial values `env`. -/
def slotsL (env : Array α) (ops : List KOp) : Array α :=
  ops.foldl (fun env op => env.push (op.eval A fun i => env.getD i default)) env

theorem slotsL_append (env : Array α) (l m : List KOp) :
    slotsL A env (l ++ m) = slotsL A (slotsL A env l) m := by
  simp [slotsL, List.foldl_append]

theorem slotsL_size (env : Array α) (l : List KOp) : (slotsL A env l).size = env.size + l.length := by
  induction l generalizing env with
  | nil => simp [slotsL]
  | cons op l ih =>
    simp only [slotsL, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem slotsL_getD (env : Array α) (l : List KOp) (i : Nat) (hi : i < env.size) :
    (slotsL A env l).getD i default = env.getD i default := by
  induction l generalizing env with
  | nil => simp [slotsL]
  | cons op l ih =>
    simp only [slotsL, List.foldl_cons] at ih ⊢
    rw [ih _ (by simp; omega)]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, show i ≠ env.size by omega, ite_false]

theorem getD_push_size (a : Array α) (x : α) : (a.push x).getD a.size default = x := by
  simp [Array.getD]

theorem slotsL_single (env : Array α) (op : KOp) :
    slotsL A env [op] = env.push (op.eval A fun i => env.getD i default) := rfl

theorem slotsL_concat (env : Array α) (l : List KOp) (op : KOp) :
    (slotsL A env (l ++ [op])).getD (env.size + l.length) default =
      op.eval A fun i => (slotsL A env l).getD i default := by
  rw [slotsL_append, slotsL_single, ← slotsL_size A env l, getD_push_size]

/-! ### The CSE invariant -/

variable (nIn : Nat) (inp : Array α)

/-- Value of slot `v` in state `s`. -/
def val (s : CSEState) (v : Nat) : α := (slotsL A inp s.ops.toList).getD v default

/-- Every remembered operation is stored at a slot that holds its value. -/
def Inv (s : CSEState) : Prop :=
  ∀ (op : KOp) (v : Nat), s.map[op]? = some v →
    v < nIn + s.ops.size ∧ op.Bounded v ∧ val A inp s v = op.eval A (val A inp s)

/-- `s'` extends `s`: the operations of `s` are a prefix of those of `s'`. -/
def Ext (s s' : CSEState) : Prop := ∃ m, s'.ops.toList = s.ops.toList ++ m

variable {A nIn inp}

theorem Ext.refl (s : CSEState) : Ext s s := ⟨[], by simp⟩

theorem Ext.trans {s1 s2 s3 : CSEState} (h1 : Ext s1 s2) (h2 : Ext s2 s3) : Ext s1 s3 := by
  obtain ⟨m1, h1⟩ := h1
  obtain ⟨m2, h2⟩ := h2
  exact ⟨m1 ++ m2, by rw [h2, h1, List.append_assoc]⟩

theorem Ext.size_le {s s' : CSEState} (h : Ext s s') : s.ops.size ≤ s'.ops.size := by
  obtain ⟨m, h⟩ := h
  have := congrArg List.length h
  simp at this
  omega

theorem Ext.val_eq (hinp : inp.size = nIn) {s s' : CSEState} (h : Ext s s') {v : Nat}
    (hv : v < nIn + s.ops.size) : val A inp s' v = val A inp s v := by
  obtain ⟨m, h⟩ := h
  unfold val
  rw [h, slotsL_append, slotsL_getD]
  rw [slotsL_size]
  simp
  omega

theorem val_input (hinp : inp.size = nIn) (s : CSEState) {i : Nat} (hi : i < nIn) :
    val A inp s i = inp.getD i default := by
  unfold val
  rw [slotsL_getD]
  omega

theorem Inv.ext (hinp : inp.size = nIn) {s s' : CSEState} (hs : Inv A nIn inp s) (h : Ext s s')
    (hmap : ∀ (op : KOp) (v : Nat), s'.map[op]? = some v → s.map[op]? = some v) : Inv A nIn inp s' := by
  intro op v hv
  obtain ⟨h1, h2, h3⟩ := hs op v (hmap op v hv)
  refine ⟨by have := h.size_le; omega, h2, ?_⟩
  rw [Ext.val_eq hinp h h1, h3]
  refine KOp.eval_congr A h2 (fun i hi => ?_)
  rw [Ext.val_eq hinp h (by omega)]

/-- Specification of `node`. -/
theorem node_spec (hinp : inp.size = nIn) (op : KOp) (s : CSEState) (hs : Inv A nIn inp s)
    (hb : op.Bounded (nIn + s.ops.size)) :
    Inv A nIn inp (node nIn op s).2 ∧ Ext s (node nIn op s).2 ∧
      (node nIn op s).1 < nIn + (node nIn op s).2.ops.size ∧
      val A inp (node nIn op s).2 (node nIn op s).1 = op.eval A (val A inp (node nIn op s).2) := by
  unfold node
  split
  · next v hv =>
    obtain ⟨h1, _, h3⟩ := hs op v hv
    exact ⟨hs, Ext.refl s, h1, h3⟩
  · next hnone =>
    have hext : Ext s { map := s.map.insert op (nIn + s.ops.size), ops := s.ops.push op } :=
      ⟨[op], by simp⟩
    have hval : val A inp { map := s.map.insert op (nIn + s.ops.size), ops := s.ops.push op }
        (nIn + s.ops.size) = op.eval A (val A inp s) := by
      unfold val
      simp only [Array.toList_push]
      have := slotsL_concat A inp s.ops.toList op
      rw [hinp, Array.length_toList] at this
      exact this
    have hval' : op.eval A (val A inp s) = op.eval A
        (val A inp { map := s.map.insert op (nIn + s.ops.size), ops := s.ops.push op }) :=
      KOp.eval_congr A hb (fun i hi => (Ext.val_eq hinp hext hi).symm)
    refine ⟨?_, hext, by simp, by rw [hval, hval']⟩
    intro op' v hv
    simp only [Std.HashMap.getElem?_insert] at hv
    split at hv
    · next heq =>
      have heq : op = op' := by simpa using heq
      subst heq
      simp only [Option.some.injEq] at hv
      subst hv
      exact ⟨by simp, hb, by rw [hval, hval']⟩
    · obtain ⟨h1, h2, h3⟩ := hs op' v hv
      refine ⟨by simp; omega, h2, ?_⟩
      rw [Ext.val_eq hinp hext h1, h3]
      exact KOp.eval_congr A h2 (fun i hi => (Ext.val_eq hinp hext (by omega)).symm)

/-- Result of `cseExpr`: the invariant is kept, the state extended, and the returned slot
holds the value of the expression. -/
def CSEPost (A : Arith α) (nIn : Nat) (inp : Array α) (e : SExpr) (s : CSEState)
    (r : Nat × CSEState) : Prop :=
  Inv A nIn inp r.2 ∧ Ext s r.2 ∧ r.1 < nIn + r.2.ops.size ∧
    val A inp r.2 r.1 = e.evalWith A (fun i => inp.getD i default)

theorem ord2_eval_add (hA : A.Comm) (x y : Nat) (g : Nat → α) :
    (ord2 x y .add).eval A g = A.add (g x) (g y) := by
  unfold ord2; split <;> simp [KOp.eval, hA.add]

theorem ord2_eval_mul (hA : A.Comm) (x y : Nat) (g : Nat → α) :
    (ord2 x y .mul).eval A g = A.mul (g x) (g y) := by
  unfold ord2; split <;> simp [KOp.eval, hA.mul]

theorem ord2_eval_fma (hA : A.Comm) (x y z : Nat) (g : Nat → α) :
    (ord2 x y fun a b => .fma a b z).eval A g = A.fma (g x) (g y) (g z) := by
  unfold ord2; split <;> simp [KOp.eval, hA.fma]

theorem ord2_eval_fms (hA : A.Comm) (x y z : Nat) (g : Nat → α) :
    (ord2 x y fun a b => .fms a b z).eval A g = A.fms (g x) (g y) (g z) := by
  unfold ord2; split <;> simp [KOp.eval, hA.fms]

theorem ord2_eval_fnma (hA : A.Comm) (x y z : Nat) (g : Nat → α) :
    (ord2 x y fun a b => .fnma a b z).eval A g = A.fnma (g x) (g y) (g z) := by
  unfold ord2; split <;> simp [KOp.eval, hA.fnma]

theorem ord2_bounded2 (x y n : Nat) (f : Nat → Nat → KOp) (hf : ∀ a b, a < n → b < n → (f a b).Bounded n)
    (hx : x < n) (hy : y < n) : (ord2 x y f).Bounded n := by
  unfold ord2; split <;> exact hf _ _ (by assumption) (by assumption)

/-- Specification of `cseExpr`. -/
theorem cseExpr_spec (hA : A.Comm) (hinp : inp.size = nIn) :
    ∀ (e : SExpr) (s : CSEState), Inv A nIn inp s → e.InputsLt nIn →
      CSEPost A nIn inp e s (cseExpr nIn e s)
  | .input i, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    exact ⟨hs, Ext.refl s, by simp [cseExpr]; omega, by simp [cseExpr, SExpr.evalWith, val_input hinp s he]⟩
  | .zero, s, hs, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := node_spec hinp .zero s hs trivial
    exact ⟨h1, h2, h3, by simp only [cseExpr, h4, KOp.eval, SExpr.evalWith]⟩
  | .cst c, s, hs, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := node_spec hinp (.cst c) s hs trivial
    exact ⟨h1, h2, h3, by simp only [cseExpr, h4, KOp.eval, SExpr.evalWith]⟩
  | .neg a, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp (.neg (cseExpr nIn a s).1) _ a1 a3
    refine ⟨n1, a2.trans n2, n3, ?_⟩
    simp only [cseExpr, n4, KOp.eval, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 a3, a4]
  | .add a b, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he.1
    obtain ⟨b1, b2, b3, b4⟩ := cseExpr_spec hA hinp b _ a1 he.2
    have hb := ord2_bounded2 (cseExpr nIn a s).1 (cseExpr nIn b (cseExpr nIn a s).2).1
      (nIn + (cseExpr nIn b (cseExpr nIn a s).2).2.ops.size) .add (fun _ _ h1 h2 => ⟨h1, h2⟩)
      (by have := b2.size_le; omega) b3
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp _ _ b1 hb
    refine ⟨n1, a2.trans (b2.trans n2), n3, ?_⟩
    simp only [cseExpr, n4, ord2_eval_add hA, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 b3, b4, Ext.val_eq hinp (b2.trans n2) a3, a4]
  | .sub a b, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he.1
    obtain ⟨b1, b2, b3, b4⟩ := cseExpr_spec hA hinp b _ a1 he.2
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp
      (.sub (cseExpr nIn a s).1 (cseExpr nIn b (cseExpr nIn a s).2).1) _ b1
      ⟨by have := b2.size_le; omega, b3⟩
    refine ⟨n1, a2.trans (b2.trans n2), n3, ?_⟩
    simp only [cseExpr, n4, KOp.eval, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 b3, b4, Ext.val_eq hinp (b2.trans n2) a3, a4]
  | .mul a b, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he.1
    obtain ⟨b1, b2, b3, b4⟩ := cseExpr_spec hA hinp b _ a1 he.2
    have hb := ord2_bounded2 (cseExpr nIn a s).1 (cseExpr nIn b (cseExpr nIn a s).2).1
      (nIn + (cseExpr nIn b (cseExpr nIn a s).2).2.ops.size) .mul (fun _ _ h1 h2 => ⟨h1, h2⟩)
      (by have := b2.size_le; omega) b3
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp _ _ b1 hb
    refine ⟨n1, a2.trans (b2.trans n2), n3, ?_⟩
    simp only [cseExpr, n4, ord2_eval_mul hA, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 b3, b4, Ext.val_eq hinp (b2.trans n2) a3, a4]
  | .fma a b c, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he.1
    obtain ⟨b1, b2, b3, b4⟩ := cseExpr_spec hA hinp b _ a1 he.2.1
    obtain ⟨c1, c2, c3, c4⟩ := cseExpr_spec hA hinp c _ b1 he.2.2
    have hb := ord2_bounded2 (cseExpr nIn a s).1 (cseExpr nIn b (cseExpr nIn a s).2).1
      (nIn + (cseExpr nIn c (cseExpr nIn b (cseExpr nIn a s).2).2).2.ops.size)
      (fun x y => .fma x y (cseExpr nIn c (cseExpr nIn b (cseExpr nIn a s).2).2).1)
      (fun _ _ h1 h2 => ⟨h1, h2, c3⟩)
      (by have := b2.size_le; have := c2.size_le; omega) (by have := c2.size_le; omega)
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp _ _ c1 hb
    refine ⟨n1, a2.trans (b2.trans (c2.trans n2)), n3, ?_⟩
    simp only [cseExpr, n4, ord2_eval_fma hA, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 c3, c4, Ext.val_eq hinp (c2.trans n2) b3, b4,
      Ext.val_eq hinp (b2.trans (c2.trans n2)) a3, a4]
  | .fms a b c, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he.1
    obtain ⟨b1, b2, b3, b4⟩ := cseExpr_spec hA hinp b _ a1 he.2.1
    obtain ⟨c1, c2, c3, c4⟩ := cseExpr_spec hA hinp c _ b1 he.2.2
    have hb := ord2_bounded2 (cseExpr nIn a s).1 (cseExpr nIn b (cseExpr nIn a s).2).1
      (nIn + (cseExpr nIn c (cseExpr nIn b (cseExpr nIn a s).2).2).2.ops.size)
      (fun x y => .fms x y (cseExpr nIn c (cseExpr nIn b (cseExpr nIn a s).2).2).1)
      (fun _ _ h1 h2 => ⟨h1, h2, c3⟩)
      (by have := b2.size_le; have := c2.size_le; omega) (by have := c2.size_le; omega)
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp _ _ c1 hb
    refine ⟨n1, a2.trans (b2.trans (c2.trans n2)), n3, ?_⟩
    simp only [cseExpr, n4, ord2_eval_fms hA, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 c3, c4, Ext.val_eq hinp (c2.trans n2) b3, b4,
      Ext.val_eq hinp (b2.trans (c2.trans n2)) a3, a4]
  | .fnma a b c, s, hs, he => by
    simp only [SExpr.InputsLt] at he
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp a s hs he.1
    obtain ⟨b1, b2, b3, b4⟩ := cseExpr_spec hA hinp b _ a1 he.2.1
    obtain ⟨c1, c2, c3, c4⟩ := cseExpr_spec hA hinp c _ b1 he.2.2
    have hb := ord2_bounded2 (cseExpr nIn a s).1 (cseExpr nIn b (cseExpr nIn a s).2).1
      (nIn + (cseExpr nIn c (cseExpr nIn b (cseExpr nIn a s).2).2).2.ops.size)
      (fun x y => .fnma x y (cseExpr nIn c (cseExpr nIn b (cseExpr nIn a s).2).2).1)
      (fun _ _ h1 h2 => ⟨h1, h2, c3⟩)
      (by have := b2.size_le; have := c2.size_le; omega) (by have := c2.size_le; omega)
    obtain ⟨n1, n2, n3, n4⟩ := node_spec hinp _ _ c1 hb
    refine ⟨n1, a2.trans (b2.trans (c2.trans n2)), n3, ?_⟩
    simp only [cseExpr, n4, ord2_eval_fnma hA, SExpr.evalWith]
    rw [Ext.val_eq hinp n2 c3, c4, Ext.val_eq hinp (c2.trans n2) b3, b4,
      Ext.val_eq hinp (b2.trans (c2.trans n2)) a3, a4]

/-- Specification of `cseList`. -/
theorem cseList_spec (hA : A.Comm) (hinp : inp.size = nIn) :
    ∀ (es : List SExpr) (s : CSEState), Inv A nIn inp s → (∀ e ∈ es, e.InputsLt nIn) →
      Inv A nIn inp (cseList nIn es s).2 ∧ Ext s (cseList nIn es s).2 ∧
        (cseList nIn es s).1.length = es.length ∧
        ∀ i (hi : i < es.length), ∃ v, (cseList nIn es s).1[i]? = some v ∧
          val A inp (cseList nIn es s).2 v = es[i].evalWith A (fun i => inp.getD i default)
  | [], s, hs, _ => ⟨hs, Ext.refl s, rfl, fun i hi => by simp at hi⟩
  | e :: es, s, hs, he => by
    obtain ⟨a1, a2, a3, a4⟩ := cseExpr_spec hA hinp e s hs (he e (by simp))
    obtain ⟨l1, l2, l3, l4⟩ := cseList_spec hA hinp es _ a1 (fun e' h => he e' (by simp [h]))
    refine ⟨l1, a2.trans l2, by simp [cseList, l3], fun i hi => ?_⟩
    cases i with
    | zero =>
      refine ⟨(cseExpr nIn e s).1, by simp [cseList], ?_⟩
      simp only [cseList, List.getElem_cons_zero]
      rw [Ext.val_eq hinp l2 a3, a4]
    | succ i =>
      obtain ⟨v, hv1, hv2⟩ := l4 i (by simpa using hi)
      exact ⟨v, by simpa [cseList] using hv1, by simpa [cseList] using hv2⟩

theorem Inv.empty : Inv A nIn inp ({} : CSEState) := by
  intro op v hv
  simp at hv

/-- **CSE is correct**: the kernel computes the expressions. -/
theorem cse_correct (hA : A.Comm) (outs : Array SExpr) (hinp : inp.size = nIn)
    (hout : ∀ e ∈ outs, e.InputsLt nIn) :
    (cse nIn outs).eval A inp = outs.map (SExpr.evalWith A (fun i => inp.getD i default)) := by
  obtain ⟨_, _, hlen, hval⟩ := cseList_spec hA hinp outs.toList {} Inv.empty
    (fun e h => hout e (by simpa using h))
  apply Array.ext
  · simp [cse, Kernel.eval, hlen]
  · intro i h1 h2
    simp only [Array.size_map] at h2
    obtain ⟨v, hv1, hv2⟩ := hval i (by simpa using h2)
    simp only [cse, Kernel.eval, Array.getElem_map]
    have : (cseList nIn outs.toList {}).1.toArray[i]'(by simpa [hlen] using h2) = v := by
      simp only [List.getElem_toArray]
      exact Option.some_inj.mp ((List.getElem?_eq_getElem _).symm.trans hv1)
    rw [this]
    simp only [Kernel.slots]
    have hs : Array.foldl (fun env op => env.push (op.eval A fun i => env.getD i default)) inp
        (cseList nIn outs.toList {}).2.ops = slotsL A inp (cseList nIn outs.toList {}).2.ops.toList := by
      simp [slotsL, Array.foldl_toList]
    rw [hs]
    exact hv2.trans (by simp)

end LeanFFTW.Gen
