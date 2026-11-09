/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Check

/-!
# The checker is sound

`check_sound`: if `check` accepts a block of instructions for a specification, then running
the instructions (`run`, the model of `LeanFFTW/Asm/Sem.lean`) from any machine state leaves,
in every lane of every operand the specification lists, the value of the node the
specification names, computed on the initial memory. This holds for every lawful machine
arithmetic, in particular the exact one and binary64.

The assumptions about memory are stated in `Sep`: operands written by the block that are
written differently do not overlap, and an operand that is written does not overlap an
operand of another kind that is read (spill slots, data, constants). Data that is read may
overlap data that is written, as in an in-place transform.
-/

namespace LeanFFTW.Asm

open Std LeanFFTW.Gen

variable {α : Type}

/-! ## Values of nodes -/

section Vals

variable (M : Machine α) (ad : Mem → Int) (mem0 : Int → α)

theorem SNode.eval_congr {nd : SNode} {i : Nat} (hb : nd.below i = true) {g g' : Nat → α}
    (h : ∀ j, j < i → g j = g' j) : nd.eval M ad mem0 g = nd.eval M ad mem0 g' := by
  cases nd with
  | inp m l => rfl
  | bits b => rfl
  | add a b | sub a b | mul a b =>
      simp only [SNode.below, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [SNode.eval, h _ hb.1, h _ hb.2]
  | neg a =>
      simp only [SNode.below, decide_eq_true_eq] at hb
      simp only [SNode.eval, h _ hb]
  | fma a b c | fms a b c | fnma a b c =>
      simp only [SNode.below, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [SNode.eval, h _ hb.1.1, h _ hb.1.2, h _ hb.2]

theorem getD_push_lt (acc : Array α) (x d : α) (i : Nat) (h : i < acc.size) :
    (acc.push x).getD i d = acc.getD i d := by
  have : i ≠ acc.size := by omega
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, this]

theorem getD_push_eq (acc : Array α) (x d : α) : (acc.push x).getD acc.size d = x := by
  simp [Array.getD_eq_getD_getElem?]

theorem valsL_getD_lt (nodes : List SNode) : ∀ (acc : Array α) (i : Nat), i < acc.size →
    (valsL M ad mem0 nodes acc).getD i (M.ofBits 0) = acc.getD i (M.ofBits 0) := by
  induction nodes with
  | nil => intro acc i _; rfl
  | cons nd rest ih =>
      intro acc i hi
      rw [valsL, ih _ _ (by simp; omega), getD_push_lt _ _ _ _ hi]

theorem valsL_getD_node (nodes : List SNode) : ∀ (acc : Array α) (i : Nat) (nd : SNode),
    acc.size ≤ i → nodes[i - acc.size]? = some nd → nd.below i = true →
    (valsL M ad mem0 nodes acc).getD i (M.ofBits 0) =
      nd.eval M ad mem0 fun j => (valsL M ad mem0 nodes acc).getD j (M.ofBits 0) := by
  induction nodes with
  | nil => intro acc i nd _ hn; simp at hn
  | cons nd' rest ih =>
      intro acc i nd hi hn hb
      rw [valsL]
      by_cases h : i = acc.size
      · subst h
        simp at hn
        subst hn
        rw [valsL_getD_lt _ _ _ _ _ _ (by simp), getD_push_eq]
        apply SNode.eval_congr M ad mem0 hb
        intro j hj
        rw [valsL_getD_lt _ _ _ _ _ _ (by simp; omega), getD_push_lt _ _ _ _ hj]
      · apply ih
        · simp; omega
        · have : i - acc.size = (i - (acc.push (nd'.eval M ad mem0 fun i => acc.getD i (M.ofBits 0))).size) + 1 := by
            simp; omega
          rw [this, List.getElem?_cons_succ] at hn
          exact hn
        · exact hb

end Vals

/-- The value of node `i` of the checker's context on the initial memory `mem0`. -/
def Ctx.val (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) (cx : Ctx) (i : Nat) : α :=
  (valsL M ad mem0 cx.nodes.toList #[]).getD i (M.ofBits 0)

/-! ## Symbolic values agree with the machine -/

section Sym

variable (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) (cx : Ctx)

theorem look_sound {nd : SNode} {i : Nat} (h : cx.look nd = .node i) :
    cx.val M ad mem0 i = nd.eval M ad mem0 (cx.val M ad mem0) := by
  unfold Ctx.look at h
  split at h
  · split at h
    · rename_i hc
      cases h
      unfold Ctx.val
      apply valsL_getD_node
      · simp
      · simpa using hc.1
      · exact hc.2
    · cases h
  · cases h

theorem look_cases (nd : SNode) : cx.look nd = .junk ∨ ∃ i, cx.look nd = .node i := by
  unfold Ctx.look
  split
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- What a symbolic value says about a scalar. -/
def Agree (v : SVal) (x : α) : Prop :=
  match v with
  | .node i => x = cx.val M ad mem0 i
  | .negNode i => x = M.A.neg (cx.val M ad mem0 i)
  | .bits b => x = M.ofBits b
  | .junk => True

theorem agree_look {nd : SNode} {x : α} (h : x = nd.eval M ad mem0 (cx.val M ad mem0)) :
    Agree M ad mem0 cx (cx.look nd) x := by
  rcases look_cases cx nd with h' | ⟨i, h'⟩
  · rw [h']; trivial
  · rw [h']; show x = _; rw [look_sound M ad mem0 cx h']; exact h

theorem agree_look2 {n₁ n₂ : SNode} {x : α} (h₁ : x = n₁.eval M ad mem0 (cx.val M ad mem0))
    (h₂ : x = n₂.eval M ad mem0 (cx.val M ad mem0)) : Agree M ad mem0 cx (cx.look2 n₁ n₂) x := by
  unfold Ctx.look2
  split
  · exact agree_look M ad mem0 cx h₂
  · exact agree_look M ad mem0 cx h₁

theorem agree_look3 {f : Nat → Nat → Nat → SNode} {ox oy oc : Option Nat} {x : α}
    (h : ∀ a b d, ox = some a → oy = some b → oc = some d →
      x = (f a b d).eval M ad mem0 (cx.val M ad mem0) ∧ x = (f b a d).eval M ad mem0 (cx.val M ad mem0)) :
    Agree M ad mem0 cx (cx.look3 f ox oy oc) x := by
  unfold Ctx.look3
  split
  · exact agree_look2 M ad mem0 cx (h _ _ _ rfl rfl rfl).1 (h _ _ _ rfl rfl rfl).2
  · trivial

theorem agree_orElse {v w : SVal} {x : α} (hv : Agree M ad mem0 cx v x) (hw : Agree M ad mem0 cx w x) :
    Agree M ad mem0 cx (v.orElse w) x := by
  cases v <;> first | exact hw | exact hv

theorem toId_sound {v : SVal} {i : Nat} {x : α} (h : cx.toId v = some i) (hx : Agree M ad mem0 cx v x) :
    x = cx.val M ad mem0 i := by
  cases v with
  | node j => simp [Ctx.toId] at h; subst h; exact hx
  | bits b =>
      simp only [Ctx.toId] at h
      split at h
      · rename_i j hj
        cases h
        rw [look_sound M ad mem0 cx hj]; exact hx
      · cases h
  | negNode j =>
      simp only [Ctx.toId] at h
      split at h
      · rename_i k hk
        cases h
        rw [look_sound M ad mem0 cx hk]; exact hx
      · cases h
  | junk => simp [Ctx.toId] at h

variable (hM : M.Lawful)
include hM

theorem asNeg_sound {v : SVal} {i : Nat} {x : α} (h : cx.asNeg v = some i)
    (hx : Agree M ad mem0 cx v x) : x = M.A.neg (cx.val M ad mem0 i) := by
  cases v with
  | negNode j => simp [Ctx.asNeg] at h; subst h; exact hx
  | bits b =>
      simp only [Ctx.asNeg] at h
      split at h
      · rename_i j hj
        cases h
        have : cx.val M ad mem0 i = M.ofBits (b ^^^ 0x8000000000000000) := look_sound M ad mem0 cx hj
        rw [this, hM.ofBits_neg, hM.neg_neg]; exact hx
      · cases h
  | node j => simp [Ctx.asNeg] at h
  | junk => simp [Ctx.asNeg] at h

theorem agree_sAdd {v w : SVal} {a b : α} (ha : Agree M ad mem0 cx v a) (hb : Agree M ad mem0 cx w b) :
    Agree M ad mem0 cx (cx.sAdd v w) (M.A.add a b) := by
  unfold Ctx.sAdd
  split
  · rename_i i j hi hj
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    apply agree_look2
    · simp only [SNode.eval, ea, eb]
    · simp only [SNode.eval, ea, eb]; exact hM.add_comm _ _
  · trivial

omit hM in
theorem agree_sSub {v w : SVal} {a b : α} (ha : Agree M ad mem0 cx v a) (hb : Agree M ad mem0 cx w b) :
    Agree M ad mem0 cx (cx.sSub v w) (M.A.sub a b) := by
  unfold Ctx.sSub
  split
  · rename_i i j hi hj
    apply agree_look
    simp only [SNode.eval, toId_sound M ad mem0 cx hi ha, toId_sound M ad mem0 cx hj hb]
  · trivial

theorem agree_sMul {v w : SVal} {a b : α} (ha : Agree M ad mem0 cx v a) (hb : Agree M ad mem0 cx w b) :
    Agree M ad mem0 cx (cx.sMul v w) (M.A.mul a b) := by
  unfold Ctx.sMul
  split
  · rename_i i j hi hj
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    apply agree_look2
    · simp only [SNode.eval, ea, eb]
    · simp only [SNode.eval, ea, eb]; exact hM.mul_comm _ _
  · trivial

theorem agree_sNeg {v : SVal} {a : α} (ha : Agree M ad mem0 cx v a) :
    Agree M ad mem0 cx (cx.sNeg v) (M.A.neg a) := by
  cases v with
  | node i =>
      simp only [Ctx.sNeg]
      split
      · rename_i j hj
        show _ = _
        rw [look_sound M ad mem0 cx hj]
        simp only [SNode.eval]; rw [show a = _ from ha]
      · show _ = _
        rw [show a = _ from ha]
  | negNode i =>
      show _ = _
      rw [show a = _ from ha, hM.neg_neg]
  | bits b => trivial
  | junk => trivial

theorem agree_sXor {v w : SVal} {a b : α} (ha : Agree M ad mem0 cx v a) (hb : Agree M ad mem0 cx w b) :
    Agree M ad mem0 cx (cx.sXor v w) (M.xor a b) := by
  unfold Ctx.sXor
  split
  · rename_i c
    have eb : b = M.ofBits c := hb
    split
    · rename_i h0; subst h0; rw [eb, hM.xor_zero]; exact ha
    · split
      · rename_i h1; subst h1; rw [eb, hM.xor_sign]; exact agree_sNeg M ad mem0 cx hM ha
      · trivial
  · trivial

theorem agree_sFma0 {u v w : SVal} {a b c : α} (ha : Agree M ad mem0 cx u a)
    (hb : Agree M ad mem0 cx v b) (hc : Agree M ad mem0 cx w c) :
    Agree M ad mem0 cx (cx.sFma0 u v w) (M.A.fma a b c) := by
  unfold Ctx.sFma0
  refine agree_orElse M ad mem0 cx (agree_orElse M ad mem0 cx ?_ ?_) ?_
  · apply agree_look3
    intro i j k hi hj hk
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨trivial, hM.fma_comm _ _ _⟩
  · apply agree_look3
    intro i j k hi hj hk
    have ea := asNeg_sound M ad mem0 cx hM hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨hM.fma_neg _ _ _, by rw [hM.fma_neg, hM.fnma_comm]⟩
  · apply agree_look3
    intro i j k hi hj hk
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := asNeg_sound M ad mem0 cx hM hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨by rw [hM.fma_comm, hM.fma_neg, hM.fnma_comm], by rw [hM.fma_comm, hM.fma_neg]⟩

theorem agree_sFma {u v w : SVal} {a b c : α} (ha : Agree M ad mem0 cx u a)
    (hb : Agree M ad mem0 cx v b) (hc : Agree M ad mem0 cx w c) :
    Agree M ad mem0 cx (cx.sFma u v w) (M.A.fma a b c) := by
  have h0 := agree_sFma0 M ad mem0 cx hM ha hb hc
  unfold Ctx.sFma
  split
  · split
    · rename_i h1; subst h1
      rw [show a = M.ofBits oneBits from ha, hM.fma_comm, hM.fma_one]
      exact agree_sAdd M ad mem0 cx hM hb hc
    · split
      · rename_i h2; subst h2
        rw [show b = M.ofBits oneBits from hb, hM.fma_one]
        exact agree_sAdd M ad mem0 cx hM ha hc
      · trivial
  · exact h0

theorem agree_sFms {u v w : SVal} {a b c : α} (ha : Agree M ad mem0 cx u a)
    (hb : Agree M ad mem0 cx v b) (hc : Agree M ad mem0 cx w c) :
    Agree M ad mem0 cx (cx.sFms u v w) (M.A.fms a b c) := by
  have h0 : Agree M ad mem0 cx (cx.look3 .fms (cx.toId u) (cx.toId v) (cx.toId w)) (M.A.fms a b c) := by
    apply agree_look3
    intro i j k hi hj hk
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨trivial, hM.fms_comm _ _ _⟩
  unfold Ctx.sFms
  split
  · split
    · rename_i h1; subst h1
      rw [show a = M.ofBits oneBits from ha, hM.fms_comm, hM.fms_one]
      exact agree_sSub M ad mem0 cx hb hc
    · split
      · rename_i h2; subst h2
        rw [show b = M.ofBits oneBits from hb, hM.fms_one]
        exact agree_sSub M ad mem0 cx ha hc
      · trivial
  · exact h0

theorem agree_sFnma {u v w : SVal} {a b c : α} (ha : Agree M ad mem0 cx u a)
    (hb : Agree M ad mem0 cx v b) (hc : Agree M ad mem0 cx w c) :
    Agree M ad mem0 cx (cx.sFnma u v w) (M.A.fnma a b c) := by
  unfold Ctx.sFnma
  refine agree_orElse M ad mem0 cx (agree_orElse M ad mem0 cx ?_ ?_) ?_
  · apply agree_look3
    intro i j k hi hj hk
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨trivial, hM.fnma_comm _ _ _⟩
  · apply agree_look3
    intro i j k hi hj hk
    have ea := asNeg_sound M ad mem0 cx hM hi ha
    have eb := toId_sound M ad mem0 cx hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨hM.fnma_neg _ _ _, by rw [hM.fnma_neg, hM.fma_comm]⟩
  · apply agree_look3
    intro i j k hi hj hk
    have ea := toId_sound M ad mem0 cx hi ha
    have eb := asNeg_sound M ad mem0 cx hM hj hb
    have ec := toId_sound M ad mem0 cx hk hc
    simp only [SNode.eval, ea, eb, ec]
    exact ⟨by rw [hM.fnma_comm, hM.fnma_neg, hM.fma_comm], by rw [hM.fnma_comm, hM.fnma_neg]⟩

theorem agree_sFmaLane (op : VFma) (l : Nat) {u v w : SVal} {a b c : α}
    (ha : Agree M ad mem0 cx u a) (hb : Agree M ad mem0 cx v b) (hc : Agree M ad mem0 cx w c) :
    Agree M ad mem0 cx (cx.sFmaLane op l u v w) (fmaLane M op l a b c) := by
  cases op <;> simp only [Ctx.sFmaLane, fmaLane]
  · exact agree_sFma M ad mem0 cx hM ha hb hc
  · exact agree_sFms M ad mem0 cx hM ha hb hc
  · exact agree_sFnma M ad mem0 cx hM ha hb hc
  · split
    · exact agree_sFms M ad mem0 cx hM ha hb hc
    · exact agree_sFma M ad mem0 cx hM ha hb hc
  · split
    · exact agree_sFma M ad mem0 cx hM ha hb hc
    · exact agree_sFms M ad mem0 cx hM ha hb hc

theorem agree_sBinLane (op : VBin) (l : Nat) {x y : Nat → SVal} {a b : Nat → α}
    (ha : ∀ l, Agree M ad mem0 cx (x l) (a l)) (hb : ∀ l, Agree M ad mem0 cx (y l) (b l)) :
    Agree M ad mem0 cx (cx.sBinLane op x y l) (binLane M op a b l) := by
  cases op <;> simp only [Ctx.sBinLane, binLane]
  · exact agree_sAdd M ad mem0 cx hM (ha l) (hb l)
  · exact agree_sSub M ad mem0 cx (ha l) (hb l)
  · exact agree_sMul M ad mem0 cx hM (ha l) (hb l)
  · exact agree_sXor M ad mem0 cx hM (ha l) (hb l)
  · split
    · exact ha _
    · exact hb _
  · split
    · exact ha _
    · exact hb _

omit hM

theorem agree_shufpd (imm l : Nat) {x y : Nat → SVal} {a b : Nat → α}
    (ha : ∀ l, Agree M ad mem0 cx (x l) (a l)) (hb : ∀ l, Agree M ad mem0 cx (y l) (b l)) :
    Agree M ad mem0 cx (shufpdLane imm x y l) (shufpdLane imm a b l) := by
  unfold shufpdLane
  split
  · exact ha _
  · exact hb _

theorem agree_shuff (w : W) (imm l : Nat) {x y : Nat → SVal} {a b : Nat → α}
    (ha : ∀ l, Agree M ad mem0 cx (x l) (a l)) (hb : ∀ l, Agree M ad mem0 cx (y l) (b l)) :
    Agree M ad mem0 cx (shuffLane w imm x y l) (shuffLane w imm a b l) := by
  cases w <;> simp only [shuffLane]
  · exact ha _
  · split
    · exact ha _
    · exact hb _
  · split
    · exact ha _
    · exact hb _

end Sym

/-! ## Memory -/

theorem W.lanes_pos (w : W) : 0 < w.lanes := by cases w <;> decide

theorem W.lanes_le (w : W) : w.lanes ≤ 8 := by cases w <;> decide

theorem setMem_hit (s : MState α) (w : W) (a : Int) (f : Nat → α) {l : Nat} (h : l < w.lanes) :
    (s.setMem w a f).mem (a + l) = f l := by
  simp only [MState.setMem]
  have h1 : a ≤ a + (l : Int) ∧ a + (l : Int) < a + (w.lanes : Int) := by omega
  simp only [h1, and_self, ↓reduceIte]
  congr 1
  omega

theorem setMem_miss (s : MState α) (w : W) (a : Int) (f : Nat → α) {x : Int}
    (h : ∀ l : Nat, l < w.lanes → x ≠ a + l) : (s.setMem w a f).mem x = s.mem x := by
  simp only [MState.setMem]
  have h1 : ¬(a ≤ x ∧ x < a + (w.lanes : Int)) := fun ⟨h1, h2⟩ =>
    h (x - a).toNat (by omega) (by omega)
  simp only [h1, ↓reduceIte]

/-- The operand an instruction stores to. -/
def Instr.wr : Instr → Option Mem
  | .vstore _ m _ => some m
  | _ => none

/-- The memory operand of a source. -/
def VSrc.mem? : VSrc → Option Mem
  | .reg _ => none
  | .mem m => some m
  | .bcst m => some m

/-- The memory operand an instruction reads. -/
def Instr.rdm : Instr → Option Mem
  | .vmov _ _ s | .vbin _ _ _ _ s | .vfma _ _ _ _ _ s | .vshufpd _ _ _ s _
  | .vshuff64x2 _ _ _ s _ => s.mem?
  | _ => none

/-- What the theorem assumes about the addresses of the operands of a block (`ad` gives
the word number of an operand; an operand covers `w.lanes` words).

* Two different operands the block stores to do not overlap.
* An operand the block stores to does not overlap an operand of another kind (data, spill
  slot, constant) that it reads.

An operand of data that is read may overlap one that is stored: transforms in place. -/
structure Sep (ad : Mem → Int) (w : W) (is : List Instr) : Prop where
  wr_wr : ∀ i ∈ is, ∀ j ∈ is, ∀ m m', i.wr = some m → j.wr = some m' → m ≠ m' →
    ∀ l l' : Nat, l < w.lanes → l' < w.lanes → ad m + l ≠ ad m' + l'
  wr_rd : ∀ i ∈ is, ∀ j ∈ is, ∀ m m', i.wr = some m → j.rdm = some m' → m.kind ≠ m'.kind →
    ∀ l l' : Nat, l < w.lanes → l' < w.lanes → ad m + l ≠ ad m' + l'

/-! ## The symbolic state agrees with the machine -/

theorem Lanes.get_ofFn (f : Nat → SVal) (l : Nat) :
    (Lanes.ofFn f).get l = if l < 8 then f l else .junk := by
  simp only [Lanes.get, Lanes.ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases h : l < 8
  · simp [h]
  · simp [h]

theorem regLane_setReg (cs : CState) (w : W) (r : VReg) (f : Nat → SVal) (n l : Nat) :
    (cs.setReg w r f).regLane n l =
      if n = r.n then (if l < 8 then (if l < w.lanes then f l else .bits 0) else .junk)
      else cs.regLane n l := by
  simp only [CState.setReg, CState.regLane, HashMap.getD_insert]
  by_cases h : n = r.n
  · subst h; simp [Lanes.get_ofFn]
  · have : (r.n == n) = false := by simpa using fun e => h e.symm
    simp [h, this]

theorem mem_snoc_wr {pre : List Instr} {i j : Instr} {m : Mem} (hj : j ∈ pre ++ [i])
    (hw : j.wr = some m) : j ∈ pre ∨ i.wr = some m := by
  rcases List.mem_append.1 hj with h | h
  · exact Or.inl h
  · rw [List.mem_singleton] at h; subst h; exact Or.inr hw

section Run

variable (M : Machine α) (ad : Mem → Int) (mem0 : Int → α) (cx : Ctx)

/-- The invariant of the symbolic run: after the instructions `pre`, the symbolic state `cs`
describes the machine state `s`. -/
structure Inv (pre : List Instr) (cs : CState) (s : MState α) : Prop where
  /-- registers -/
  reg : ∀ n l, Agree M ad mem0 cx (cs.regLane n l) (s.reg n l)
  /-- only spill slots and data were stored to -/
  kinds : ∀ i ∈ pre, ∀ m, i.wr = some m → m.kind = .frame ∨ m.kind = .data
  /-- before the first store to data, only spill slots were stored to -/
  early : cs.stored = false → ∀ i ∈ pre, ∀ m, i.wr = some m → m.kind = .frame
  /-- spill slots -/
  frame : ∀ m v, lookupSlot cs.slot m = some v →
    m.kind = .frame ∧ (∃ i ∈ pre, i.wr = some m) ∧
    ∀ l, l < cx.w.lanes → Agree M ad mem0 cx (v.get l) (s.mem (ad m + l))
  /-- stored data -/
  out : ∀ m ∈ cs.done, m.kind = .data ∧ (∃ i ∈ pre, i.wr = some m) ∧
    ∃ ids, cx.outOf m = some ids ∧
      ∀ l, l < cx.w.lanes → ∃ i, ids[l]? = some i ∧ s.mem (ad m + l) = cx.val M ad mem0 i
  /-- the rest of memory -/
  rest : ∀ x, (∀ i ∈ pre, ∀ m, i.wr = some m → ∀ l : Nat, l < cx.w.lanes → x ≠ ad m + l) →
    s.mem x = mem0 x

variable {M ad mem0 cx}

theorem Inv.init (s0 : MState α) : Inv M ad s0.mem cx [] {} s0 where
  reg := by intro n l; simp [CState.regLane, Lanes.get, Agree]
  kinds := by intro i hi; cases hi
  early := by intro _ i hi; cases hi
  frame := by intro m v h; cases h
  out := by intro m hm; cases hm
  rest := by intro x _; rfl

variable {is pre : List Instr} {cs : CState} {s : MState α}

/-- A word of an operand that is read and whose kind was never stored to is unchanged. -/
theorem Inv.unchanged (hsep : Sep ad cx.w is) (hpre : ∀ j ∈ pre, j ∈ is)
    (inv : Inv M ad mem0 cx pre cs s) {m : Mem} (hr : ∃ j ∈ is, j.rdm = some m)
    (hk : ∀ i ∈ pre, ∀ m', i.wr = some m' → m'.kind ≠ m.kind) {l : Nat} (hl : l < cx.w.lanes) :
    s.mem (ad m + l) = mem0 (ad m + l) := by
  apply inv.rest
  intro i hi m' hw l' hl' e
  obtain ⟨j, hj, hjr⟩ := hr
  exact hsep.wr_rd i (hpre i hi) j hj m' m hw hjr (hk i hi m' hw) l' l hl' hl e.symm

/-- Reading a source. -/
theorem rd_sound (hsep : Sep ad cx.w is) (hpre : ∀ j ∈ pre, j ∈ is)
    (hc : ∀ lab bs, cx.consts lab = some bs → ∀ (l : Nat) b, bs[l]? = some b →
      mem0 (ad (Mem.rip lab) + l) = M.ofBits b)
    (inv : Inv M ad mem0 cx pre cs s) {src : VSrc} {f : Nat → SVal} (h : cs.rd cx src = some f)
    (hr : ∀ m, src.mem? = some m → ∃ j ∈ is, j.rdm = some m) :
    ∀ l, Agree M ad mem0 cx (f l) (s.rd ad src l) := by
  cases src with
  | reg r =>
      simp only [CState.rd, Option.some.injEq] at h
      subst h
      exact inv.reg _
  | mem m =>
      simp only [CState.rd] at h
      split at h
      · rename_i lab hk
        split at h
        · rename_i hm
          cases hcs : cx.consts lab with
          | none => simp [hcs] at h
          | some bs =>
              simp only [hcs, Option.map_some, Option.some.injEq] at h
              subst h
              intro l
              show Agree M ad mem0 cx (if l < cx.w.lanes then _ else _) _
              split
              · rename_i hl
                split
                · rename_i b hb
                  show s.mem (ad m + l) = M.ofBits b
                  rw [inv.unchanged hsep hpre (hr m rfl) (fun i hi m' hw e => by
                    rcases inv.kinds i hi m' hw with h' | h' <;> rw [h', hk] at e <;> cases e) hl,
                    hm]
                  exact hc lab bs hcs l b hb
                · trivial
              · trivial
        · cases h
      · rename_i hk
        cases hs : lookupSlot cs.slot m with
        | none => simp [hs] at h
        | some v =>
            simp only [hs, Option.map_some, Option.some.injEq] at h
            subst h
            intro l
            show Agree M ad mem0 cx (if l < cx.w.lanes then _ else _) _
            split
            · rename_i hl; exact (inv.frame m v hs).2.2 l hl
            · trivial
      · rename_i hk
        split at h
        · cases h
        · rename_i hst
          simp only [Option.some.injEq] at h
          subst h
          intro l
          show Agree M ad mem0 cx (if l < cx.w.lanes then _ else _) _
          split
          · rename_i hl
            apply agree_look
            show s.mem (ad m + l) = mem0 (ad m + l)
            exact inv.unchanged hsep hpre (hr m rfl) (fun i hi m' hw e => by
              rw [inv.early (by simpa using hst) i hi m' hw, hk] at e; cases e) hl
          · trivial
  | bcst m =>
      simp only [CState.rd] at h
      split at h
      · rename_i lab hk
        split at h
        · rename_i hm
          cases hcs : cx.consts lab with
          | none => simp [hcs] at h
          | some bs =>
              simp only [hcs, Option.map_some, Option.some.injEq] at h
              subst h
              intro l
              show Agree M ad mem0 cx (match bs[0]? with | some b => SVal.bits b | none => .junk) _
              split
              · rename_i b hb
                show s.mem (ad m) = M.ofBits b
                have h0 := inv.unchanged hsep hpre (hr m rfl) (fun i hi m' hw e => by
                  rcases inv.kinds i hi m' hw with h' | h' <;> rw [h', hk] at e <;> cases e)
                  (W.lanes_pos cx.w)
                have h1 := hc lab bs hcs 0 b hb
                simp only [Int.natCast_zero, Int.add_zero] at h0 h1
                rw [h0, hm]; exact h1
              · trivial
        · cases h
      · cases h

/-- An instruction that writes a register. -/
theorem Inv.setReg (inv : Inv M ad mem0 cx pre cs s) {i : Instr} (hi : i.wr = none) (w : W)
    (d : VReg) {f : Nat → SVal} {g : Nat → α} (h : ∀ l, Agree M ad mem0 cx (f l) (g l)) :
    Inv M ad mem0 cx (pre ++ [i]) (cs.setReg w d f) (s.setReg M w d g) where
  reg := by
    intro n l
    rw [regLane_setReg]
    simp only [MState.setReg]
    split
    · split
      · split
        · exact h l
        · rfl
      · trivial
    · exact inv.reg n l
  kinds := by
    intro j hj m hw
    rcases mem_snoc_wr hj hw with h' | h'
    · exact inv.kinds j h' m hw
    · rw [hi] at h'; cases h'
  early := by
    intro hst j hj m hw
    rcases mem_snoc_wr hj hw with h' | h'
    · exact inv.early hst j h' m hw
    · rw [hi] at h'; cases h'
  frame := by
    intro m v hv
    obtain ⟨h1, ⟨j, hj, hw⟩, h3⟩ := inv.frame m v hv
    exact ⟨h1, ⟨j, List.mem_append_left _ hj, hw⟩, h3⟩
  out := by
    intro m hm
    obtain ⟨h1, ⟨j, hj, hw⟩, h3⟩ := inv.out m hm
    exact ⟨h1, ⟨j, List.mem_append_left _ hj, hw⟩, h3⟩
  rest := by
    intro x hx
    exact inv.rest x fun j hj m hw => hx j (List.mem_append_left _ hj) m hw

/-- A store. -/
theorem Inv.store (hsep : Sep ad cx.w is) (hpre : ∀ j ∈ pre, j ∈ is) {m : Mem} {r : VReg}
    (hi : Instr.vstore cx.w m r ∈ is) (inv : Inv M ad mem0 cx pre cs s) {cs' : CState}
    (hreg : cs'.reg = cs.reg) (hk : m.kind = .frame ∨ m.kind = .data)
    (hearly : cs'.stored = false → cs.stored = false ∧ m.kind = .frame)
    (hframe : ∀ m' v, lookupSlot cs'.slot m' = some v →
      (m' ≠ m ∧ lookupSlot cs.slot m' = some v) ∨
      (m' = m ∧ m.kind = .frame ∧
        ∀ l, l < cx.w.lanes → Agree M ad mem0 cx (v.get l) (s.reg r.n l)))
    (hout : ∀ m' ∈ cs'.done, (m' ≠ m ∧ m' ∈ cs.done) ∨
      (m' = m ∧ m.kind = .data ∧ ∃ ids, cx.outOf m = some ids ∧
        ∀ l, l < cx.w.lanes → ∃ i, ids[l]? = some i ∧ s.reg r.n l = cx.val M ad mem0 i)) :
    Inv M ad mem0 cx (pre ++ [.vstore cx.w m r]) cs' (s.setMem cx.w (ad m) (s.reg r.n)) := by
  -- a word of another stored operand is not touched
  have other : ∀ m', m' ≠ m → (∃ j ∈ pre, j.wr = some m') → ∀ l : Nat, l < cx.w.lanes →
      (s.setMem cx.w (ad m) (s.reg r.n)).mem (ad m' + l) = s.mem (ad m' + l) := by
    intro m' hne ⟨j, hj, hw⟩ l hl
    apply setMem_miss
    intro l' hl' e
    exact hsep.wr_wr _ hi j (hpre j hj) m m' rfl hw (Ne.symm hne) l' l hl' hl e.symm
  have here : ∃ j ∈ pre ++ [Instr.vstore cx.w m r], j.wr = some m :=
    ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n l
    have : cs'.regLane n l = cs.regLane n l := by simp only [CState.regLane, hreg]
    rw [this]
    exact inv.reg n l
  · intro j hj m' hw
    rcases mem_snoc_wr hj hw with h' | h'
    · exact inv.kinds j h' m' hw
    · cases h'; exact hk
  · intro hst j hj m' hw
    rcases mem_snoc_wr hj hw with h' | h'
    · exact inv.early (hearly hst).1 j h' m' hw
    · cases h'; exact (hearly hst).2
  · intro m' v hv
    rcases hframe m' v hv with ⟨hne, hv'⟩ | ⟨he, hkf, ha⟩
    · obtain ⟨h1, ⟨j, hj, hw⟩, h3⟩ := inv.frame m' v hv'
      refine ⟨h1, ⟨j, List.mem_append_left _ hj, hw⟩, fun l hl => ?_⟩
      rw [other m' hne ⟨j, hj, hw⟩ l hl]
      exact h3 l hl
    · subst he
      refine ⟨hkf, here, fun l hl => ?_⟩
      rw [setMem_hit _ _ _ _ hl]
      exact ha l hl
  · intro m' hm'
    rcases hout m' hm' with ⟨hne, hd⟩ | ⟨he, hkd, ids, hids, ha⟩
    · obtain ⟨h1, ⟨j, hj, hw⟩, ids, hids, h3⟩ := inv.out m' hd
      refine ⟨h1, ⟨j, List.mem_append_left _ hj, hw⟩, ids, hids, fun l hl => ?_⟩
      rw [other m' hne ⟨j, hj, hw⟩ l hl]
      exact h3 l hl
    · subst he
      refine ⟨hkd, here, ids, hids, fun l hl => ?_⟩
      rw [setMem_hit _ _ _ _ hl]
      exact ha l hl
  · intro x hx
    rw [setMem_miss]
    · exact inv.rest x fun j hj m' hw => hx j (List.mem_append_left _ hj) m' hw
    · exact hx _ (List.mem_append_right _ (List.mem_singleton.2 rfl)) m rfl

variable (hM : M.Lawful)
include hM

/-- One instruction. -/
theorem cstep_sound (hsep : Sep ad cx.w is) (hpre : ∀ j ∈ pre, j ∈ is)
    (hc : ∀ lab bs, cx.consts lab = some bs → ∀ (l : Nat) b, bs[l]? = some b →
      mem0 (ad (Mem.rip lab) + l) = M.ofBits b)
    (inv : Inv M ad mem0 cx pre cs s) {i : Instr} (hi : i ∈ is) {cs' : CState}
    (h : cstep cx cs i = some cs') : Inv M ad mem0 cx (pre ++ [i]) cs' (step M ad s i) := by
  cases i with
  | vmov w d src =>
      simp only [cstep] at h
      split at h
      · rename_i hw
        subst hw
        cases hf : cs.rd cx src with
        | none => simp [hf] at h
        | some f =>
            simp only [hf, Option.map_some, Option.some.injEq] at h
            subst h
            exact inv.setReg rfl _ _ (rd_sound hsep hpre hc inv hf fun m hm => ⟨_, hi, hm⟩)
      · cases h
  | vbin op w d s1 s2 =>
      simp only [cstep] at h
      split at h
      · rename_i hw
        subst hw
        cases hf : cs.rd cx s2 with
        | none => simp [hf] at h
        | some f =>
            simp only [hf, Option.map_some, Option.some.injEq] at h
            subst h
            have hs := rd_sound hsep hpre hc inv hf fun m hm => ⟨_, hi, hm⟩
            exact inv.setReg rfl _ _ fun l =>
              agree_sBinLane M ad mem0 cx hM op l (fun l => inv.reg _ l) hs
      · cases h
  | vfma op form w d s2 s3 =>
      simp only [cstep] at h
      split at h
      · rename_i hw
        subst hw
        cases hf : cs.rd cx s3 with
        | none => simp [hf] at h
        | some f =>
            simp only [hf, Option.map_some, Option.some.injEq] at h
            subst h
            have hs := rd_sound hsep hpre hc inv hf fun m hm => ⟨_, hi, hm⟩
            refine inv.setReg rfl _ _ fun l => ?_
            cases form
            · exact agree_sFmaLane M ad mem0 cx hM op l (inv.reg _ l) (hs l) (inv.reg _ l)
            · exact agree_sFmaLane M ad mem0 cx hM op l (inv.reg _ l) (inv.reg _ l) (hs l)
            · exact agree_sFmaLane M ad mem0 cx hM op l (inv.reg _ l) (hs l) (inv.reg _ l)
      · cases h
  | vshufpd w d s1 s2 imm =>
      simp only [cstep] at h
      split at h
      · rename_i hw
        subst hw
        cases hf : cs.rd cx s2 with
        | none => simp [hf] at h
        | some f =>
            simp only [hf, Option.map_some, Option.some.injEq] at h
            subst h
            have hs := rd_sound hsep hpre hc inv hf fun m hm => ⟨_, hi, hm⟩
            exact inv.setReg rfl _ _ fun l =>
              agree_shufpd M ad mem0 cx imm l (fun l => inv.reg _ l) hs
      · cases h
  | vshuff64x2 w d s1 s2 imm =>
      simp only [cstep] at h
      split at h
      · rename_i hw
        obtain ⟨hw, _⟩ := hw
        subst hw
        cases hf : cs.rd cx s2 with
        | none => simp [hf] at h
        | some f =>
            simp only [hf, Option.map_some, Option.some.injEq] at h
            subst h
            have hs := rd_sound hsep hpre hc inv hf fun m hm => ⟨_, hi, hm⟩
            exact inv.setReg rfl _ _ fun l =>
              agree_shuff M ad mem0 cx _ imm l (fun l => inv.reg _ l) hs
      · cases h
  | vzero d =>
      simp only [cstep, Option.some.injEq] at h
      subst h
      have e : step M ad s (.vzero d) = s.setReg M cx.w d fun _ => M.ofBits 0 := by
        simp [step, MState.setReg]
      rw [e]
      exact inv.setReg rfl _ _ fun _ => rfl
  | vstore w m r =>
      simp only [cstep] at h
      split at h
      · rename_i hw
        subst hw
        split at h
        · cases h
        · rename_i hk
          simp only [Option.some.injEq] at h
          subst h
          refine inv.store hsep hpre hi rfl (Or.inl hk) (fun hst => ⟨hst, hk⟩) ?_ ?_
          · intro m' v hv
            simp only [lookupSlot] at hv
            split at hv
            · rename_i he
              cases hv
              refine Or.inr ⟨he.symm, hk, fun l hl => ?_⟩
              have h8 : l < 8 := by have := cx.w.lanes_le; omega
              simp only [Lanes.get_ofFn, h8, ↓reduceIte]
              exact inv.reg _ l
            · rename_i hne
              exact Or.inl ⟨fun e => hne e.symm, hv⟩
          · intro m' hm'
            refine Or.inl ⟨fun e => ?_, hm'⟩
            have := (inv.out m' hm').1
            rw [e, hk] at this
            cases this
        · rename_i hk
          split at h
          · rename_i ids hids
            split at h
            · rename_i hall
              simp only [Option.some.injEq] at h
              subst h
              refine inv.store hsep hpre hi rfl (Or.inr hk) (fun hst => by cases hst) ?_ ?_
              · intro m' v hv
                refine Or.inl ⟨fun e => ?_, hv⟩
                have := (inv.frame m' v hv).1
                rw [e, hk] at this
                cases this
              · intro m' hm'
                by_cases he : m' = m
                · refine Or.inr ⟨he, hk, ids, hids, fun l hl => ?_⟩
                  have hl' := (List.all_eq_true.1 hall) l (List.mem_range.2 hl)
                  split at hl'
                  · rename_i i hil
                    refine ⟨i, hil, ?_⟩
                    have ha := inv.reg r.n l
                    rw [of_decide_eq_true hl'] at ha
                    exact ha
                  · cases hl'
                · rcases List.mem_cons.1 hm' with h' | h'
                  · exact absurd h' he
                  · exact Or.inl ⟨he, h'⟩
            · cases h
          · cases h
      · cases h
  | _ => simp [cstep] at h

/-- A block: the symbolic run describes the machine after the block. -/
theorem crun_sound (hsep : Sep ad cx.w is)
    (hc : ∀ lab bs, cx.consts lab = some bs → ∀ (l : Nat) b, bs[l]? = some b →
      mem0 (ad (Mem.rip lab) + l) = M.ofBits b) :
    ∀ (rest pre : List Instr) (cs cs' : CState) (s : MState α), (∀ j ∈ pre ++ rest, j ∈ is) →
      Inv M ad mem0 cx pre cs s → crun cx rest cs = some cs' →
      Inv M ad mem0 cx (pre ++ rest) cs' (run M ad rest s) := by
  intro rest
  induction rest with
  | nil =>
      intro pre cs cs' s _ inv h
      simp only [crun, Option.some.injEq] at h
      subst h
      simpa [run] using inv
  | cons i rest ih =>
      intro pre cs cs' s hsub inv h
      simp only [crun] at h
      split at h
      · rename_i cs1 h1
        have h2 := ih (pre ++ [i]) cs1 cs' (step M ad s i) (by simpa using hsub)
          (cstep_sound hM hsep (fun j hj => hsub j (List.mem_append_left _ hj)) hc inv
            (hsub i (by simp)) h1) h
        simpa [run] using h2
      · cases h

end Run

/-- **The checker is sound.** If `check` accepts the instructions `is` for the specification
`sp`, then on every lawful machine, from every state `s0` whose constant pool holds the
constants and whose operands are separated (`Sep`), the block leaves in every lane of every
operand the specification lists the value of the node the specification names, computed on
the memory before the block. -/
theorem check_sound (M : Machine α) (hM : M.Lawful) (ad : Mem → Int)
    (consts : String → Option (Array UInt64)) (sp : Spec) (w : W) (is : List Instr)
    (s0 : MState α) (hcheck : check consts sp w is = true)
    (hconst : ∀ lab bs, consts lab = some bs → ∀ (l : Nat) b, bs[l]? = some b →
      s0.mem (ad (Mem.rip lab) + l) = M.ofBits b)
    (hsep : Sep ad w is) :
    ∀ m ids, (m, ids) ∈ sp.outs → ∀ l, l < w.lanes →
      ∃ i, ids[l]? = some i ∧ (run M ad is s0).mem (ad m + l) = sp.val M ad s0.mem i := by
  intro m ids hmem l hl
  simp only [check] at hcheck
  split at hcheck
  · rename_i cs hrun
    have inv := crun_sound (cx := sp.ctx w consts) hM hsep hconst is [] {} cs s0 (by simp)
      (Inv.init s0) hrun
    have h1 := (List.all_eq_true.1 hcheck) (m, ids) hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨_, _, ids', hids', h3⟩ := inv.out m h1.1
    rw [h1.2] at hids'
    cases hids'
    exact h3 l hl
  · cases hcheck

end LeanFFTW.Asm
