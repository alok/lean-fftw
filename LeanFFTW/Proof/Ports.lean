/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Cslib.Algorithms.Lean.Query.FreeM
import LeanFFTW.Asm.Check
import LeanFFTW.Asm.Ports

/-!
# One program, three handlers: the machine, the checker, and the cost

A block of emitted vector code is a program in CSLib's free monad whose only query is "run
this instruction on this state" (`blockQ`). CSLib's interpreters then give the block three
meanings, and each is something this library already had, now as a handler of one object:

* answered by the processor model (`machine`), the program evaluates to `run`, the semantics
  of `LeanFFTW/Asm/Sem.lean` (`eval_blockQ_machine`);
* answered by the symbolic step (`checker`), it evaluates to `crun`, the run of the checker
  that `check_sound` is about (`eval_blockQ_checker`);
* weighed by the micro-operations of each instruction (`uopWeight`), its cost under **every**
  handler is `portsOf`, the vector of port counts (`cost_blockQ`).

The cost lives in an ordered structure rather than in `Nat`: a vector of counts by port
class, where the price of a block is its scarcest port. `block_cycles_ge` proves that this
price is real: in the port model of `LeanFFTW/Asm/Ports.lean`, **every** assignment of the
block's micro-operations to cycles and ports takes at least `(portsOf is).bound` cycles.
It is a lower bound on what any out-of-order scheduler can do with the block, proved from
the instructions that are emitted, not from an annotation.

What the bound does not see is stated in `docs/COST_MODEL.md`, with measurements.
-/

namespace LeanFFTW.Asm

open Cslib

/-! ## The block as a query program -/

/-- The query of a block over states `σ`: run an instruction on a state. -/
inductive InstrQ (σ : Type) : Type → Type where
  | exec (s : σ) (i : Instr) : InstrQ σ σ

/-- A block: its instructions in order, each asked as a query. -/
def blockQ {σ : Type} : List Instr → σ → FreeM (InstrQ σ) σ
  | [], s => pure s
  | i :: is, s => do
      let s' ← FreeM.lift (InstrQ.exec s i)
      blockQ is s'

variable {α : Type}

/-- Handler 1: the model of the processor. -/
def machine (M : Machine α) (ad : Mem → Int) : {ι : Type} → InstrQ (MState α) ι → ι
  | _, .exec s i => step M ad s i

/-- Handler 2: the checker's symbolic step; `none` is a rejected block. -/
def checker (cx : Ctx) : {ι : Type} → InstrQ (Option CState) ι → ι
  | _, .exec s i => s.bind fun cs => cstep cx cs i

/-- Handler 3: the micro-operations of the instruction, by port class. -/
def uopWeight {σ : Type} : {ι : Type} → InstrQ σ ι → Ports
  | _, .exec _ i => Ports.ofList i.uops

theorem eval_blockQ_machine (M : Machine α) (ad : Mem → Int) :
    ∀ (is : List Instr) (s : MState α),
      FreeM.eval (machine M ad) (blockQ is s) = run M ad is s
  | [], _ => rfl
  | i :: is, s => by
    simp only [blockQ, FreeM.eval_bind, FreeM.eval_lift]
    exact eval_blockQ_machine M ad is _

theorem eval_blockQ_checker (cx : Ctx) :
    ∀ (is : List Instr) (s : Option CState),
      FreeM.eval (checker cx) (blockQ is s) = s.bind (crun cx is)
  | [], s => by cases s <;> rfl
  | i :: is, s => by
    simp only [blockQ, FreeM.eval_bind, FreeM.eval_lift]
    rw [eval_blockQ_checker cx is]
    cases s with
    | none => rfl
    | some cs =>
        simp only [checker, Option.bind_some, crun]
        cases cstep cx cs i <;> rfl

/-! ## Port counts form an additive monoid -/

namespace Ports

@[ext] theorem ext {a b : Ports} (h1 : a.fp = b.fp) (h2 : a.shuf = b.shuf)
    (h3 : a.load = b.load) (h4 : a.store = b.store) : a = b := by
  cases a; cases b; simp_all

instance : Zero Ports := ⟨{}⟩

@[simp] theorem add_fp (a b : Ports) : (a + b).fp = a.fp + b.fp := rfl
@[simp] theorem add_shuf (a b : Ports) : (a + b).shuf = a.shuf + b.shuf := rfl
@[simp] theorem add_load (a b : Ports) : (a + b).load = a.load + b.load := rfl
@[simp] theorem add_store (a b : Ports) : (a + b).store = a.store + b.store := rfl
@[simp] theorem zero_fp : (0 : Ports).fp = 0 := rfl
@[simp] theorem zero_shuf : (0 : Ports).shuf = 0 := rfl
@[simp] theorem zero_load : (0 : Ports).load = 0 := rfl
@[simp] theorem zero_store : (0 : Ports).store = 0 := rfl

instance : AddMonoid Ports where
  add_assoc a b c := by ext <;> simp [Nat.add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec

theorem ofList_nil : ofList [] = 0 := rfl

theorem ofList_append (a b : List UClass) : ofList (a ++ b) = ofList a + ofList b := by
  ext <;> simp [ofList, List.count_append]

end Ports

/-- The cost of a block is its vector of port counts, whatever answers the queries. -/
theorem cost_blockQ {σ : Type} (oracle : {ι : Type} → InstrQ σ ι → ι) :
    ∀ (is : List Instr) (s : σ),
      FreeM.cost oracle uopWeight (blockQ is s) = portsOf is
  | [], _ => rfl
  | i :: is, s => by
    simp only [blockQ, FreeM.cost_bind, FreeM.cost_lift, cost_blockQ oracle is]
    simp only [uopWeight, portsOf, uopsOf, List.flatMap_cons, Ports.ofList_append]

/-! ## The port model and its lower bound -/

/-- The ports of the model: two for 512-bit arithmetic, of which `p5` also shuffles; two
load ports; one store per cycle. -/
inductive Port where
  | p0 | p5 | l0 | l1 | s0
  deriving DecidableEq

instance : Fintype Port where
  elems := {.p0, .p5, .l0, .l1, .s0}
  complete := by intro p; cases p <;> simp

/-- The ports a micro-operation of a class may use. -/
def UClass.allowed : UClass → Port → Bool
  | .fp, .p0 | .fp, .p5 => true
  | .shuf, .p5 => true
  | .load, .l0 | .load, .l1 => true
  | .store, .s0 => true
  | _, _ => false

/-- A schedule of micro-operations in `T` cycles: every micro-operation gets a cycle and a
port it may use, and no port does two things in one cycle. Dependencies between the
micro-operations are ignored, which only makes schedules easier to find. -/
structure Schedule (us : List UClass) (T : Nat) where
  slot : Fin us.length → Fin T × Port
  inj : Function.Injective slot
  ok : ∀ i, (us.get i).allowed (slot i).2 = true

/-- Counting the positions of a list that satisfy a predicate. -/
theorem card_filter_get (us : List UClass) (C : UClass → Bool) :
    (Finset.univ.filter fun i : Fin us.length => C (us.get i) = true).card = us.countP C := by
  induction us with
  | nil => simp
  | cons a t ih =>
      rw [Finset.card_filter] at ih ⊢
      refine (Fin.sum_univ_succ
        (fun i : Fin (t.length + 1) => if C ((a :: t).get i) = true then 1 else 0)).trans ?_
      simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
        List.getElem_cons_succ, List.countP_cons] at ih ⊢
      rw [ih]
      by_cases h : C a = true <;> simp [h, Nat.add_comm]

/-- The micro-operations of a set of classes fit in the slots of the ports they may use. -/
theorem Schedule.countP_le {us : List UClass} {T : Nat} (σ : Schedule us T) (C : UClass → Bool)
    (S : Finset Port) (h : ∀ c p, C c = true → c.allowed p = true → p ∈ S) :
    us.countP C ≤ T * S.card := by
  rw [← card_filter_get]
  have hcard : ((Finset.univ : Finset (Fin T)) ×ˢ S).card = T * S.card := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn σ.slot (fun i hi => ?_) σ.inj.injOn
  have hi' := (Finset.mem_filter.1 hi).2
  exact Finset.mem_product.2 ⟨Finset.mem_univ _, h _ _ hi' (σ.ok i)⟩

theorem countP_two (us : List UClass) (a b : UClass) (hab : a ≠ b) :
    us.countP (fun c => decide (c = a) || decide (c = b)) = us.count a + us.count b := by
  induction us with
  | nil => rfl
  | cons c t ih =>
      simp only [List.countP_cons, List.count_cons, ih, Bool.or_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      by_cases h1 : c = a
      · subst h1; simp [hab]; omega
      · by_cases h2 : c = b
        · subst h2; simp [h1]; omega
        · simp [h1, h2]

theorem countP_one (us : List UClass) (a : UClass) :
    us.countP (fun c => decide (c = a)) = us.count a := by
  induction us with
  | nil => rfl
  | cons c t ih =>
      simp only [List.countP_cons, List.count_cons, ih, decide_eq_true_eq, beq_iff_eq]

/-- **The port bound.** Every schedule of a list of micro-operations takes at least as many
cycles as the bound of its port counts. -/
theorem Schedule.bound_le {us : List UClass} {T : Nat} (σ : Schedule us T) :
    (Ports.ofList us).bound ≤ T := by
  have hshuf : us.count .shuf ≤ T := by
    have := σ.countP_le (fun c => decide (c = .shuf)) {.p5} (by
      intro c p hc hp
      simp only [decide_eq_true_eq] at hc
      subst hc
      cases p <;> simp_all [UClass.allowed])
    rw [countP_one] at this
    simpa using this
  have hfp : us.count .fp + us.count .shuf ≤ T * 2 := by
    have := σ.countP_le (fun c => decide (c = .fp) || decide (c = .shuf)) {.p0, .p5} (by
      intro c p hc hp
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc <;> subst hc <;> cases p <;> simp_all [UClass.allowed])
    rw [countP_two _ _ _ (by decide)] at this
    simpa using this
  have hload : us.count .load ≤ T * 2 := by
    have := σ.countP_le (fun c => decide (c = .load)) {.l0, .l1} (by
      intro c p hc hp
      simp only [decide_eq_true_eq] at hc
      subst hc
      cases p <;> simp_all [UClass.allowed])
    rw [countP_one] at this
    simpa using this
  have hstore : us.count .store ≤ T := by
    have := σ.countP_le (fun c => decide (c = .store)) {.s0} (by
      intro c p hc hp
      simp only [decide_eq_true_eq] at hc
      subst hc
      cases p <;> simp_all [UClass.allowed])
    rw [countP_one] at this
    simpa using this
  simp only [Ports.bound, Ports.ofList]
  omega

/-- **A block cannot run faster than its ports allow.** In the port model, every schedule of
the micro-operations of a block of instructions takes at least `(portsOf is).bound` cycles;
and `portsOf is` is the cost of the block as a query program (`cost_blockQ`). -/
theorem block_cycles_ge (is : List Instr) (T : Nat) (σ : Schedule (uopsOf is) T) :
    (portsOf is).bound ≤ T :=
  σ.bound_le

end LeanFFTW.Asm
