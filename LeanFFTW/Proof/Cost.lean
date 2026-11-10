/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import Cslib.Algorithms.Lean.Query.FreeM
import LeanFFTW.Gen.OpCount
import LeanFFTW.Proof.Stockham

/-!
# The engine's cost model, as a CSLib query program

The Stockham schedule of the fast engine, written as a program in CSLib's free monad
(`Cslib.FreeM`) over the queries of the engine: a kernel operation on operand values, a
load, a store. CSLib gives the program two meanings, by its two interpreters:

* `FreeM.eval (EngineQ.honest A)` answers each query with the arithmetic `A`;
* `FreeM.cost oracle (EngineQ.weight W)` adds up the weight of each query asked.

We prove

* `eval_stockhamQ`: the evaluation is `stockhamWith`, the schedule that the assembly engine is
  tested against bit for bit and that `stockhamWith_exact` proves computes the DFT;
* `cost_stockhamQ`: for **every** oracle (every arithmetic, every data), the cost is
  `stockhamCost W fwd N rs`, the executable count that the planner uses
  (`LeanFFTW/Gen/OpCount.lean`).

So the planner's operation counts are theorems about the algorithm that runs, in the style
of CSLib's query complexity (`Cslib.Query`), rather than hand-written annotations.
-/

namespace LeanFFTW.Cost

open Cslib LeanFFTW.Gen

/-- The queries of the fast engine over scalars `α`. -/
inductive EngineQ (α : Type) : Type → Type where
  /-- one kernel operation, on the values `g` of the slots -/
  | op (o : KOp) (g : Nat → α) : EngineQ α α
  /-- read entry `i` of an array -/
  | load (z : Array α) (i : Nat) : EngineQ α α
  /-- write a value -/
  | store (v : α) : EngineQ α Unit

namespace EngineQ

/-- Answer each query with the arithmetic `A`. -/
def honest {α : Type} [Inhabited α] (A : Arith α) : {ι : Type} → EngineQ α ι → ι
  | _, .op o g => o.eval A g
  | _, .load z i => z.getD i default
  | _, .store _ => ()

/-- The weight of each query. -/
def weight {α : Type} (W : Weights) : {ι : Type} → EngineQ α ι → Nat
  | _, .op o _ => o.cost W
  | _, .load .. => W.load
  | _, .store _ => W.store

end EngineQ

variable {α : Type} [Inhabited α]

/-! ## The programs -/

/-- Run kernel operations, appending each result to the slots. -/
def slotsQ : List KOp → Array α → FreeM (EngineQ α) (Array α)
  | [], env => pure env
  | o :: os, env => do
      let v ← FreeM.lift (EngineQ.op o fun i => env.getD i default)
      slotsQ os (env.push v)

/-- Load two consecutive entries for each `r` in `l`, at `ia r` and `ib r`. -/
def loadPairsQ (z : Array α) (ia ib : Nat → Nat) : List Nat → Array α → FreeM (EngineQ α) (Array α)
  | [], acc => pure acc
  | r :: l, acc => do
      let a ← FreeM.lift (EngineQ.load z (ia r))
      let b ← FreeM.lift (EngineQ.load z (ib r))
      loadPairsQ z ia ib l ((acc.push a).push b)

/-- Load the inputs of butterfly `j` (as `bflyInputs`). -/
def bflyInputsQ (R ns N : Nat) (tw : Option (Array α)) (z : Array α) (j : Nat) :
    FreeM (EngineQ α) (Array α) := do
  let xs ← loadPairsQ z (fun r => 2 * (j + r * (N / R))) (fun r => 2 * (j + r * (N / R)) + 1)
    (List.range R) #[]
  match tw with
  | none => pure xs
  | some t =>
    loadPairsQ t (fun r => 2 * r * ns + j % ns) (fun r => (2 * r + 1) * ns + j % ns) (List.range (R - 1)) xs

/-- Store each value of a list. -/
def storeAllQ : List α → FreeM (EngineQ α) Unit
  | [] => pure ()
  | v :: vs => do FreeM.lift (EngineQ.store v); storeAllQ vs

/-- Butterfly `j` of a pass: load, compute, store. -/
def bflyQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) (j : Nat) :
    FreeM (EngineQ α) (Array α) := do
  let inp ← bflyInputsQ R ns N tw z j
  let env ← slotsQ k.ops.toList inp
  let out := k.outs.map fun o => env.getD o default
  storeAllQ out.toList
  pure out

/-- All butterflies of a pass, in order. -/
def bfliesQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) :
    List Nat → FreeM (EngineQ α) (List (Array α))
  | [] => pure []
  | j :: js => do
      let b ← bflyQ k R ns N tw z j
      let bs ← bfliesQ k R ns N tw z js
      pure (b :: bs)

/-- One Stockham pass (as `passWith`). -/
def passQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) :
    FreeM (EngineQ α) (Array α) := do
  let bs ← bfliesQ k R ns N tw z (List.range (N / R))
  let bfs := bs.toArray
  pure <| (Array.range (2 * N)).map fun i =>
    let c := i / 2
    let kk := c % ns
    let r := (c / ns) % R
    let b := c / (ns * R)
    (bfs.getD (b * ns + kk) #[]).getD (2 * r + i % 2) default

/-- Passes `ts` of the plan `rs` (as the loop of `stockhamWith`). -/
def passesQ (fwd : Bool) (N : Nat) (rs : Array Nat) (twOf : Nat → Array α) :
    List Nat → Array α → FreeM (EngineQ α) (Array α)
  | [], z => pure z
  | t :: ts, z => do
      let z' ← passQ (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1) (passNs rs t) N
        (if t ≥ 1 then some (twOf t) else none) z
      passesQ fwd N rs twOf ts z'

/-- The whole Stockham schedule of the plan `rs`, as a query program. -/
def stockhamQ (fwd : Bool) (N : Nat) (rs : Array Nat) (twOf : Nat → Array α) (z : Array α) :
    FreeM (EngineQ α) (Array α) :=
  passesQ fwd N rs twOf (List.range rs.size) z

/-! ## Evaluation: the program computes `stockhamWith` -/

section Eval

variable (A : Arith α)

theorem eval_slotsQ : ∀ (ops : List KOp) (env : Array α),
    FreeM.eval (EngineQ.honest A) (slotsQ ops env) =
      ops.foldl (fun env op => env.push (op.eval A fun i => env.getD i default)) env
  | [], _ => rfl
  | o :: os, env => by
    simp only [slotsQ, FreeM.eval_bind, FreeM.eval_lift, List.foldl_cons]
    exact eval_slotsQ os _

theorem eval_loadPairsQ (z : Array α) (ia ib : Nat → Nat) : ∀ (l : List Nat) (acc : Array α),
    FreeM.eval (EngineQ.honest A) (loadPairsQ z ia ib l acc) =
      l.foldl (fun acc r => (acc.push (z.getD (ia r) default)).push (z.getD (ib r) default)) acc
  | [], _ => rfl
  | r :: l, acc => by
    simp only [loadPairsQ, FreeM.eval_bind, FreeM.eval_lift, List.foldl_cons]
    exact eval_loadPairsQ z ia ib l _

theorem eval_bflyInputsQ (R ns N : Nat) (tw : Option (Array α)) (z : Array α) (j : Nat) :
    FreeM.eval (EngineQ.honest A) (bflyInputsQ R ns N tw z j) = bflyInputs R ns N tw z j := by
  cases tw with
  | none => simp [bflyInputsQ, bflyInputs, eval_loadPairsQ]
  | some t => simp [bflyInputsQ, bflyInputs, eval_loadPairsQ]

theorem eval_storeAllQ : ∀ (l : List α), FreeM.eval (EngineQ.honest A) (storeAllQ l) = ()
  | [] => rfl
  | _ :: _ => rfl

theorem eval_bflyQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) (j : Nat) :
    FreeM.eval (EngineQ.honest A) (bflyQ k R ns N tw z j) = k.eval A (bflyInputs R ns N tw z j) := by
  simp only [bflyQ, FreeM.eval_bind, FreeM.eval_pure, eval_bflyInputsQ, eval_slotsQ]
  simp [Kernel.eval, Kernel.slots, ← Array.foldl_toList]

theorem eval_bfliesQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) :
    ∀ js : List Nat, FreeM.eval (EngineQ.honest A) (bfliesQ k R ns N tw z js) =
      js.map fun j => k.eval A (bflyInputs R ns N tw z j)
  | [] => rfl
  | j :: js => by
    simp only [bfliesQ, FreeM.eval_bind, FreeM.eval_pure, eval_bflyQ, List.map_cons]
    rw [eval_bfliesQ k R ns N tw z js]

theorem eval_passQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) :
    FreeM.eval (EngineQ.honest A) (passQ k R ns N tw z) = passWith A k R ns N tw z := by
  simp only [passQ, FreeM.eval_bind, FreeM.eval_pure, eval_bfliesQ, passWith]
  congr 1
  funext i
  congr 2
  apply Array.ext <;> simp

theorem eval_passesQ (fwd : Bool) (N : Nat) (rs : Array Nat) (twOf : Nat → Array α) :
    ∀ (ts : List Nat) (z : Array α), FreeM.eval (EngineQ.honest A) (passesQ fwd N rs twOf ts z) =
      ts.foldl (fun z t => passWith A (butterflyK fwd (rs.getD t 1) (t ≥ 1)) (rs.getD t 1)
        (passNs rs t) N (if t ≥ 1 then some (twOf t) else none) z) z
  | [], _ => rfl
  | t :: ts, z => by
    simp only [passesQ, FreeM.eval_bind, eval_passQ, List.foldl_cons]
    exact eval_passesQ fwd N rs twOf ts _

/-- **The query program computes the fast engine's schedule.** Answered by an arithmetic
`A`, `stockhamQ` returns `stockhamWith A`: over binary64 this is the reference the assembly engine
matches bit for bit, over exact reals it is the DFT (`stockhamWith_exact`). -/
theorem eval_stockhamQ (fwd : Bool) (N : Nat) (rs : Array Nat) (twOf : Nat → Array α)
    (z : Array α) :
    FreeM.eval (EngineQ.honest A) (stockhamQ fwd N rs twOf z) = stockhamWith A fwd N rs twOf z := by
  rw [stockhamQ, eval_passesQ, stockhamWith_eq_foldl]

end Eval

/-! ## Cost: the program's query cost is `stockhamCost`, for every oracle -/

section Cost

variable (oracle : {ι : Type} → EngineQ α ι → ι) (W : Weights)

theorem cost_slotsQ : ∀ (ops : List KOp) (env : Array α),
    FreeM.cost oracle (EngineQ.weight W) (slotsQ ops env) = opsCost W ops
  | [], _ => by simp [slotsQ, opsCost]
  | o :: os, env => by
    simp only [slotsQ, FreeM.cost_bind, FreeM.cost_lift, cost_slotsQ os]
    simp [opsCost, EngineQ.weight]

omit [Inhabited α] in
theorem cost_loadPairsQ (z : Array α) (ia ib : Nat → Nat) : ∀ (l : List Nat) (acc : Array α),
    FreeM.cost oracle (EngineQ.weight W) (loadPairsQ z ia ib l acc) = 2 * l.length * W.load
  | [], _ => by simp [loadPairsQ]
  | r :: l, acc => by
    simp only [loadPairsQ, FreeM.cost_bind, FreeM.cost_lift, cost_loadPairsQ z ia ib l,
      EngineQ.weight, List.length_cons]
    ring

omit [Inhabited α] in
theorem cost_bflyInputsQ (R ns N : Nat) (tw : Option (Array α)) (z : Array α) (j : Nat) :
    FreeM.cost oracle (EngineQ.weight W) (bflyInputsQ R ns N tw z j) =
      bflyLoads R tw.isSome * W.load := by
  cases tw with
  | none => simp [bflyInputsQ, cost_loadPairsQ, bflyLoads]
  | some t =>
    simp only [bflyInputsQ, FreeM.cost_bind, cost_loadPairsQ, bflyLoads,
      Option.isSome_some, ite_true, List.length_range]
    ring

omit [Inhabited α] in
theorem cost_storeAllQ : ∀ (l : List α),
    FreeM.cost oracle (EngineQ.weight W) (storeAllQ l) = l.length * W.store
  | [] => by simp [storeAllQ]
  | v :: vs => by
    simp only [storeAllQ, FreeM.cost_bind, FreeM.cost_lift, cost_storeAllQ vs, EngineQ.weight,
      List.length_cons]
    ring

theorem cost_bflyQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) (j : Nat) :
    FreeM.cost oracle (EngineQ.weight W) (bflyQ k R ns N tw z j) = bflyCost W k R tw.isSome := by
  simp only [bflyQ, FreeM.cost_bind, FreeM.cost_pure, cost_bflyInputsQ, cost_slotsQ,
    cost_storeAllQ, bflyCost]
  simp [Nat.add_assoc]

theorem cost_bfliesQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) :
    ∀ js : List Nat, FreeM.cost oracle (EngineQ.weight W) (bfliesQ k R ns N tw z js) =
      js.length * bflyCost W k R tw.isSome
  | [] => by simp [bfliesQ]
  | j :: js => by
    simp only [bfliesQ, FreeM.cost_bind, FreeM.cost_pure, cost_bflyQ, cost_bfliesQ k R ns N tw z js,
      List.length_cons]
    ring

theorem cost_passQ (k : Kernel) (R ns N : Nat) (tw : Option (Array α)) (z : Array α) :
    FreeM.cost oracle (EngineQ.weight W) (passQ k R ns N tw z) = (N / R) * bflyCost W k R tw.isSome := by
  simp [passQ, cost_bfliesQ]

theorem cost_passesQ (fwd : Bool) (N : Nat) (rs : Array Nat) (twOf : Nat → Array α) :
    ∀ (ts : List Nat) (z : Array α), FreeM.cost oracle (EngineQ.weight W) (passesQ fwd N rs twOf ts z) =
      (ts.map (passCost W fwd N rs)).sum
  | [], _ => by simp [passesQ]
  | t :: ts, z => by
    simp only [passesQ, FreeM.cost_bind, cost_passQ, cost_passesQ fwd N rs twOf ts,
      List.map_cons, List.sum_cons, passCost]
    congr 2
    by_cases h : t ≥ 1 <;> simp [h]

/-- **The planner's operation count is the cost of the algorithm.** For every oracle, the
weighted query cost of the Stockham program is `stockhamCost W fwd N rs`: the arithmetic
operations of the generated kernels, the loads and the stores, each counted once per
execution. The count does not depend on the data or on the arithmetic answering the
queries. -/
theorem cost_stockhamQ (fwd : Bool) (N : Nat) (rs : Array Nat) (twOf : Nat → Array α)
    (z : Array α) :
    FreeM.cost oracle (EngineQ.weight W) (stockhamQ fwd N rs twOf z) = stockhamCost W fwd N rs := by
  rw [stockhamQ, cost_passesQ, stockhamCost]

end Cost

/-- Both meanings at once, over exact arithmetic: the program that `stockhamCost` counts
computes the DFT. -/
theorem stockhamQ_dft_and_cost (fwd : Bool) (rs : Array ℕ) (hrs : ∀ r ∈ rs, 0 < r) (N : ℕ)
    (hN : N = rs.toList.prod) (z : Array ℝ) (hz : z.size = 2 * N) (W : Weights)
    (oracle : {ι : Type} → EngineQ ℝ ι → ι) :
    FreeM.eval (EngineQ.honest realArith) (stockhamQ fwd N rs (exactTwOf fwd N rs) z) =
      ((Array.range (2 * N)).map fun i =>
        let y := dftSum fwd N (fun j => ⟨z.getD (2 * j) 0, z.getD (2 * j + 1) 0⟩) (i / 2)
        if i % 2 = 0 then y.re else y.im) ∧
    FreeM.cost oracle (EngineQ.weight W) (stockhamQ fwd N rs (exactTwOf fwd N rs) z) =
      stockhamCost W fwd N rs :=
  ⟨by rw [eval_stockhamQ, stockhamWith_exact fwd rs hrs N hN z hz], cost_stockhamQ oracle W _ _ _ _ _⟩

end LeanFFTW.Cost
