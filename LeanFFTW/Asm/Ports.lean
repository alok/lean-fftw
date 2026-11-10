/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Instr

/-!
# What a block of vector code asks of the processor

The cost of a block of 512-bit code is not one number. The processor has a few execution
ports, each micro-operation can only run on some of them, and a block is as slow as its
scarcest port. This file gives each instruction its micro-operations by class (`Instr.uops`)
and adds them up as a vector of counts (`Ports`).

`Ports.bound` is the number of cycles that vector forces. That it is a lower bound for every
schedule of the micro-operations is proved in `LeanFFTW/Proof/Ports.lean`
(`block_cycles_ge`), where the block is also a query program whose cost is this vector.

## The model

512-bit code on the Intel cores this engine targets (Sunny Cove to Raptor Cove):

* arithmetic (add, subtract, multiply, fused multiply-add, xor) runs on either of two ports;
* shuffles (`unpck`, `shufpd`, `shuff64x2`, `permt2pd`) run on one port only, and that port
  is one of the two arithmetic ports;
* two loads start per cycle; a memory operand of an arithmetic or shuffle instruction is a
  load of its own;
* one 512-bit store completes per cycle.

Instructions the model does not know (register copies, which the renamer removes; integer
and control instructions) count as nothing, so the bound stays a lower bound.
-/

namespace LeanFFTW.Asm

/-- Classes of micro-operations. -/
inductive UClass where
  /-- arithmetic: either of the two 512-bit execution ports -/
  | fp
  /-- a shuffle: the shuffle port only -/
  | shuf
  | load
  | store
  deriving DecidableEq, Repr, Inhabited

/-- The load of a memory operand. -/
def VSrc.loadUops : VSrc → List UClass
  | .reg _ => []
  | .mem _ | .bcst _ => [.load]

/-- Shuffles among the two-operand instructions. -/
def VBin.isShuffle : VBin → Bool
  | .unpcklo | .unpckhi => true
  | _ => false

/-- The micro-operations of an instruction, by class. -/
def Instr.uops : Instr → List UClass
  | .vmov _ _ src => src.loadUops
  | .vloadz .. => [.load]
  | .vstore .. | .vstorek .. => [.store]
  | .vbin op _ _ _ s => (if op.isShuffle then .shuf else .fp) :: s.loadUops
  | .vfma _ _ _ _ _ s | .vaddsubpd _ _ _ s => .fp :: s.loadUops
  | .vshufpd _ _ _ s _ | .vshuff64x2 _ _ _ s _ | .vpermt2pd _ _ _ s | .vpermi2pd _ _ _ s =>
      .shuf :: s.loadUops
  | _ => []

/-- Numbers of micro-operations by class. -/
structure Ports where
  fp : Nat := 0
  shuf : Nat := 0
  load : Nat := 0
  store : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Ports

def add (a b : Ports) : Ports :=
  ⟨a.fp + b.fp, a.shuf + b.shuf, a.load + b.load, a.store + b.store⟩

instance : Add Ports := ⟨add⟩

/-- Count a list of micro-operations. -/
def ofList (us : List UClass) : Ports :=
  ⟨us.count .fp, us.count .shuf, us.count .load, us.count .store⟩

/-- The cycles a vector of counts forces: every shuffle needs the shuffle port; arithmetic
and shuffles share two ports; two loads and one store per cycle. -/
def bound (p : Ports) : Nat :=
  max (max p.shuf ((p.fp + p.shuf + 1) / 2)) (max ((p.load + 1) / 2) p.store)

def print (p : Ports) : String :=
  s!"arith {p.fp} shuffle {p.shuf} load {p.load} store {p.store} bound {p.bound}"

end Ports

/-- The micro-operations of a block. -/
def uopsOf (is : List Instr) : List UClass := is.flatMap Instr.uops

/-- The counts of a block. -/
def portsOf (is : List Instr) : Ports := Ports.ofList (uopsOf is)

end LeanFFTW.Asm
