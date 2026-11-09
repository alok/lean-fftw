/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Instr
import LeanFFTW.Gen.Emit

/-!
# What the vector instructions compute

A model of the vector instructions the engine emits, over an abstract scalar type `α`
(a lane of a register, a word of memory). The model is the specification the checker
(`LeanFFTW/Asm/Check.lean`) is proved against; it is written from the Intel manual and is
part of the trusted base (`docs/TRUST.md`).

## The model

* A vector register is a function from lane numbers to scalars; an instruction of width `w`
  writes the lanes below `w.lanes` and zeroes the others (VEX/EVEX encodings).
* Memory is a function from word numbers (address / 8) to scalars. Operands are word
  aligned. The integer registers do not change inside a block of vector code, so an operand
  denotes a fixed word number: `ad m`.
* Arithmetic is the `Arith` of the kernels (`LeanFFTW.Gen.Arith`), so the theorems hold for
  every arithmetic satisfying the laws of `Machine.Lawful`: the exact one and binary64.
-/

namespace LeanFFTW.Asm

open LeanFFTW.Gen

/-- The scalars of the machine: the arithmetic of the kernels, the scalar with a given bit
pattern, and bitwise exclusive or. -/
structure Machine (α : Type) where
  A : Arith α
  ofBits : UInt64 → α
  xor : α → α → α

/-- Bits of `1.0`. -/
def oneBits : UInt64 := 0x3FF0000000000000

/-- The laws the checker uses. In binary64 arithmetic they hold bit for bit, except that
the payload of a NaN result may depend on the operand order (the result is a NaN either
way). `fma x 1 c` is `x + c` because the product by one is exact; a sign flip of a factor
negates the exact product, and negation is a flip of the sign bit. -/
structure Machine.Lawful {α : Type} (M : Machine α) : Prop where
  add_comm : ∀ x y, M.A.add x y = M.A.add y x
  mul_comm : ∀ x y, M.A.mul x y = M.A.mul y x
  fma_comm : ∀ x y c, M.A.fma x y c = M.A.fma y x c
  fms_comm : ∀ x y c, M.A.fms x y c = M.A.fms y x c
  fnma_comm : ∀ x y c, M.A.fnma x y c = M.A.fnma y x c
  fma_one : ∀ x c, M.A.fma x (M.ofBits oneBits) c = M.A.add x c
  fms_one : ∀ x c, M.A.fms x (M.ofBits oneBits) c = M.A.sub x c
  fma_neg : ∀ x y c, M.A.fma (M.A.neg x) y c = M.A.fnma x y c
  fnma_neg : ∀ x y c, M.A.fnma (M.A.neg x) y c = M.A.fma x y c
  neg_neg : ∀ x, M.A.neg (M.A.neg x) = x
  xor_sign : ∀ x, M.xor x (M.ofBits 0x8000000000000000) = M.A.neg x
  xor_zero : ∀ x, M.xor x (M.ofBits 0) = x
  /-- negation flips the sign bit -/
  ofBits_neg : ∀ b, M.ofBits (b ^^^ 0x8000000000000000) = M.A.neg (M.ofBits b)

/-- Vector registers (by number, then lane) and memory (by word number). -/
structure MState (α : Type) where
  reg : Nat → Nat → α
  mem : Int → α

variable {α : Type}

/-- The lanes of a source operand; `ad` gives the word number of a memory operand. -/
def MState.rd (ad : Mem → Int) (s : MState α) : VSrc → Nat → α
  | .reg r, l => s.reg r.n l
  | .mem m, l => s.mem (ad m + l)
  | .bcst m, _ => s.mem (ad m)

/-- Write a register at width `w`: the lanes above the width become zero. -/
def MState.setReg (M : Machine α) (s : MState α) (w : W) (r : VReg) (f : Nat → α) : MState α :=
  { s with reg := fun n l => if n = r.n then (if l < w.lanes then f l else M.ofBits 0) else s.reg n l }

/-- Write `w.lanes` words at word number `a`. -/
def MState.setMem (s : MState α) (w : W) (a : Int) (f : Nat → α) : MState α :=
  { s with mem := fun x => if a ≤ x ∧ x < a + w.lanes then f (x - a).toNat else s.mem x }

/-- One lane of a fused operation with factors `a`, `b` and addend `c`. -/
def fmaLane (M : Machine α) (op : VFma) (l : Nat) (a b c : α) : α :=
  match op with
  | .fmadd => M.A.fma a b c
  | .fmsub => M.A.fms a b c
  | .fnmadd => M.A.fnma a b c
  | .fmaddsub => if l % 2 = 0 then M.A.fms a b c else M.A.fma a b c
  | .fmsubadd => if l % 2 = 0 then M.A.fma a b c else M.A.fms a b c

/-- One lane of `dst = x op y`. -/
def binLane (M : Machine α) (op : VBin) (x y : Nat → α) (l : Nat) : α :=
  match op with
  | .add => M.A.add (x l) (y l)
  | .sub => M.A.sub (x l) (y l)
  | .mul => M.A.mul (x l) (y l)
  | .xor => M.xor (x l) (y l)
  | .unpcklo => if l % 2 = 0 then x l else y (l - 1)
  | .unpckhi => if l % 2 = 0 then x (l + 1) else y l

/-- `vshufpd`: in each pair of lanes, one lane of `x` (bit `l` of `imm` chooses which), then
one lane of `y` (bit `l + 1`). -/
def shufpdLane (imm : Nat) (x y : Nat → α) (l : Nat) : α :=
  if l % 2 = 0 then x (l + (imm >>> l) % 2) else y (l - 1 + (imm >>> l) % 2)

/-- `vshuff64x2`: pairs of lanes move together; the low half of the result is chosen from
`x`, the high half from `y`. -/
def shuffLane (w : W) (imm : Nat) (x y : Nat → α) (l : Nat) : α :=
  match w with
  | .z => (if l / 2 < 2 then x else y) (2 * ((imm >>> (2 * (l / 2))) % 4) + l % 2)
  | .y => (if l / 2 < 1 then x else y) (2 * ((imm >>> (l / 2)) % 2) + l % 2)
  | .x => x l

/-- The instructions of the model. The checker rejects every other instruction. -/
def Instr.modeled : Instr → Bool
  | .vmov .. | .vstore .. | .vbin .. | .vfma .. | .vshufpd .. | .vshuff64x2 .. | .vzero .. => true
  | _ => false

/-- Run one instruction. -/
def step (M : Machine α) (ad : Mem → Int) (s : MState α) : Instr → MState α
  | .vmov w d src => s.setReg M w d (s.rd ad src)
  | .vstore w m r => s.setMem w (ad m) (s.reg r.n)
  | .vbin op w d s1 s2 => s.setReg M w d (binLane M op (s.reg s1.n) (s.rd ad s2))
  | .vfma op form w d s2 s3 =>
      let x := s.reg d.n
      let y := s.reg s2.n
      let z := s.rd ad s3
      s.setReg M w d fun l =>
        match form with
        | .f132 => fmaLane M op l (x l) (z l) (y l)
        | .f213 => fmaLane M op l (y l) (x l) (z l)
        | .f231 => fmaLane M op l (y l) (z l) (x l)
  | .vshufpd w d s1 s2 imm => s.setReg M w d (shufpdLane imm (s.reg s1.n) (s.rd ad s2))
  | .vshuff64x2 w d s1 s2 imm => s.setReg M w d (shuffLane w imm (s.reg s1.n) (s.rd ad s2))
  | .vzero d => { s with reg := fun n l => if n = d.n then M.ofBits 0 else s.reg n l }
  | _ => s

/-- Run a block. -/
def run (M : Machine α) (ad : Mem → Int) (is : List Instr) (s : MState α) : MState α :=
  is.foldl (step M ad) s

end LeanFFTW.Asm
