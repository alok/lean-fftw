/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/

/-!
# A typed x86-64 assembly language, embedded in Lean

The instruction subset the FFT engine is written in: AVX-512 / AVX2 / FMA arithmetic on
packed doubles, the shuffles of the data-movement steps, and the integer instructions of
loops and address arithmetic. Operands are typed (general-purpose registers, vector
registers with a width, mask registers, memory operands), so an instruction with an
ill-formed operand is not a value of `Instr`.

Programs are values of this type built by Lean functions (`LeanFFTW/Asm/Build.lean`);
`Instr.print` writes them in GNU assembler syntax. No C compiler is involved: the
instructions printed here are the instructions the processor runs.

The semantics of the data instructions (everything in a loop body) is
`LeanFFTW/Asm/Sem.lean`.
-/

namespace LeanFFTW.Asm

/-- 64-bit general-purpose registers. -/
inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Gpr

def name : Gpr → String
  | rax => "rax" | rcx => "rcx" | rdx => "rdx" | rbx => "rbx" | rsp => "rsp" | rbp => "rbp"
  | rsi => "rsi" | rdi => "rdi" | r8 => "r8" | r9 => "r9" | r10 => "r10" | r11 => "r11"
  | r12 => "r12" | r13 => "r13" | r14 => "r14" | r15 => "r15"

/-- Name of the low 32 bits. -/
def name32 : Gpr → String
  | rax => "eax" | rcx => "ecx" | rdx => "edx" | rbx => "ebx" | rsp => "esp" | rbp => "ebp"
  | rsi => "esi" | rdi => "edi" | r8 => "r8d" | r9 => "r9d" | r10 => "r10d" | r11 => "r11d"
  | r12 => "r12d" | r13 => "r13d" | r14 => "r14d" | r15 => "r15d"

/-- Callee-saved in the System V ABI. -/
def calleeSaved : Gpr → Bool
  | rbx | rbp | r12 | r13 | r14 | r15 => true
  | _ => false

end Gpr

/-- Vector width: 128, 256 or 512 bits (2, 4 or 8 doubles). -/
inductive W where
  | x | y | z
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Number of doubles. -/
def W.lanes : W → Nat
  | .x => 2 | .y => 4 | .z => 8

def W.bytes (w : W) : Nat := 8 * w.lanes

/-- A vector register `xmm/ymm/zmm n`, `n < 32`. -/
structure VReg where
  n : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

def VReg.name (r : VReg) (w : W) : String :=
  match w with
  | .x => s!"xmm{r.n}" | .y => s!"ymm{r.n}" | .z => s!"zmm{r.n}"

/-- A mask register `k1 … k7`. -/
structure KReg where
  n : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A memory operand: `[base + index·scale + disp]`, or `[rip + label + disp]`. -/
structure Mem where
  base : Option Gpr := none
  index : Option (Gpr × Nat) := none
  disp : Int := 0
  label : Option String := none
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Mem

def b (r : Gpr) (disp : Int := 0) : Mem := { base := some r, disp }
def bi (r i : Gpr) (scale : Nat := 1) (disp : Int := 0) : Mem :=
  { base := some r, index := some (i, scale), disp }
def rip (l : String) (disp : Int := 0) : Mem := { label := some l, disp }

def addDisp (m : Mem) (d : Int) : Mem := { m with disp := m.disp + d }

/-- The bracketed address expression. -/
def addr (m : Mem) : String :=
  let parts : List String :=
    (match m.label with
      | some l => ["rip", l]
      | none => []) ++
    (match m.base with
      | some r => [r.name]
      | none => []) ++
    (match m.index with
      | some (i, s) => [if s == 1 then i.name else s!"{i.name}*{s}"]
      | none => [])
  let body := " + ".intercalate parts
  let d := if m.disp == 0 then "" else if m.disp > 0 then s!" + {m.disp}" else s!" - {-m.disp}"
  s!"[{body}{d}]"

def sized (m : Mem) (w : W) : String :=
  (match w with
    | .x => "xmmword ptr " | .y => "ymmword ptr " | .z => "zmmword ptr ") ++ m.addr

def qword (m : Mem) : String := "qword ptr " ++ m.addr
def dword (m : Mem) : String := "dword ptr " ++ m.addr

end Mem

/-- The last source operand of a vector instruction: a register, a full-width memory
operand, or one double broadcast to every lane (`{1toN}`, EVEX only). -/
inductive VSrc where
  | reg (r : VReg)
  | mem (m : Mem)
  | bcst (m : Mem)
  deriving DecidableEq, Repr, Inhabited

def VSrc.print (s : VSrc) (w : W) : String :=
  match s with
  | .reg r => r.name w
  | .mem m => m.sized w
  | .bcst m => m.qword ++ "{1to" ++ toString w.lanes ++ "}"

/-- Lane-wise binary operations `dst = s1 op s2` (non-destructive, three operands). -/
inductive VBin where
  | add | sub | mul
  /-- bitwise xor (sign flips) -/
  | xor
  /-- per 128-bit lane: `(s1.lo, s2.lo)` -/
  | unpcklo
  /-- per 128-bit lane: `(s1.hi, s2.hi)` -/
  | unpckhi
  deriving DecidableEq, Repr, Inhabited, Hashable

def VBin.mnemonic : VBin → String
  | .add => "vaddpd" | .sub => "vsubpd" | .mul => "vmulpd" | .xor => "vxorpd"
  | .unpcklo => "vunpcklpd" | .unpckhi => "vunpckhpd"

def VBin.comm : VBin → Bool
  | .add | .mul | .xor => true
  | _ => false

/-- Fused multiply-add families, each with one rounding. For factors `a, b` and addend `c`:
`fmadd = a·b + c`, `fmsub = a·b − c`, `fnmadd = −(a·b) + c`,
`fmaddsub` = `a·b − c` in even lanes and `a·b + c` in odd lanes, `fmsubadd` the reverse. -/
inductive VFma where
  | fmadd | fmsub | fnmadd | fmaddsub | fmsubadd
  deriving DecidableEq, Repr, Inhabited, Hashable

def VFma.stem : VFma → String
  | .fmadd => "vfmadd" | .fmsub => "vfmsub" | .fnmadd => "vfnmadd"
  | .fmaddsub => "vfmaddsub" | .fmsubadd => "vfmsubadd"

/-- Operand roles of the three encodings of a fused operation with operands
`(dst, s2, s3)`: `f132`: `dst·s3 ± s2`; `f213`: `s2·dst ± s3`; `f231`: `s2·s3 ± dst`. -/
inductive FmaForm where
  | f132 | f213 | f231
  deriving DecidableEq, Repr, Inhabited, Hashable

def FmaForm.digits : FmaForm → String
  | .f132 => "132" | .f213 => "213" | .f231 => "231"

/-- Condition codes of the branches used. -/
inductive CC where
  | e | ne | b | ae | a | be | l | ge
  deriving DecidableEq, Repr, Inhabited

def CC.name : CC → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae" | .a => "a" | .be => "be"
  | .l => "l" | .ge => "ge"

/-- Integer source operand. -/
inductive GSrc where
  | reg (r : Gpr)
  | imm (v : Int)
  | mem (m : Mem)
  deriving DecidableEq, Repr, Inhabited

def GSrc.print : GSrc → String
  | .reg r => r.name
  | .imm v => toString v
  | .mem m => m.qword

/-- Instructions. -/
inductive Instr where
  -- vector data instructions
  /-- `dst = src` (register copy, load, or broadcast of one double) -/
  | vmov (w : W) (dst : VReg) (src : VSrc)
  /-- store -/
  | vstore (w : W) (dst : Mem) (src : VReg)
  /-- masked load, inactive lanes zero (`vmovupd dst{k}{z}, m`) -/
  | vloadz (w : W) (dst : VReg) (k : KReg) (m : Mem)
  /-- masked store (`vmovupd m{k}, src`) -/
  | vstorek (w : W) (dst : Mem) (k : KReg) (src : VReg)
  | vbin (op : VBin) (w : W) (dst s1 : VReg) (s2 : VSrc)
  | vfma (op : VFma) (form : FmaForm) (w : W) (dst s2 : VReg) (s3 : VSrc)
  /-- per 128-bit lane `i`: `(s1[2i + imm_{2i}], s2[2i + imm_{2i+1}])` -/
  | vshufpd (w : W) (dst s1 : VReg) (s2 : VSrc) (imm : Nat)
  /-- 128-bit lanes: low half of `dst` from `s1`, high half from `s2`, selected by `imm`
  (2 bits per lane for `zmm`, 1 bit for `ymm`) -/
  | vshuff64x2 (w : W) (dst s1 : VReg) (s2 : VSrc) (imm : Nat)
  /-- `dst[i] = (dst ++ s2)[idx[i]]`: the first table is overwritten -/
  | vpermt2pd (w : W) (dst idx : VReg) (s2 : VSrc)
  /-- `dst[i] = (s1 ++ s2)[dst[i]]`: the index is overwritten -/
  | vpermi2pd (w : W) (dst s1 : VReg) (s2 : VSrc)
  /-- `(s1 − s2)` in even lanes, `(s1 + s2)` in odd lanes (VEX: `xmm`, `ymm` 0–15 only) -/
  | vaddsubpd (w : W) (dst s1 : VReg) (s2 : VSrc)
  /-- zero a register -/
  | vzero (dst : VReg)
  | vzeroupper
  /-- `k = low 8 bits of r` -/
  | kmov (k : KReg) (r : Gpr)
  -- integer and control instructions
  | mov (dst : Gpr) (src : GSrc)
  /-- `dst = zero-extended 32-bit load` -/
  | mov32 (dst : Gpr) (m : Mem)
  | store (dst : Mem) (src : Gpr)
  | lea (dst : Gpr) (m : Mem)
  | add (dst : Gpr) (src : GSrc)
  | sub (dst : Gpr) (src : GSrc)
  | imul (dst src : Gpr) (imm : Int)
  /-- `dst *= src` -/
  | imul2 (dst : Gpr) (src : GSrc)
  /-- unsigned `rdx:rax / r`: quotient in `rax`, remainder in `rdx` -/
  | div (r : Gpr)
  | shl (dst : Gpr) (imm : Nat)
  | shr (dst : Gpr) (imm : Nat)
  | and (dst : Gpr) (src : GSrc)
  | neg (dst : Gpr)
  | dec (dst : Gpr)
  | inc (dst : Gpr)
  /-- `dec qword ptr [m]` (sets the zero flag as `dec` does) -/
  | decMem (m : Mem)
  /-- atomic increment and decrement of a word of memory; `lockInc32`: of a 32-bit word -/
  | lockInc (m : Mem)
  | lockDec (m : Mem)
  | lockInc32 (m : Mem)
  /-- spin-wait hint -/
  | pause
  /-- prefetch the cache line of `m`: `lvl` 0, 1, 2 for `prefetcht0/1/2`, 3 for `prefetchw` -/
  | prefetch (lvl : Nat) (m : Mem)
  /-- copy `rcx` bytes from `[rsi]` to `[rdi]` -/
  | repMovsb
  /-- store `rax` in the `rcx` words at `[rdi]` -/
  | repStosq
  | syscall
  | cmp (a : Gpr) (b : GSrc)
  | test (a b : Gpr)
  /-- `dst = src` if the condition holds -/
  | cmov (cc : CC) (dst src : Gpr)
  | jcc (cc : CC) (label : String)
  | jmp (label : String)
  | jmpMem (m : Mem)
  | jmpReg (r : Gpr)
  | call (label : String)
  | callReg (r : Gpr)
  | callMem (m : Mem)
  | ret
  | push (r : Gpr)
  | pop (r : Gpr)
  -- assembler directives
  | label (name : String)
  | align (n : Nat)
  | directive (text : String)
  | comment (text : String)
  deriving Repr, Inhabited

namespace Instr

def vreg3 (m : String) (w : W) (d s1 : VReg) (s2 : VSrc) : String :=
  s!"\t{m} {d.name w}, {s1.name w}, {s2.print w}"

/-- GNU assembler text (Intel syntax, `.intel_syntax noprefix`). -/
def print : Instr → String
  | vmov w d (.reg s) => s!"\tvmovapd {d.name w}, {s.name w}"
  | vmov w d (.mem m) => s!"\tvmovupd {d.name w}, {m.sized w}"
  | vmov w d (.bcst m) =>
      match w with
      | .x => s!"\tvmovddup {d.name w}, {m.qword}"
      | _ => s!"\tvbroadcastsd {d.name w}, {m.qword}"
  | vstore w m s => s!"\tvmovupd {m.sized w}, {s.name w}"
  | vloadz w d k m => s!"\tvmovupd {d.name w}\{k{k.n}}\{z}, {m.sized w}"
  | vstorek w m k s => s!"\tvmovupd {m.sized w}\{k{k.n}}, {s.name w}"
  | vbin op w d s1 s2 => vreg3 op.mnemonic w d s1 s2
  | vfma op form w d s2 s3 => vreg3 (op.stem ++ form.digits ++ "pd") w d s2 s3
  | vshufpd w d s1 s2 imm => vreg3 "vshufpd" w d s1 s2 ++ s!", {imm}"
  | vshuff64x2 w d s1 s2 imm => vreg3 "vshuff64x2" w d s1 s2 ++ s!", {imm}"
  | vpermt2pd w d i s2 => vreg3 "vpermt2pd" w d i s2
  | vpermi2pd w d s1 s2 => vreg3 "vpermi2pd" w d s1 s2
  | vaddsubpd w d s1 s2 => vreg3 "vaddsubpd" w d s1 s2
  | vzero d =>
      if d.n < 16 then s!"\tvxorpd xmm{d.n}, xmm{d.n}, xmm{d.n}"
      else s!"\tvpxord zmm{d.n}, zmm{d.n}, zmm{d.n}"
  | vzeroupper => "\tvzeroupper"
  | kmov k r => s!"\tkmovb k{k.n}, {r.name32}"
  | mov d s => s!"\tmov {d.name}, {s.print}"
  | mov32 d m => s!"\tmov {d.name32}, {m.dword}"
  | store m s => s!"\tmov {m.qword}, {s.name}"
  | lea d m => s!"\tlea {d.name}, {m.addr}"
  | add d s => s!"\tadd {d.name}, {s.print}"
  | sub d s => s!"\tsub {d.name}, {s.print}"
  | imul d s imm => s!"\timul {d.name}, {s.name}, {imm}"
  | imul2 d s => s!"\timul {d.name}, {s.print}"
  | div r => s!"\tdiv {r.name}"
  | shl d imm => s!"\tshl {d.name}, {imm}"
  | shr d imm => s!"\tshr {d.name}, {imm}"
  | and d s => s!"\tand {d.name}, {s.print}"
  | neg d => s!"\tneg {d.name}"
  | dec d => s!"\tdec {d.name}"
  | inc d => s!"\tinc {d.name}"
  | decMem m => s!"\tdec {m.qword}"
  | lockInc m => s!"\tlock inc {m.qword}"
  | lockDec m => s!"\tlock dec {m.qword}"
  | lockInc32 m => s!"\tlock inc {m.dword}"
  | pause => "\tpause"
  | prefetch lvl m =>
      s!"\tprefetch{match lvl with | 0 => "t0" | 1 => "t1" | 2 => "t2" | _ => "w"} byte ptr {m.addr}"
  | repMovsb => "\trep movsb"
  | repStosq => "\trep stosq"
  | syscall => "\tsyscall"
  | cmp a b => s!"\tcmp {a.name}, {b.print}"
  | test a b => s!"\ttest {a.name}, {b.name}"
  | cmov cc d s => s!"\tcmov{cc.name} {d.name}, {s.name}"
  | jcc cc l => s!"\tj{cc.name} {l}"
  | jmp l => s!"\tjmp {l}"
  | jmpMem m => s!"\tjmp {m.qword}"
  | jmpReg r => s!"\tjmp {r.name}"
  | call l => s!"\tcall {l}"
  | callReg r => s!"\tcall {r.name}"
  | callMem m => s!"\tcall {m.qword}"
  | ret => "\tret"
  | push r => s!"\tpush {r.name}"
  | pop r => s!"\tpop {r.name}"
  | label n => s!"{n}:"
  | align n => s!"\t.p2align {Nat.log2 n}"
  | directive t => s!"\t{t}"
  | comment t => s!"\t# {t}"

end Instr

end LeanFFTW.Asm
