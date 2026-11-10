/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Alloc
import LeanFFTW.Asm.Check

/-!
# Building assembly functions

`FnM` is a small macro-assembler monad: integer and control instructions are appended as
they are (the author picks the general-purpose registers, as in hand-written assembly),
and straight-line vector code is appended as blocks over virtual registers (`BlockM`),
which `Fn.finish` passes through the register allocator.

## Calling convention of generated functions

Every generated function takes `rdi = ctx` (a record whose first word is the function's
own address and whose other words are its parameters), `rsi = in`, `rdx = out`. Functions
may clobber every vector register and the caller-saved general-purpose registers; they save
the callee-saved ones they use. A plan is a sequence of such records
(`LeanFFTW/Asm/Exec.lean`).
-/

namespace LeanFFTW.Asm

open Std

/-- Building a block. -/
structure BState where
  stmts : Array VStmt := #[]
  nextV : Nat

abbrev BlockM := StateM BState

namespace BlockM

/-- Define a value. -/
def df (op : VOp) : BlockM VId :=
  modifyGet fun s => (s.nextV, { stmts := s.stmts.push (.df s.nextV op), nextV := s.nextV + 1 })

def store (m : Mem) (v : VId) : BlockM Unit :=
  modify fun s => { s with stmts := s.stmts.push (.store m v) }

def storek (m : Mem) (k : KReg) (v : VId) : BlockM Unit :=
  modify fun s => { s with stmts := s.stmts.push (.storek m k v) }

def load (m : Mem) : BlockM VId := df (.load m)
def bin (op : VBin) (a b : VId) : BlockM VId := df (.bin op a b)

end BlockM

inductive Item where
  | i (ins : Instr)
  /-- a block of vector code and what it must compute (`LeanFFTW/Asm/Check.lean`) -/
  | blk (b : VBlock) (spec : Option Spec)
  deriving Inhabited

structure FnState where
  name : String
  items : Array Item := #[]
  nextV : Nat := 0
  nextL : Nat := 0
  /-- constants held in fixed registers for the whole function -/
  pins : Array (VId × VReg × W × VOp) := #[]
  /-- callee-saved registers the function uses -/
  saved : List Gpr := []
  /-- 8-byte integer slots at the bottom of the frame (`[rsp + 8i]`) -/
  gslots : Nat := 0
  foldLimit : Nat := 2
  sched : Nat := 1
  metric : Nat := 0
  foldAlso : List Nat := []
  constAlso : List Nat := []

abbrev FnM := StateM FnState

namespace FnM

def ins (i : Instr) : FnM Unit := modify fun s => { s with items := s.items.push (.i i) }

def freshLabel : FnM String :=
  modifyGet fun s => (s!".L{s.name}_{s.nextL}", { s with nextL := s.nextL + 1 })

/-- Declare the use of callee-saved registers (saved in the prologue). -/
def save (rs : List Gpr) : FnM Unit :=
  modify fun s => { s with saved := s.saved ++ rs.filter fun r => !s.saved.contains r }

/-- A new 8-byte slot in the frame, for an integer the function keeps in memory. -/
def gslot : FnM Mem :=
  modifyGet fun s => (Mem.b .rsp (8 * s.gslots), { s with gslots := s.gslots + 1 })

/-- Append a block of vector code. With a specification, the instructions emitted for the
block are checked against it, and generation fails if the check does. -/
def block {α : Type} (w : W) (body : BlockM α) (spec : Option Spec := none) : FnM α :=
  modifyGet fun s =>
    let (a, b) := body.run { nextV := s.nextV }
    (a, { s with items := s.items.push (.blk ⟨w, b.stmts⟩ spec), nextV := b.nextV })

/-- A constant kept in a register for the whole function (registers are taken from
`zmm31` downward). -/
def pin (w : W) (op : VOp) : FnM VId :=
  modifyGet fun s =>
    let r : VReg := ⟨31 - s.pins.size⟩
    (s.nextV, { s with pins := s.pins.push (s.nextV, r, w, op), nextV := s.nextV + 1 })

/-- `do body while (cc)` where `cond` sets the flags. -/
def doWhile (body : FnM Unit) (cond : FnM Unit) (cc : CC) : FnM Unit := do
  let l ← freshLabel
  ins (.align 16)
  ins (.label l)
  body
  cond
  ins (.jcc cc l)

/-- Repeat `body` `ctr` times (`ctr ≥ 1`), counting `ctr` down to zero. -/
def repeatDown (ctr : Gpr) (body : FnM Unit) : FnM Unit :=
  doWhile body (ins (.dec ctr)) .ne

end FnM

/-- Allocatable registers for a width: `zmm` code prefers 16–31 (leaving 0–15 clean avoids
`vzeroupper`), narrower code prefers 0–15 (shorter VEX encodings). -/
def regOrder (w : W) (npins : Nat) : Array VReg :=
  let hi := (Array.range (16 - npins)).map fun i => (⟨16 + i⟩ : VReg)
  let lo := (Array.range 16).map fun i => (⟨i⟩ : VReg)
  if w == .z then hi ++ lo else lo ++ hi

structure Fn where
  name : String
  instrs : Array Instr
  /-- blocks checked against a specification, and blocks without one -/
  checked : Nat := 0
  unchecked : Nat := 0
  /-- the checked blocks: specification, width, instructions (kept for the tests) -/
  blocks : Array (Spec × W × Array Instr) := #[]

/-- The constants of a pool, by label. -/
def Pool.consts (p : Pool) : String → Option (Array UInt64) :=
  let m : HashMap String (Array UInt64) :=
    (List.range p.vecs.size).foldl (fun m i => m.insert s!".LV{i}" p.vecs[i]!) {}
  let m := p.quads.foldl (fun m b => m.insert (".LQ" ++ hexDigits b.toNat 16) #[b]) m
  fun l => m[l]?

/-- Allocate registers for the blocks and add the prologue and epilogue. -/
def FnState.finish (s : FnState) (pool : Pool) (global : Bool := true) :
    Except String (Fn × Pool) := do
  let pinned : HashMap VId VReg := s.pins.foldl (fun m (v, r, _, _) => m.insert v r) {}
  let mut pool := pool
  let mut body : Array Instr := #[]
  let mut nSlots := 0
  let mut dirty := false
  let mut checked := 0
  let mut unchecked := 0
  let mut blocks : Array (Spec × W × Array Instr) := #[]
  -- integer slots, rounded up to whole 64-byte lines
  let gBytes := 64 * ((s.gslots + 7) / 8)
  for it in s.items do
    match it with
    | .i ins => body := body.push ins
    | .blk b spec =>
        let cfg : ACfg := { w := b.w, regs := regOrder b.w s.pins.size, pinned,
                            foldLimit := s.foldLimit, sched := s.sched, slotBase := gBytes,
                            metric := s.metric, foldAlso := s.foldAlso, constAlso := s.constAlso }
        let a ← (allocBlock cfg b pool).mapError fun e => s!"{s.name}: {e}"
        pool := a.pool
        match spec with
        | some sp =>
            unless check pool.consts sp b.w a.instrs.toList do
              throw s!"{s.name}: a block does not compute its specification ({checkWhy pool.consts sp b.w a.instrs.toList})"
            checked := checked + 1
            blocks := blocks.push (sp, b.w, a.instrs)
        | none => unchecked := unchecked + 1
        body := body ++ a.instrs
        nSlots := max nSlots a.nSlots
        if b.w != .x && a.touched % 65536 != 0 then dirty := true
  let mut pre : Array Instr := #[.align 64]
  if global then
    pre := pre.push (.directive s!".globl {s.name}")
  pre := pre ++ #[.directive s!".type {s.name}, @function", .label s.name]
  for r in s.saved do pre := pre.push (.push r)
  -- frame: `[rsp, rsp + gBytes)` integer slots, then the spill slots, then the caller's `rsp`.
  -- The frame is 64-byte aligned, so vector spills are aligned and `call` is allowed.
  let frame := gBytes + 64 * nSlots + 64
  let hasFrame := gBytes + nSlots > 0
  if hasFrame then
    pre := pre ++ #[.mov .rax (.reg .rsp), .and .rsp (.imm (-64)), .sub .rsp (.imm frame),
      .store (Mem.b .rsp (frame - 8)) .rax]
  for (_, r, w, op) in s.pins do
    match op with
    | .cvec bits =>
        let (l, p) := pool.vec bits
        pool := p
        pre := pre.push (.vmov w r (.mem (Mem.rip l)))
    | .bcast bits =>
        let (l, p) := pool.quad bits
        pool := p
        pre := pre.push (.vmov w r (.bcst (Mem.rip l)))
    | _ => throw s!"{s.name}: unsupported pinned value"
  let mut post : Array Instr := #[]
  if dirty then post := post.push .vzeroupper
  if hasFrame then post := post.push (.mov .rsp (.mem (Mem.b .rsp (frame - 8))))
  for r in s.saved.reverse do post := post.push (.pop r)
  post := post ++ #[.ret, .directive s!".size {s.name}, .-{s.name}"]
  return (⟨s.name, pre ++ body ++ post, checked, unchecked, blocks⟩, pool)

/-- An assembly file under construction. -/
structure AsmFile where
  fns : Array Fn := #[]
  pool : Pool := {}
  /-- raw text appended after the functions (tables) -/
  extra : Array String := #[]

/-- Add a function built by `body`. -/
def AsmFile.addFn (f : AsmFile) (name : String) (body : FnM Unit) (foldLimit : Nat := 2)
    (global : Bool := true) (sched : Nat := 1) (metric : Nat := 0) (foldAlso : List Nat := [])
    (constAlso : List Nat := []) : Except String AsmFile := do
  let ((), st) := body.run { name, foldLimit, sched, metric, foldAlso, constAlso }
  let (fn, pool) ← st.finish f.pool global
  return { f with fns := f.fns.push fn, pool }

/-- Add a function given directly as instructions (no vector blocks). -/
def AsmFile.addRaw (f : AsmFile) (name : String) (body : Array Instr) (global : Bool := true) :
    AsmFile :=
  let pre : Array Instr := #[.align 64] ++ (if global then #[.directive s!".globl {name}"] else #[]) ++
    #[.directive s!".type {name}, @function", .label name]
  { f with fns := f.fns.push { name, instrs := pre ++ body ++ #[.directive s!".size {name}, .-{name}"] } }

def AsmFile.print (f : AsmFile) : String := Id.run do
  let mut parts : Array String := #["# Generated by LeanFFTW.Asm (Lean). Do not edit.\n\t.intel_syntax noprefix\n\t.text\n"]
  for fn in f.fns do
    let mut s := ""
    for i in fn.instrs do
      s := s ++ i.print ++ "\n"
    parts := parts.push s
  for e in f.extra do parts := parts.push e
  parts := parts.push f.pool.print
  parts := parts.push "\t.section .note.GNU-stack,\"\",@progbits\n"
  return String.join parts.toList

end LeanFFTW.Asm
