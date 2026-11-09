/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Instr
import Std.Data.HashMap

/-!
# Straight-line vector code over virtual registers

A `VBlock` is the body of a loop before register allocation: every value has a number
(`VId`), defined once. Kernels (`LeanFFTW.Gen.Kernel`) and the data-movement steps around
them are written as blocks; `LeanFFTW/Asm/Alloc.lean` turns a block into instructions.

Constants live in a per-file pool (`Pool`) in `.rodata` and are used as memory operands.
-/

namespace LeanFFTW.Asm

open Std

/-- Sign bit of a double. -/
def signBit : UInt64 := 0x8000000000000000

/-- A virtual vector register. -/
abbrev VId := Nat

/-- Vector values. -/
inductive VOp where
  /-- unaligned full-width load -/
  | load (m : Mem)
  /-- masked load, inactive lanes zero -/
  | loadz (k : KReg) (m : Mem)
  /-- the double with these bits, in every lane -/
  | bcast (bits : UInt64)
  /-- one 64-bit constant per lane (doubles, or the indices of `permt2`) -/
  | cvec (bits : Array UInt64)
  | zero
  | bin (op : VBin) (a b : VId)
  /-- xor with per-lane constants (sign flips) -/
  | xorc (a : VId) (bits : Array UInt64)
  /-- `±(a·b) ± c` -/
  | fma (op : VFma) (a b c : VId)
  | shufpd (a b : VId) (imm : Nat)
  | shuff (a b : VId) (imm : Nat)
  /-- lane `i` is `(a ++ b)[idx[i]]` -/
  | permt2 (a idx b : VId)
  /-- `a − b` in even lanes, `a + b` in odd lanes -/
  | addsub (a b : VId)
  /-- `a + b` in even lanes, `a − b` in odd lanes -/
  | subadd (a b : VId)
  deriving Repr, Inhabited

def VOp.args : VOp → List VId
  | .bin _ a b | .shufpd a b _ | .shuff a b _ | .addsub a b | .subadd a b => [a, b]
  | .xorc a _ => [a]
  | .fma _ a b c | .permt2 a b c => [a, b, c]
  | _ => []

inductive VStmt where
  | df (id : VId) (op : VOp)
  | store (m : Mem) (v : VId)
  | storek (m : Mem) (k : KReg) (v : VId)
  deriving Repr, Inhabited

/-- Straight-line vector code of one width. -/
structure VBlock where
  w : W
  stmts : Array VStmt
  deriving Repr, Inhabited

/-! ## The constant pool -/

def hexDigits (n : Nat) (width : Nat) : String :=
  String.ofList ((Nat.toDigits 16 n).leftpad width '0')

structure Pool where
  quads : Array UInt64 := #[]
  qset : HashMap UInt64 Unit := {}
  vecs : Array (Array UInt64) := #[]
  vmap : HashMap (Array UInt64) Nat := {}
  deriving Inhabited

namespace Pool

/-- Label of a 64-bit constant. -/
def quad (p : Pool) (bits : UInt64) : String × Pool :=
  let l := ".LQ" ++ hexDigits bits.toNat 16
  if p.qset.contains bits then (l, p)
  else (l, { p with quads := p.quads.push bits, qset := p.qset.insert bits () })

/-- Label of a vector constant. -/
def vec (p : Pool) (bits : Array UInt64) : String × Pool :=
  match p.vmap[bits]? with
  | some i => (s!".LV{i}", p)
  | none =>
      let i := p.vecs.size
      (s!".LV{i}", { p with vecs := p.vecs.push bits, vmap := p.vmap.insert bits i })

/-- The `.rodata` section holding the pool. -/
def print (p : Pool) : String := Id.run do
  let mut s := "\t.section .rodata\n"
  for i in [0:p.vecs.size] do
    let v := p.vecs[i]!
    s := s ++ s!"\t.p2align {Nat.log2 (min 64 (8 * v.size))}\n.LV{i}:\n"
    for b in v do
      s := s ++ s!"\t.quad 0x{hexDigits b.toNat 16}\n"
  s := s ++ "\t.p2align 3\n"
  for b in p.quads do
    s := s ++ s!".LQ{hexDigits b.toNat 16}:\n\t.quad 0x{hexDigits b.toNat 16}\n"
  return s

end Pool

end LeanFFTW.Asm
