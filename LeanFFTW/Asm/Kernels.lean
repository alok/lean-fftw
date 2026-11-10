/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Slp
import LeanFFTW.Gen.Stockham

/-!
# The passes of the fast engine, in assembly

Each pass of a plan is a loop around one kernel (`LeanFFTW.Gen.butterflyK`, the CSE'd
straight-line code of a proved butterfly). This file writes those loops in the assembly DSL:
the integer part by hand, the vector part by instantiating the kernel over virtual
registers.

## Records

A plan is a tree of *records* in one block of memory (`LeanFFTW/Asm/Plan.lean`). Every
function here takes `rdi` = its record, `rsi = in`, `rdx = out`, `rcx = col`. Word 0 of a
record is the index of its function in `lfa_table`; the other words are the parameters listed
at each function (8 bytes each). Pointers inside a record are byte offsets from the record's
own address, so plan memory is position independent. `col` is the column (in vectors of 8
butterflies) at which a pass starts; `lfa_loop` records advance `in`, `out` and `col`.

## Lane order

A vector of blocked data holds 8 consecutive positions `8c + i` in the lane order
`σ = [0, 4, 1, 5, 2, 6, 3, 7]` (lane `p` holds position `8c + σ p`). With this order the
conversions from and to interleaved complex data are `vunpcklpd`/`vunpckhpd`, which need no
index vectors.
-/

namespace LeanFFTW.Asm

open LeanFFTW.Gen

/-- Instantiate a kernel on split data: every lane runs the kernel on its own butterfly.
Input slot `i` is the vector `bind i`; returns the vectors of the outputs. -/
def instSplit (k : Kernel) (bind : Nat → VId) : BlockM (Array VId) := do
  let mut env : Array VId := (Array.range k.nIn).map bind
  for op in k.ops do
    let v ← (match op with
      | .cst c => BlockM.df (.bcast c.toFloat.toBits)
      | .zero => BlockM.df .zero
      | .add a b => BlockM.df (.bin .add env[a]! env[b]!)
      | .sub a b => BlockM.df (.bin .sub env[a]! env[b]!)
      | .mul a b => BlockM.df (.bin .mul env[a]! env[b]!)
      | .neg a => BlockM.df (.xorc env[a]! #[signBit])
      | .fma a b c => BlockM.df (.fma .fmadd env[a]! env[b]! env[c]!)
      | .fms a b c => BlockM.df (.fma .fmsub env[a]! env[b]! env[c]!)
      | .fnma a b c => BlockM.df (.fma .fnmadd env[a]! env[b]! env[c]!))
    env := env.push v
  return k.outs.map (env[·]!)

/-! ## General-purpose registers of a function -/

/-- Registers handed out by `GprPool.take`, caller-saved first. `rdi`, `rsi`, `rdx`, `rcx`
hold the arguments and are added with `give` once they are no longer needed. -/
structure GprPool where
  free : List Gpr := [.rax, .r8, .r9, .r10, .r11, .rbx, .r12, .r13, .r14, .r15, .rbp]

abbrev KM := StateT GprPool FnM

namespace KM

def ins (i : Instr) : KM Unit := liftM (m := FnM) (FnM.ins i)

/-- A free register (saved in the prologue if callee-saved). -/
def take : KM Gpr := do
  let p ← get
  match p.free with
  | r :: rest =>
      set ({ free := rest } : GprPool)
      if r.calleeSaved then liftM (m := FnM) (FnM.save [r])
      return r
  | [] => return .rax  -- generation fails later on the clash; templates never get here

def give (rs : List Gpr) : KM Unit := modify fun p => { free := rs ++ p.free }

/-- An integer slot in the frame. -/
def gslot : KM Mem := liftM (m := FnM) FnM.gslot

/-- A register holding parameter `i` of the record. -/
def param (i : Nat) : KM Gpr := do
  let r ← take
  ins (.mov r (.mem (Mem.b .rdi (8 * i))))
  return r

def block {α : Type} (w : W) (body : BlockM α) (spec : Option Spec := none) : KM α :=
  liftM (m := FnM) (FnM.block w body spec)

def repeatDown (ctr : Gpr) (body : KM Unit) : KM Unit := do
  let l ← liftM (m := FnM) FnM.freshLabel
  ins (.align 16)
  ins (.label l)
  body
  ins (.dec ctr)
  ins (.jcc .ne l)

/-- As `repeatDown`, with the counter in memory. -/
def repeatDownMem (ctr : Mem) (body : KM Unit) : KM Unit := do
  let l ← liftM (m := FnM) FnM.freshLabel
  ins (.align 16)
  ins (.label l)
  body
  ins (.decMem ctr)
  ins (.jcc .ne l)

end KM

/-! ## Addressing the rows of a pass

A pass of radix `R` reads `R` rows `base + r·S` (`S` = the stride in bytes, a run-time
value). Row `r` is addressed as `B_{r/8} + (r mod 8)·S`, where the multiples `S, 3S, 5S, 7S`
are kept in registers (`m·S` with `m` even is an odd multiple scaled by 2 or 4) and
`B_i = base + 8i·S`. -/

structure Rows where
  bases : Array Gpr
  /-- registers holding `S, 3S, 5S, 7S` (as many as needed) -/
  mult : Array Gpr

/-- The address of row `r`, plus `disp` bytes. -/
def Rows.mem (rw : Rows) (r : Nat) (disp : Int := 0) : Mem :=
  let b := rw.bases[r / 8]!
  match r % 8 with
  | 0 => Mem.b b disp
  | 1 => Mem.bi b rw.mult[0]! 1 disp
  | 2 => Mem.bi b rw.mult[0]! 2 disp
  | 3 => Mem.bi b rw.mult[1]! 1 disp
  | 4 => Mem.bi b rw.mult[0]! 4 disp
  | 5 => Mem.bi b rw.mult[2]! 1 disp
  | 6 => Mem.bi b rw.mult[1]! 2 disp
  | _ => Mem.bi b rw.mult[3]! 1 disp

/-- Set up row addressing for `R` rows from the first base `b0` and the stride `s`. -/
def Rows.setup (R : Nat) (b0 s : Gpr) : KM Rows := do
  let mut mult := #[s]
  if R > 3 then
    let s3 ← KM.take
    KM.ins (.lea s3 (Mem.bi s s 2))
    mult := mult.push s3
    if R > 5 then
      let s5 ← KM.take
      KM.ins (.lea s5 (Mem.bi s s 4))
      mult := mult.push s5
      if R > 7 then
        let s7 ← KM.take
        KM.ins (.lea s7 (Mem.bi s3 s 4))
        mult := mult.push s7
  let mut bases := #[b0]
  for i in [1:(R + 7) / 8] do
    let b ← KM.take
    KM.ins (.lea b (Mem.bi bases[i - 1]! s 8))
    bases := bases.push b
  return ⟨bases, mult⟩

/-- Advance every base by `step`. -/
def Rows.advance (rw : Rows) (step : GSrc) : KM Unit :=
  for b in rw.bases do KM.ins (.add b step)

/-- Move every base back by `step`. -/
def Rows.retreat (rw : Rows) (step : GSrc) : KM Unit :=
  for b in rw.bases do KM.ins (.sub b step)

def dirTag (fwd : Bool) : String := if fwd then "f" else "b"

/-! ## The lane order σ and the data-movement steps -/

/-- Lane `p` of a vector of blocked data holds position `8c + σ p`. -/
def sigma : Array Nat := #[0, 4, 1, 5, 2, 6, 3, 7]

/-- Split two vectors of 4 interleaved complex numbers (`lo` = numbers 0–3, `hi` = 4–7) into
real and imaginary parts, lanes in the order σ. -/
def deinterleave (lo hi : VId) : BlockM (VId × VId) := do
  return (← BlockM.bin .unpcklo lo hi, ← BlockM.bin .unpckhi lo hi)

/-- The inverse of `deinterleave`: complex numbers 0–3, then 4–7. -/
def interleave (re im : VId) : BlockM (VId × VId) := do
  return (← BlockM.bin .unpcklo re im, ← BlockM.bin .unpckhi re im)

/-- Transpose 8 vectors: column `p` holds lane `p` of the rows, in the order σ
(`[a₀[p], a₄[p], a₁[p], a₅[p], a₂[p], a₆[p], a₃[p], a₇[p]]`). -/
def transposeS (a : Array VId) : BlockM (Array VId) := do
  let mut cols : Array VId := Array.replicate 8 0
  for par in [0, 1] do
    let mut h : Array VId := #[]
    for i in [0:4] do
      h := h.push (← BlockM.bin (if par == 0 then .unpcklo else .unpckhi) a[i]! a[i + 4]!)
    let e01 ← BlockM.df (.shuff h[0]! h[1]! 0x88)
    let o01 ← BlockM.df (.shuff h[0]! h[1]! 0xDD)
    let e23 ← BlockM.df (.shuff h[2]! h[3]! 0x88)
    let o23 ← BlockM.df (.shuff h[2]! h[3]! 0xDD)
    cols := cols.set! par (← BlockM.df (.shuff e01 e23 0x88))
    cols := cols.set! (par + 4) (← BlockM.df (.shuff e01 e23 0xDD))
    cols := cols.set! (par + 2) (← BlockM.df (.shuff o01 o23 0x88))
    cols := cols.set! (par + 6) (← BlockM.df (.shuff o01 o23 0xDD))
  return cols

/-! ## The in-place schedule

The data of the in-place schedule are in blocks of 8 complex numbers: 8 real parts, then
8 imaginary parts, each in lane order σ. The twiddles of a pass are stored in the order the
loop reads them: for each vector of 8 butterflies, `w_1.re, w_1.im, …, w_{R-1}.re,
w_{R-1}.im` (8 doubles each, lane order σ). -/

/-- Entries after the end of an offset table of `leafFn` that the prefetches may read. -/
def leafPad : Nat := 4

def leafName (R : Nat) (fwd : Bool) (pf : Nat := 0) : String :=
  s!"lfa_leaf_r{R}_{dirTag fwd}{if pf == 0 then "" else s!"_p{pf}"}"
def ditName (R : Nat) (fwd last : Bool) : String :=
  s!"lfa_dit{if last then "last" else ""}_r{R}_{dirTag fwd}"

/-- What the block of `leafFn` computes: lane `p` runs the kernel on the complex numbers `p`
of the rows (`lo` holds numbers 0–3 of a row, `hi` 4–7, interleaved; lane `p` is number
`σ p`), and output `8c + σ ℓ` of lane `p` is stored in lane `ℓ` of block `c` of leaf `p`. -/
def leafSpec (k : Kernel) (R : Nat) (row : Nat → Int → Mem) (lane : Nat → Int → Mem) : Spec :=
  SpecB.spec do
    let mut outs : Array (Array Nat) := #[]
    for p in [0:8] do
      let mut inp : Array Nat := #[]
      for r in [0:R] do
        let cell := row r (if p % 2 == 0 then 0 else 64)
        inp := inp.push (← SpecB.node (.inp cell (p - p % 2)))
        inp := inp.push (← SpecB.node (.inp cell (p - p % 2 + 1)))
      outs := outs.push (← SpecB.kernel k inp)
    let mut res : List (Mem × Array Nat) := []
    for part in [0:2] do
      for c in [0:R / 8] do
        for q in [0:8] do
          res := (lane sigma[q]! (128 * c + 64 * part),
            (Array.range 8).map fun l => outs[q]![2 * (8 * c + sigma[l]!) + part]!) :: res
    return res

/-- What the block of `ditFn` computes: lane `p` runs the kernel on lane `p` of the rows and
of the twiddles. `last`: the results are stored interleaved. -/
def ditSpec (k : Kernel) (R : Nat) (last : Bool) (row : Nat → Int → Mem) (tw : Int → Mem) : Spec :=
  SpecB.spec do
    let mut outs : Array (Array Nat) := #[]
    for p in [0:8] do
      let mut inp : Array Nat := #[]
      for r in [0:R] do
        inp := inp.push (← SpecB.node (.inp (row r 0) p))
        inp := inp.push (← SpecB.node (.inp (row r 64) p))
      for r in [1:R] do
        inp := inp.push (← SpecB.node (.inp (tw (128 * (r - 1))) p))
        inp := inp.push (← SpecB.node (.inp (tw (128 * (r - 1) + 64)) p))
      outs := outs.push (← SpecB.kernel k inp)
    let mut res : List (Mem × Array Nat) := []
    for r in [0:R] do
      let re (l : Nat) : Nat := outs[l]![2 * r]!
      let im (l : Nat) : Nat := outs[l]![2 * r + 1]!
      if last then
        res := (row r 0, (Array.range 8).map fun l => if l % 2 == 0 then re l else im (l - 1)) :: res
        res := (row r 64, (Array.range 8).map fun l => if l % 2 == 0 then re (l + 1) else im l) :: res
      else
        res := (row r 0, (Array.range 8).map re) :: res
        res := (row r 64, (Array.range 8).map im) :: res
    return res

/-- First pass of the in-place schedule: interleaved `in` → blocked `out`, 8 leaves per
iteration (`8 ∣ R`). Leaf `l = 4h + m` of an iteration (`h < 2`, `m < 4`) is written at
`out + tab[i] + h·Δ + X_m` (`X_0 = 0`); offsets of this form cover the digit-reversed order
of every sequence of power-of-two radices.

Parameters: `1`: `S` = bytes between the `R` inputs of a leaf; `2`: number of iterations;
`3`: bytes `in` advances per iteration; `4`: table of the byte offsets in `out` of the first
leaf of each iteration; `5`: `Δ`; `6`–`8`: `X_1`, `X_2`, `X_3`.

`pf` adds software prefetches (they change no value): bit 0, the 128 bytes after each input
vector (what the next call reads when the calls advance `in` by 128; into the second-level
cache); `pf / 2 = d ≥ 1`: the output of the iteration `d` iterations ahead (for writing; the
table of parameter 4 has `leafPad` more entries). -/
def leafFn (R : Nat) (fwd : Bool) (pf : Nat := 0) : KM Unit := do
  let k := butterflyK fwd R false
  let sOut ← KM.gslot
  let sStep ← KM.gslot
  let sCnt ← KM.gslot
  let sDelta ← KM.gslot
  KM.ins (.store sOut .rdx)
  let s ← KM.param 1
  for (i, slot) in [(2, sCnt), (3, sStep), (5, sDelta)] do
    KM.ins (.mov .rdx (.mem (Mem.b .rdi (8 * i))))
    KM.ins (.store slot .rdx)
  let gt ← KM.param 4
  KM.ins (.add gt (.reg .rdi))
  let x1 ← KM.param 6
  let x2 ← KM.param 7
  let x3 ← KM.param 8
  KM.give [.rdi, .rdx, .rcx]
  let rin ← Rows.setup R .rsi s
  let ob ← KM.take
  let ob2 ← KM.take
  let lane (l : Nat) (disp : Int) : Mem :=
    let b := if l / 4 == 0 then ob else ob2
    match l % 4 with
    | 0 => Mem.b b disp
    | 1 => Mem.bi b x1 1 disp
    | 2 => Mem.bi b x2 1 disp
    | _ => Mem.bi b x3 1 disp
  KM.repeatDownMem sCnt do
    if pf / 2 ≥ 1 then
      KM.ins (.mov ob (.mem (Mem.b gt (8 * (pf / 2)))))
      KM.ins (.add ob (.mem sOut))
      KM.ins (.mov ob2 (.reg ob))
      KM.ins (.add ob2 (.mem sDelta))
      for l in [0:8] do
        for line in [0:R / 4] do
          KM.ins (.prefetch 3 (lane l (64 * line)))
    KM.ins (.mov ob (.mem (Mem.b gt)))
    KM.ins (.add ob (.mem sOut))
    KM.ins (.mov ob2 (.reg ob))
    KM.ins (.add ob2 (.mem sDelta))
    KM.ins (.add gt (.imm 8))
    if pf % 2 == 1 then
      for r in [0:R] do
        KM.ins (.prefetch 1 (rin.mem r 128))
        KM.ins (.prefetch 1 (rin.mem r 192))
    KM.block .z (spec := some (leafSpec k R (fun r d => rin.mem r d) lane)) do
      let mut inp : Array VId := #[]
      for r in [0:R] do
        let lo ← BlockM.load (rin.mem r 0)
        let hi ← BlockM.load (rin.mem r 64)
        let (re, im) ← deinterleave lo hi
        inp := (inp.push re).push im
      let outs ← instSplit k (inp[·]!)
      for part in [0:2] do
        for c in [0:R / 8] do
          let cols ← transposeS ((Array.range 8).map fun i => outs[2 * (8 * c + i) + part]!)
          for p in [0:8] do
            BlockM.store (lane sigma[p]! (128 * c + 64 * part)) cols[p]!
    rin.advance (.mem sStep)

/-- A twiddled pass of the in-place schedule; `last`: the outputs are written as interleaved
complex numbers (the last pass).

Parameters: `1`: byte offset in `out` of the first butterfly; `2`: twiddles of column 0;
`3`: `S = 16·ns`; `4`: number of blocks; `5`: number of vectors of 8 butterflies per block;
`6`: bytes from the end of one block's range to the start of the next. The pass starts at
column `8·col` of each block. -/
def ditFn (R : Nat) (fwd last : Bool) : KM Unit := do
  let k := butterflyK fwd R true
  let p0 ← KM.param 1
  KM.ins (.add p0 (.reg .rdx))
  let tw0 ← KM.param 2
  KM.ins (.add tw0 (.reg .rdi))
  KM.ins (.imul .rdx .rcx (128 * (R - 1)))
  KM.ins (.add tw0 (.reg .rdx))
  KM.ins (.shl .rcx 7)
  KM.ins (.add p0 (.reg .rcx))
  let s ← KM.param 3
  let nb ← KM.param 4
  let nq ← KM.param 5
  let bstep ← KM.param 6
  KM.give [.rdi, .rsi, .rdx, .rcx]
  let rw ← Rows.setup R p0 s
  let t ← KM.take
  let q ← KM.take
  KM.repeatDown nb do
    KM.ins (.mov t (.reg tw0))
    KM.ins (.mov q (.reg nq))
    KM.repeatDown q do
      KM.block .z (spec := some (ditSpec k R last (fun r d => rw.mem r d) (fun d => Mem.b t d))) do
        let mut inp : Array VId := #[]
        for r in [0:R] do
          inp := inp.push (← BlockM.load (rw.mem r 0))
          inp := inp.push (← BlockM.load (rw.mem r 64))
        for r in [1:R] do
          inp := inp.push (← BlockM.load (Mem.b t (128 * (r - 1))))
          inp := inp.push (← BlockM.load (Mem.b t (128 * (r - 1) + 64)))
        let outs ← instSplit k (inp[·]!)
        for r in [0:R] do
          let (a, b) ← (if last then interleave outs[2 * r]! outs[2 * r + 1]!
                        else pure (outs[2 * r]!, outs[2 * r + 1]!))
          BlockM.store (rw.mem r 0) a
          BlockM.store (rw.mem r 64) b
      rw.advance (.imm 128)
      KM.ins (.add t (.imm (128 * (R - 1))))
    rw.advance (.reg bstep)

/-! ## Stockham passes on interleaved data

Sizes that are not powers of two use the Stockham schedule (`LeanFFTW.Gen.stockhamWith`):
pass `t` of radix `R` reads the complex numbers `b + k + r·N/R` and writes `b·R + k + r·ns`
(`k < ns`, `b` a multiple of `ns`). Data are interleaved complex numbers in every pass, so
any stride is allowed; a vector of 8 butterflies loads 8 numbers of each row, splits them
into real and imaginary parts (lane order σ), and joins the results again. The butterflies
beyond the last multiple of 8 run as one iteration with masked loads and stores. -/

def stkName (R : Nat) (fwd : Bool) : String := s!"lfa_stk_r{R}_{dirTag fwd}"
def stk0Name (R : Nat) (fwd : Bool) : String := s!"lfa_stk0_r{R}_{dirTag fwd}"

/-- What a full block of a Stockham pass computes: lane `p` runs the kernel on the complex
number `σ p` of every row (and lane `p` of the twiddles), and the results are stored
interleaved. -/
def stkSpec (k : Kernel) (R : Nat) (rin rout : Nat → Int → Mem) (tw : Option (Int → Mem)) : Spec :=
  SpecB.spec do
    let mut outs : Array (Array Nat) := #[]
    for p in [0:8] do
      let mut inp : Array Nat := #[]
      for r in [0:R] do
        let cell := rin r (if p % 2 == 0 then 0 else 64)
        inp := inp.push (← SpecB.node (.inp cell (p - p % 2)))
        inp := inp.push (← SpecB.node (.inp cell (p - p % 2 + 1)))
      if let some t := tw then
        for r in [1:R] do
          inp := inp.push (← SpecB.node (.inp (t (128 * (r - 1))) p))
          inp := inp.push (← SpecB.node (.inp (t (128 * (r - 1) + 64)) p))
      outs := outs.push (← SpecB.kernel k inp)
    let mut res : List (Mem × Array Nat) := []
    for r in [0:R] do
      let re (l : Nat) : Nat := outs[l]![2 * r]!
      let im (l : Nat) : Nat := outs[l]![2 * r + 1]!
      res := (rout r 0, (Array.range 8).map fun l => if l % 2 == 0 then re l else im (l - 1)) :: res
      res := (rout r 64, (Array.range 8).map fun l => if l % 2 == 0 then re (l + 1) else im l) :: res
    return res

/-- The block of a Stockham pass. `lmask`, `smask`: masks of the two vectors of a row, for
the loads and for the stores. -/
def stkBlock (k : Kernel) (R : Nat) (rin rout : Nat → Int → Mem) (tw : Option (Int → Mem))
    (lmask smask : Option (KReg × KReg)) : BlockM Unit := do
  let ld (kr : Option KReg) (m : Mem) : BlockM VId :=
    match kr with
    | some kr => BlockM.df (.loadz kr m)
    | none => BlockM.load m
  let mut inp : Array VId := #[]
  for r in [0:R] do
    let lo ← ld (lmask.map (·.1)) (rin r 0)
    let hi ← ld (lmask.map (·.2)) (rin r 64)
    let (re, im) ← deinterleave lo hi
    inp := (inp.push re).push im
  if let some t := tw then
    for r in [1:R] do
      inp := inp.push (← BlockM.load (t (128 * (r - 1))))
      inp := inp.push (← BlockM.load (t (128 * (r - 1) + 64)))
  let outs ← instSplit k (inp[·]!)
  for r in [0:R] do
    let (a, b) ← interleave outs[2 * r]! outs[2 * r + 1]!
    match smask with
    | some (k0, k1) =>
        BlockM.storek (rout r 0) k0 a
        BlockM.storek (rout r 64) k1 b
    | none =>
        BlockM.store (rout r 0) a
        BlockM.store (rout r 64) b

namespace KM

def freshLabel : KM String := liftM (m := FnM) FnM.freshLabel

/-- Parameter `i` as an address: `dflt` when the word is 0, else the record plus the word. -/
def selParam (i : Nat) (dflt : Gpr) : KM Gpr := do
  let r ← param i
  ins (.test r r)
  ins (.lea r (Mem.bi .rdi r 1))
  ins (.cmov .e r dflt)
  return r

/-- Copy parameter `i` to a slot of the frame (through `rax`). -/
def slotParam (i : Nat) : KM Mem := do
  let m ← gslot
  ins (.mov .rax (.mem (Mem.b .rdi (8 * i))))
  ins (.store m .rax)
  return m

/-- The masks `k1`, `k2` of the two vectors of a row in the tail iteration, from the
parameters `i`, `i + 1`. -/
def tailMasks (i : Nat) : KM (KReg × KReg) := do
  ins (.mov .rax (.mem (Mem.b .rdi (8 * i))))
  ins (.kmov ⟨1⟩ .rax)
  ins (.mov .rax (.mem (Mem.b .rdi (8 * (i + 1)))))
  ins (.kmov ⟨2⟩ .rax)
  return (⟨1⟩, ⟨2⟩)

end KM

/-- A twiddled Stockham pass on interleaved data.

Parameters: `1`: the source (0: `in`; else its byte offset from the record); `2`: the
destination (0: `out`); `3`: twiddles, in the order the loop reads them (for each vector of
8 columns, `w_1.re, w_1.im, …`, lane order σ); `4`: `16·N/R`; `5`: `16·ns`; `6`: number of
blocks `N/(R·ns)`; `7`: `⌊ns/8⌋`; `8`: `16·(ns mod 8)`; `9`: `16·ns·(R−1)`; `10`, `11`:
masks of the two vectors of a row in the tail iteration. -/
def stkFn (R : Nat) (fwd : Bool) : KM Unit := do
  let k := butterflyK fwd R true
  let masks ← KM.tailMasks 10
  let sNb ← KM.slotParam 6
  let sFull ← KM.slotParam 7
  let sTail ← KM.slotParam 8
  let sSkip ← KM.slotParam 9
  let sTw ← KM.gslot
  KM.ins (.mov .rax (.mem (Mem.b .rdi 24)))
  KM.ins (.add .rax (.reg .rdi))
  KM.ins (.store sTw .rax)
  let x ← KM.selParam 1 .rsi
  let o ← KM.selParam 2 .rdx
  let sIn ← KM.param 4
  let sOut ← KM.param 5
  KM.give [.rdi, .rsi, .rdx, .rcx]
  let rin ← Rows.setup R x sIn
  let rout ← Rows.setup R o sOut
  let t ← KM.take
  let q ← KM.take
  let rowIn := fun (r : Nat) (d : Int) => rin.mem r d
  let rowOut := fun (r : Nat) (d : Int) => rout.mem r d
  let tw := fun (d : Int) => Mem.b t d
  KM.repeatDownMem sNb do
    let lTail ← KM.freshLabel
    let lEnd ← KM.freshLabel
    KM.ins (.mov t (.mem sTw))
    KM.ins (.mov q (.mem sFull))
    KM.ins (.test q q)
    KM.ins (.jcc .e lTail)
    KM.repeatDown q do
      KM.block .z (spec := some (stkSpec k R rowIn rowOut (some tw)))
        (stkBlock k R rowIn rowOut (some tw) none none)
      rin.advance (.imm 128)
      rout.advance (.imm 128)
      KM.ins (.add t (.imm (128 * (R - 1))))
    KM.ins (.label lTail)
    KM.ins (.mov q (.mem sTail))
    KM.ins (.test q q)
    KM.ins (.jcc .e lEnd)
    KM.block .z (stkBlock k R rowIn rowOut (some tw) (some masks) (some masks))
    rin.advance (.reg q)
    rout.advance (.reg q)
    KM.ins (.label lEnd)
    rout.advance (.mem sSkip)

/-- The first Stockham pass (`ns = 1`, no twiddles): butterfly `j` reads the numbers
`j + r·N/R` and writes `j·R + r`. A vector of 8 butterflies stores its results (interleaved)
in a buffer of the frame, from which the `R` numbers of each butterfly are copied to their
place.

Parameters: `1`: the source (0: `in`); `2`: the destination (0: `out`); `3`: `16·N/R`;
`4`: `⌊(N/R)/8⌋`; `5`: `(N/R) mod 8`; `6`, `7`: masks of the tail iteration. -/
def stk0Fn (R : Nat) (fwd : Bool) : KM Unit := do
  let k := butterflyK fwd R false
  let sIter ← KM.slotParam 4
  let sTl ← KM.slotParam 5
  -- the buffer: `2R` vectors on a 64-byte boundary, after 8 integer slots
  for _ in [0:6] do let _ ← KM.gslot
  let tb0 ← KM.gslot
  for _ in [1:16 * R] do let _ ← KM.gslot
  let masks ← KM.tailMasks 6
  let x ← KM.selParam 1 .rsi
  let o ← KM.selParam 2 .rdx
  let sIn ← KM.param 3
  KM.give [.rdi, .rsi, .rdx, .rcx]
  let rin ← Rows.setup R x sIn
  let tb ← KM.take
  KM.ins (.lea tb tb0)
  let q ← KM.take
  let rowIn := fun (r : Nat) (d : Int) => rin.mem r d
  let rowOut := fun (r : Nat) (d : Int) => Mem.b tb (128 * r + d)
  -- butterfly `m` of the vector: its `R` numbers, 16 bytes each
  let copy (m : Nat) : KM Unit :=
    for r in [0:R] do
      KM.ins (.vmov .x ⟨0⟩ (.mem (Mem.b tb (128 * r + 16 * m))))
      KM.ins (.vstore .x (Mem.b o (16 * (m * R + r))) ⟨0⟩)
  let lTail ← KM.freshLabel
  let lEnd ← KM.freshLabel
  KM.ins (.mov q (.mem sIter))
  KM.ins (.test q q)
  KM.ins (.jcc .e lTail)
  KM.repeatDown q do
    KM.block .z (spec := some (stkSpec k R rowIn rowOut none)) (stkBlock k R rowIn rowOut none none none)
    for m in [0:8] do copy m
    rin.advance (.imm 128)
    KM.ins (.add o (.imm (128 * R)))
  KM.ins (.label lTail)
  KM.ins (.mov q (.mem sTl))
  KM.ins (.test q q)
  KM.ins (.jcc .e lEnd)
  KM.block .z (stkBlock k R rowIn rowOut none (some masks) none)
  for m in [0:8] do
    if m > 0 then
      KM.ins (.cmp q (.imm m))
      KM.ins (.jcc .be lEnd)
    copy m
  KM.ins (.label lEnd)

/-! ## The blocked Stockham schedule

The Stockham schedule on blocked data (blocks of 8 real parts and 8 imaginary parts, lane
order σ), so that only the first pass splits complex numbers and only the last joins them.

A pass on blocked data needs its runs of `ns` columns to be whole vectors. The first pass of
radix `R₀` therefore writes each butterfly's `R₀` outputs in `R₀' = 8⌈R₀/8⌉` slots (*padded*):
number `i = q·R₀ + k` (`k < R₀`) of an array is in slot `q·R₀' + k`. Every later `ns` is a
multiple of `R₀`, hence a whole number of vectors in slots. The slots `k ≥ R₀` (the pads)
hold copies of other outputs after the first pass and are transformed like data (their
twiddles are zero); the last pass, which writes ordinary interleaved numbers, stores what
they became where a later vector of the same row overwrites it, and its very last vector
goes through a buffer. No instruction is masked.

The first pass takes 8 consecutive butterflies per iteration; when their number is not a
multiple of 8, a last iteration recomputes the last 8. -/

/-- Slots of a run of `R` numbers. -/
def padUp (R : Nat) : Nat := (R + 7) / 8 * 8

def bstk0Name (R : Nat) (fwd : Bool) : String := s!"lfa_bstk0_r{R}_{dirTag fwd}"
def bstkName (R : Nat) (fwd last : Bool) : String :=
  s!"lfa_bstk{if last then "last" else ""}_r{R}_{dirTag fwd}"

/-- What the block of `bstk0Fn` computes: lane `p` runs the kernel on the complex numbers
`σ p` of the rows, and slot `8c + σ ℓ` of its outputs (output `(8c + σ ℓ) mod R`) is stored
in lane `ℓ` of block `c` of butterfly `σ p`. -/
def bstk0Spec (k : Kernel) (R : Nat) (row : Nat → Int → Mem) (lane : Nat → Int → Mem) : Spec :=
  SpecB.spec do
    let mut outs : Array (Array Nat) := #[]
    for p in [0:8] do
      let mut inp : Array Nat := #[]
      for r in [0:R] do
        let cell := row r (if p % 2 == 0 then 0 else 64)
        inp := inp.push (← SpecB.node (.inp cell (p - p % 2)))
        inp := inp.push (← SpecB.node (.inp cell (p - p % 2 + 1)))
      outs := outs.push (← SpecB.kernel k inp)
    let mut res : List (Mem × Array Nat) := []
    for part in [0:2] do
      for c in [0:padUp R / 8] do
        for q in [0:8] do
          res := (lane sigma[q]! (128 * c + 64 * part),
            (Array.range 8).map fun l => outs[q]![2 * ((8 * c + sigma[l]!) % R) + part]!) :: res
    return res

/-- What a block of a twiddled pass on blocked data computes: lane `p` runs the kernel on
lane `p` of the rows of the source and of the twiddles. `last`: the results are stored
interleaved. -/
def bstkSpec (k : Kernel) (R : Nat) (last : Bool) (rin rout : Nat → Int → Mem) (tw : Int → Mem) :
    Spec :=
  SpecB.spec do
    let mut outs : Array (Array Nat) := #[]
    for p in [0:8] do
      let mut inp : Array Nat := #[]
      for r in [0:R] do
        inp := inp.push (← SpecB.node (.inp (rin r 0) p))
        inp := inp.push (← SpecB.node (.inp (rin r 64) p))
      for r in [1:R] do
        inp := inp.push (← SpecB.node (.inp (tw (128 * (r - 1))) p))
        inp := inp.push (← SpecB.node (.inp (tw (128 * (r - 1) + 64)) p))
      outs := outs.push (← SpecB.kernel k inp)
    let mut res : List (Mem × Array Nat) := []
    for r in [0:R] do
      let re (l : Nat) : Nat := outs[l]![2 * r]!
      let im (l : Nat) : Nat := outs[l]![2 * r + 1]!
      if last then
        res := (rout r 0, (Array.range 8).map fun l => if l % 2 == 0 then re l else im (l - 1)) :: res
        res := (rout r 64, (Array.range 8).map fun l => if l % 2 == 0 then re (l + 1) else im l) :: res
      else
        res := (rout r 0, (Array.range 8).map re) :: res
        res := (rout r 64, (Array.range 8).map im) :: res
    return res

/-- The block of a twiddled pass on blocked data. -/
def bstkBlock (k : Kernel) (R : Nat) (last : Bool) (rin rout : Nat → Int → Mem) (tw : Int → Mem) :
    BlockM Unit := do
  let mut inp : Array VId := #[]
  for r in [0:R] do
    inp := inp.push (← BlockM.load (rin r 0))
    inp := inp.push (← BlockM.load (rin r 64))
  for r in [1:R] do
    inp := inp.push (← BlockM.load (tw (128 * (r - 1))))
    inp := inp.push (← BlockM.load (tw (128 * (r - 1) + 64)))
  let outs ← instSplit k (inp[·]!)
  for r in [0:R] do
    let (a, b) ← (if last then interleave outs[2 * r]! outs[2 * r + 1]!
                  else pure (outs[2 * r]!, outs[2 * r + 1]!))
    BlockM.store (rout r 0) a
    BlockM.store (rout r 64) b

/-- The first pass of the blocked Stockham schedule: interleaved `in` → padded blocked work
array. Butterfly `j` reads the numbers `j + r·N/R` and writes the slots `j·R' …`.

Parameters: `1`: the destination (byte offset from the record); `2`: `S = 16·N/R`;
`3`: `⌊(N/R)/8⌋ ≥ 1` iterations; `4`: 1 when `N/R` is not a multiple of 8 (a last iteration
recomputes the last 8 butterflies), else 0; `5`, `6`: the bytes that iteration moves back
in the source and in the destination. (Parameters are never negative: a record is stored
in a `FloatArray`, and a negative word has the bits of a NaN.) -/
def bstk0Fn (R : Nat) (fwd : Bool) : KM Unit := do
  let k := butterflyK fwd R false
  let RP := padUp R
  let sTail ← KM.slotParam 4
  let sBackIn ← KM.slotParam 5
  let sBackOut ← KM.slotParam 6
  let o ← KM.param 1
  KM.ins (.add o (.reg .rdi))
  let s ← KM.param 2
  let q ← KM.param 3
  KM.give [.rdi, .rdx, .rcx]
  let rin ← Rows.setup R .rsi s
  let row := fun (r : Nat) (d : Int) => rin.mem r d
  let lane := fun (m : Nat) (d : Int) => Mem.b o (16 * RP * m + d)
  let lLoop ← KM.freshLabel
  let lEnd ← KM.freshLabel
  KM.ins (.align 16)
  KM.ins (.label lLoop)
  KM.block .z (spec := some (bstk0Spec k R row lane)) do
    let mut inp : Array VId := #[]
    for r in [0:R] do
      let lo ← BlockM.load (row r 0)
      let hi ← BlockM.load (row r 64)
      let (re, im) ← deinterleave lo hi
      inp := (inp.push re).push im
    let outs ← instSplit k (inp[·]!)
    for part in [0:2] do
      for c in [0:RP / 8] do
        let cols ← transposeS ((Array.range 8).map fun i => outs[2 * ((8 * c + i) % R) + part]!)
        for p in [0:8] do
          BlockM.store (lane sigma[p]! (128 * c + 64 * part)) cols[p]!
  rin.advance (.imm 128)
  KM.ins (.add o (.imm (128 * RP)))
  KM.ins (.dec q)
  KM.ins (.jcc .ne lLoop)
  -- the last butterflies, once
  KM.ins (.decMem sTail)
  KM.ins (.jcc .ne lEnd)
  rin.retreat (.mem sBackIn)
  KM.ins (.sub o (.mem sBackOut))
  KM.ins (.mov q (.imm 1))
  KM.ins (.jmp lLoop)
  KM.ins (.label lEnd)

/-- A twiddled pass of the blocked Stockham schedule between two padded blocked arrays:
block `b` reads the slots `b + k + r·(N/R)'` and writes `b·R + k + r·ns'` (`k < ns'`).

Parameters: `1`, `2`: the source and the destination (byte offsets from the record);
`3`: twiddles, in the order the loop reads them; `4`: `16·(N/R)'`; `5`: `16·ns'`;
`6`: number of blocks `N/(R·ns)`; `7`: `ns'/8`; `8`: `16·ns'·(R−1)`. -/
def bstkFn (R : Nat) (fwd : Bool) : KM Unit := do
  let k := butterflyK fwd R true
  let sNb ← KM.slotParam 6
  let sNv ← KM.slotParam 7
  let sSkip ← KM.slotParam 8
  let sTw ← KM.gslot
  KM.ins (.mov .rax (.mem (Mem.b .rdi 24)))
  KM.ins (.add .rax (.reg .rdi))
  KM.ins (.store sTw .rax)
  let x ← KM.param 1
  KM.ins (.add x (.reg .rdi))
  let o ← KM.param 2
  KM.ins (.add o (.reg .rdi))
  let sIn ← KM.param 4
  let sOut ← KM.param 5
  KM.give [.rdi, .rsi, .rdx, .rcx]
  let rin ← Rows.setup R x sIn
  let rout ← Rows.setup R o sOut
  let t ← KM.take
  let q ← KM.take
  let rowIn := fun (r : Nat) (d : Int) => rin.mem r d
  let rowOut := fun (r : Nat) (d : Int) => rout.mem r d
  let tw := fun (d : Int) => Mem.b t d
  KM.repeatDownMem sNb do
    KM.ins (.mov t (.mem sTw))
    KM.ins (.mov q (.mem sNv))
    KM.repeatDown q do
      KM.block .z (spec := some (bstkSpec k R false rowIn rowOut tw))
        (bstkBlock k R false rowIn rowOut tw)
      rin.advance (.imm 128)
      rout.advance (.imm 128)
      KM.ins (.add t (.imm (128 * (R - 1))))
    rout.advance (.mem sSkip)

/-- The last pass of the blocked Stockham schedule: padded blocked source → interleaved
`out`. The row of `ns` numbers is `ns/R₀` runs of `U = R₀'/8` vectors; a vector that ends a
run holds `R₀ − 8(U−1)` numbers and pads. It is stored whole (the next run of the row then
overwrites what the pads left), except the last vector of the rows, which is stored in the
frame and copied number by number.

Parameters: `1`: the source (byte offset from the record); `2`: twiddles; `3`: `16·ns'`
(bytes between the rows of the source); `4`: `16·ns`; `5`: runs per row; `6`: `U`;
`7`: vectors of the last run stored whole (`U − 1` with pads, else `U`); `8`: `16·(R₀'−R₀)`;
`9`: numbers of the last vector (0 without pads: there is none). -/
def bstkLastFn (R : Nat) (fwd : Bool) : KM Unit := do
  let k := butterflyK fwd R true
  let sQ ← KM.slotParam 5
  let sU ← KM.slotParam 6
  let sU1 ← KM.slotParam 7
  let sPad ← KM.slotParam 8
  let sC ← KM.slotParam 9
  -- the buffer: `2R` vectors on a 64-byte boundary, after 8 integer slots
  for _ in [0:3] do let _ ← KM.gslot
  let tb0 ← KM.gslot
  for _ in [1:16 * R] do let _ ← KM.gslot
  let x ← KM.param 1
  KM.ins (.add x (.reg .rdi))
  let t ← KM.param 2
  KM.ins (.add t (.reg .rdi))
  let sIn ← KM.param 3
  let sOut ← KM.param 4
  KM.give [.rdi, .rsi, .rcx]
  let rin ← Rows.setup R x sIn
  let rout ← Rows.setup R .rdx sOut
  let cv ← KM.take
  let tb ← KM.take
  KM.ins (.lea tb tb0)
  let rowIn := fun (r : Nat) (d : Int) => rin.mem r d
  let rowOut := fun (r : Nat) (d : Int) => rout.mem r d
  let rowBuf := fun (r : Nat) (d : Int) => Mem.b tb (128 * r + d)
  let tw := fun (d : Int) => Mem.b t d
  let lRun ← KM.freshLabel
  let lGo ← KM.freshLabel
  let lFinal ← KM.freshLabel
  let lEnd ← KM.freshLabel
  KM.ins (.label lRun)
  KM.ins (.mov cv (.mem sU))
  KM.ins (.decMem sQ)
  KM.ins (.jcc .ne lGo)
  -- the last run
  KM.ins (.mov cv (.mem sU1))
  KM.ins (.test cv cv)
  KM.ins (.jcc .e lFinal)
  KM.ins (.label lGo)
  KM.repeatDown cv do
    KM.block .z (spec := some (bstkSpec k R true rowIn rowOut tw)) (bstkBlock k R true rowIn rowOut tw)
    rin.advance (.imm 128)
    rout.advance (.imm 128)
    KM.ins (.add t (.imm (128 * (R - 1))))
  KM.ins (.mov cv (.mem sQ))
  KM.ins (.test cv cv)
  KM.ins (.jcc .e lFinal)
  rout.retreat (.mem sPad)
  KM.ins (.jmp lRun)
  KM.ins (.label lFinal)
  KM.ins (.mov cv (.mem sC))
  KM.ins (.test cv cv)
  KM.ins (.jcc .e lEnd)
  KM.block .z (spec := some (bstkSpec k R true rowIn rowBuf tw)) (bstkBlock k R true rowIn rowBuf tw)
  for m in [0:8] do
    if m > 0 then
      KM.ins (.cmp cv (.imm m))
      KM.ins (.jcc .be lEnd)
    for r in [0:R] do
      KM.ins (.vmov .x ⟨0⟩ (.mem (Mem.b tb (128 * r + 16 * m))))
      KM.ins (.vstore .x (rout.mem r (16 * m)) ⟨0⟩)
  KM.ins (.label lEnd)

/-! ## Small transforms on interleaved data

Whole transforms in registers, on vectors of `VLc` complex numbers (`VLc = 1`: `xmm`,
2: `ymm`, 4: `zmm`). These functions have no parameters: the record is only the index. -/

def widthOf (vlc : Nat) : W := if vlc == 4 then .z else if vlc == 2 then .y else .x

def csmallName (N : Nat) (fwd : Bool) : String := s!"lfa_csmall_n{N}_{dirTag fwd}"
def cfusedName (R1 R2 vlc : Nat) (fwd : Bool) : String := s!"lfa_cfused_{R1}x{R2}_c{vlc}_{dirTag fwd}"
def ctwoName (R1 R2 vlc : Nat) (fwd : Bool) : String := s!"lfa_ctwo_{R1}x{R2}_c{vlc}_{dirTag fwd}"

/-- A whole transform of size `N`: one untwiddled butterfly, one complex number per `xmm`.
All loads precede all stores, so `in == out` is allowed. -/
def csmallFn (N : Nat) (fwd : Bool) : KM Unit := do
  let k := butterflyK fwd N false
  let spec : Spec := SpecB.spec do
    let mut inp : Array Nat := #[]
    for r in [0:N] do
      inp := inp.push (← SpecB.node (.inp (Mem.b .rsi (16 * r)) 0))
      inp := inp.push (← SpecB.node (.inp (Mem.b .rsi (16 * r)) 1))
    let o ← SpecB.kernel k inp
    return (List.range N).map fun (r : Nat) => (Mem.b .rdx (16 * r), #[o[2 * r]!, o[2 * r + 1]!])
  KM.block .x (spec := some spec) do
    let mut x : Array VId := #[]
    for r in [0:N] do x := x.push (← BlockM.load (Mem.b .rsi (16 * r)))
    let outs ← instC k 1 (x[·]!)
    for r in [0:N] do BlockM.store (Mem.b .rdx (16 * r)) outs[r]!

/-- Transpose a `VLc × VLc` block of complex numbers (rows are vectors). -/
def ctranspose (vlc : Nat) (rows : Array VId) : BlockM (Array VId) := do
  if vlc == 1 then return rows
  if vlc == 2 then
    return #[← BlockM.df (.shuff rows[0]! rows[1]! 0), ← BlockM.df (.shuff rows[0]! rows[1]! 3)]
  let a0 ← BlockM.df (.shuff rows[0]! rows[1]! 0x44)
  let a1 ← BlockM.df (.shuff rows[0]! rows[1]! 0xEE)
  let a2 ← BlockM.df (.shuff rows[2]! rows[3]! 0x44)
  let a3 ← BlockM.df (.shuff rows[2]! rows[3]! 0xEE)
  return #[← BlockM.df (.shuff a0 a2 0x88), ← BlockM.df (.shuff a0 a2 0xDD),
           ← BlockM.df (.shuff a1 a3 0x88), ← BlockM.df (.shuff a1 a3 0xDD)]

/-- The whole transform of size `N = R1·R2` (plan `[R1, R2]`) on vectors of `VLc` complex
numbers, with the twiddles of the second pass as constants (the values of
`passTwiddles (cosSin2PiTable N) fwd N R2 R1`). Requires `VLc ∣ R1` and `R2 ≥ VLc`: the
first pass takes `VLc` consecutive butterflies at a time, and when `R2` is not a multiple of
`VLc` its last group is the last `VLc` butterflies (some are computed twice).

`mem = false`: everything stays in registers; all loads precede all stores, so `in == out`
is allowed. `mem = true`: the results of the first pass are stored in a work array and read
back: `out` itself, or the buffer of the record (parameter `1`, when not 0) for `in == out`. -/
def cfusedFn (R1 R2 vlc : Nat) (fwd mem : Bool) : KM Unit := do
  let N := R1 * R2
  let k1 := butterflyK fwd R1 false
  let k2 := butterflyK fwd R2 true
  let tw := passTwiddles (Trig.cosSin2PiTable N) fwd N R2 R1
  let mid : Gpr := .rcx
  if mem then
    -- mid = the buffer if the record has one, else out
    KM.ins (.mov .rax (.mem (Mem.b .rdi 8)))
    KM.ins (.lea .rcx (Mem.bi .rdi .rax))
    KM.ins (.test .rax .rax)
    KM.ins (.cmov .e .rcx .rdx)
  let w := widthOf vlc
  -- twiddle `(r, k)` of the second pass, real (`e = 0`) or imaginary part
  let twBits (r k e : Nat) : UInt64 := (tw[(2 * (r - 1) + e) * R1 + k]!).toBits
  -- the first butterflies of the groups of pass 1
  let j0s : List Nat := (List.range (R2 / vlc)).map (· * vlc) ++
    (if R2 % vlc == 0 then [] else [R2 - vlc])
  -- pass 1, butterflies `j = j0 + c` (`c` = complex lane): input `r` is `in[j + r·R2]`
  let pass1 (j0 : Nat) : BlockM (Array VId) := do
    let mut x : Array VId := #[]
    for r in [0:R1] do
      x := x.push (← BlockM.load (Mem.b .rsi (16 * (j0 + r * R2))))
    instC k1 vlc (x[·]!)
  let spec1 (j0 : Nat) : SpecB (Array (Array Nat)) := do
    let mut o : Array (Array Nat) := #[]
    for c in [0:vlc] do
      let mut inp : Array Nat := #[]
      for r in [0:R1] do
        let cell := Mem.b .rsi (16 * (j0 + r * R2))
        inp := inp.push (← SpecB.node (.inp cell (2 * c)))
        inp := inp.push (← SpecB.node (.inp cell (2 * c + 1)))
      o := o.push (← SpecB.kernel k1 inp)
    return o
  -- pass 2, butterflies `k = kb·VLc + c`: input `r` is output `k` of pass-1 butterfly `r`
  let pass2 (kb : Nat) (x : Nat → VId) : BlockM Unit := do
    let mut inp : Array VId := #[]
    for r in [0:R2] do inp := inp.push (x r)
    for r in [1:R2] do
      let bits := (Array.range (2 * vlc)).map fun i => twBits r (kb * vlc + i / 2) (i % 2)
      inp := inp.push (← BlockM.df (.cvec bits))
    let outs ← instC k2 vlc (inp[·]!)
    for r in [0:R2] do
      BlockM.store (Mem.b .rdx (16 * (kb * vlc + r * R1))) outs[r]!
  let spec2 (kb : Nat) (x : Nat → Nat → Nat → SpecB Nat) : SpecB (List (Mem × Array Nat)) := do
    let mut o : Array (Array Nat) := #[]
    for c in [0:vlc] do
      let mut inp : Array Nat := #[]
      for r in [0:R2] do
        inp := inp.push (← x r c 0)
        inp := inp.push (← x r c 1)
      for r in [1:R2] do
        inp := inp.push (← SpecB.node (.bits (twBits r (kb * vlc + c) 0)))
        inp := inp.push (← SpecB.node (.bits (twBits r (kb * vlc + c) 1)))
      o := o.push (← SpecB.kernel k2 inp)
    return (List.range R2).map fun (r : Nat) =>
      (Mem.b .rdx (16 * (kb * vlc + r * R1)), (Array.range (2 * vlc)).map fun i => o[i / 2]![2 * r + i % 2]!)
  if mem then
    -- one block per group of butterflies: within a block all loads precede all stores
    for j0 in j0s do
      let cell (kb m : Nat) : Mem := Mem.b mid (16 * (kb * vlc + (j0 + m) * R1))
      let spec : Spec := SpecB.spec do
        let o ← spec1 j0
        let mut res : List (Mem × Array Nat) := []
        for kb in [0:R1 / vlc] do
          for m in [0:vlc] do
            res := (cell kb m, (Array.range (2 * vlc)).map fun i =>
              o[m]![2 * (kb * vlc + i / 2) + i % 2]!) :: res
        return res
      KM.block w (spec := some spec) do
        let outs ← pass1 j0
        for kb in [0:R1 / vlc] do
          let cols ← ctranspose vlc ((Array.range vlc).map fun l => outs[kb * vlc + l]!)
          for m in [0:vlc] do
            BlockM.store (cell kb m) cols[m]!
    for kb in [0:R1 / vlc] do
      let cell (r : Nat) : Mem := Mem.b mid (16 * (kb * vlc + r * R1))
      let spec : Spec := SpecB.spec (spec2 kb fun r c e => SpecB.node (.inp (cell r) (2 * c + e)))
      KM.block w (spec := some spec) do
        let mut x : Array VId := #[]
        for r in [0:R2] do x := x.push (← BlockM.load (cell r))
        pass2 kb (x[·]!)
  else
    let spec : Spec := SpecB.spec do
      let mut o1 : Array (Array Nat) := Array.replicate R2 #[]
      for j0 in j0s do
        let o ← spec1 j0
        for c in [0:vlc] do o1 := o1.set! (j0 + c) o[c]!
      let mut res : List (Mem × Array Nat) := []
      for kb in [0:R1 / vlc] do
        let o := o1
        res := res ++ (← spec2 kb fun r c e => pure (o[r]![2 * (kb * vlc + c) + e]!))
      return res
    KM.block w (spec := some spec) do
      let mut X : Array (Array VId) := Array.replicate (R1 / vlc) (Array.replicate R2 0)
      for j0 in j0s do
        let outs ← pass1 j0
        for kb in [0:R1 / vlc] do
          let cols ← ctranspose vlc ((Array.range vlc).map fun l => outs[kb * vlc + l]!)
          for m in [0:vlc] do
            X := X.set! kb ((X[kb]!).set! (j0 + m) cols[m]!)
      for kb in [0:R1 / vlc] do
        pass2 kb ((X[kb]!)[·]!)

/-! ## The plan interpreter -/

/-- Call (or jump to) the function of the record at `rdi`. Clobbers `rax`, `r11`. -/
def dispatch (tail : Bool) : Array Instr :=
  #[.mov .rax (.mem (Mem.b .rdi)), .lea .r11 (Mem.rip "lfa_table"),
    if tail then .jmpMem (Mem.bi .r11 .rax 8) else .callMem (Mem.bi .r11 .rax 8)]

/-- The loop of `lfa_loop`. With `range`, only the iterations `r8 … r8 + r9 − 1`. -/
def loopBody (l : String) (range : Bool) : Array Instr :=
  #[.push .rbx, .push .rbp, .push .r12, .push .r13, .push .r14, .push .r15,
    .sub .rsp (.imm 24),
    .mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov .r14 (.reg .rcx),
    .mov .rbp (.mem (Mem.b .rbx 40)), .add .rbp (.reg .rbx)] ++
  (if range then
    #[.mov .r15 (.reg .r9), .test .r15 .r15, .jcc .e s!"{l}_done",
      .mov .rax (.mem (Mem.b .rbx 16)), .imul2 .rax (.reg .r8), .add .r12 (.reg .rax),
      .mov .rax (.mem (Mem.b .rbx 24)), .imul2 .rax (.reg .r8), .add .r13 (.reg .rax),
      .mov .rax (.mem (Mem.b .rbx 32)), .imul2 .rax (.reg .r8), .add .r14 (.reg .rax),
      .mov .rax (.mem (Mem.b .rbx 48)), .imul2 .rax (.reg .r8), .add .rbp (.reg .rax)]
   else #[.mov .r15 (.mem (Mem.b .rbx 8))]) ++
  #[.label s!"{l}_iter",
    .mov .rax (.imm 0), .store (Mem.b .rsp 0) .rax,
    .label s!"{l}_child",
    .mov .rdi (.mem (Mem.bi .rbx .rax 8 64)), .add .rdi (.reg .rbx),
    .mov .rsi (.reg .r12),
    .mov .rdx (.reg .r13), .add .rdx (.mem (Mem.b .rbp)),
    .mov .rcx (.reg .r14)] ++ dispatch false ++
  #[.mov .rax (.mem (Mem.b .rsp 0)), .inc .rax, .store (Mem.b .rsp 0) .rax,
    .cmp .rax (.mem (Mem.b .rbx 56)), .jcc .b s!"{l}_child",
    .add .r12 (.mem (Mem.b .rbx 16)), .add .r13 (.mem (Mem.b .rbx 24)),
    .add .r14 (.mem (Mem.b .rbx 32)), .add .rbp (.mem (Mem.b .rbx 48)),
    .dec .r15, .jcc .ne s!"{l}_iter",
    .label s!"{l}_done",
    .add .rsp (.imm 24),
    .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbp, .pop .rbx, .ret]

/-- `lfa_loop`: run the children `count` times, advancing `in`, `out` and `col`.

Record: `1`: count; `2`, `3`, `4`: what `in`, `out` (bytes) and `col` advance per iteration;
`5`: table of byte offsets added to `out` in each iteration; `6`: bytes the table pointer
advances per iteration (0 or 8); `7`: number of children; `8…`: the children. -/
def loopFn : Array Instr := loopBody ".Llfa_loop" false

/-- `lfa_loop_range`: iterations `r8 … r8 + r9 − 1` of the loop record `rdi`. -/
def loopRangeFn : Array Instr := loopBody ".Llfa_loop_range" true

/-! ### Threads

The worker threads are Lean tasks (`Pool.start`) that run `lfa_worker`, a loop in assembly.
`lfa_pool` is the state they share with the thread that executes plans:

* `0`: generation (32 bits, the futex word): incremented to publish a job;
* `8`, `16`, `24`, `32`: the job: a loop record, `in`, `out`, `col`;
* `40`: number of workers `nw`; a job has `nw + 1` parts, part `p` being the iterations
  `⌊p·count/(nw+1)⌋ … ⌊(p+1)·count/(nw+1)⌋ − 1` of the loop;
* `64`: workers that have not finished the job; `128`: workers asleep;
* `136`: workers running; `192`: workers must return.

A worker waits for the generation to change, spinning for a while (about a millisecond) and
then sleeping in `futex`, so a job published soon after the previous one starts within
nanoseconds. -/

/-- A word of the pool; `r12` holds its address. -/
def poolW (d : Int) : Mem := Mem.b .r12 d

/-- `futex(pool, op, val)`. -/
def futexCall (op : Int) (val : GSrc) : Array Instr :=
  #[.mov .rax (.imm 202), .mov .rdi (.reg .r12), .mov .rsi (.imm op), .mov .rdx val,
    .mov .r10 (.imm 0), .syscall]

/-- `lfa_ploop`: a loop (record as for `lfa_loop`) whose iterations are shared among the
threads of the pool. The iterations must write disjoint memory, and none may read what
another writes. Runs as `lfa_loop` when there are no workers or fewer iterations than
threads. -/
def ploopFn : Array Instr :=
  let l := ".Llfa_ploop"
  #[.lea .r10 (Mem.rip "lfa_pool"),
    .mov .rax (.mem (Mem.b .r10 40)),
    .test .rax .rax, .jcc .e "lfa_loop",
    .cmp .rax (.mem (Mem.b .rdi 8)), .jcc .ae "lfa_loop",
    .push .r12, .mov .r12 (.reg .r10),
    .store (poolW 8) .rdi, .store (poolW 16) .rsi, .store (poolW 24) .rdx, .store (poolW 32) .rcx,
    .store (poolW 64) .rax,
    .lockInc32 (poolW 0),
    .mov .rax (.mem (poolW 128)), .test .rax .rax, .jcc .e s!"{l}_nowake"] ++
  futexCall 1 (.imm 0x7fffffff) ++
  #[.label s!"{l}_nowake",
    -- part 0
    .mov .rdi (.mem (poolW 8)),
    .mov .rax (.mem (Mem.b .rdi 8)), .mov .rdx (.imm 0),
    .mov .r9 (.mem (poolW 40)), .inc .r9, .div .r9,
    .mov .r9 (.reg .rax), .mov .r8 (.imm 0),
    .mov .rsi (.mem (poolW 16)), .mov .rdx (.mem (poolW 24)), .mov .rcx (.mem (poolW 32)),
    .call "lfa_loop_range",
    .label s!"{l}_wait",
    .mov .rax (.mem (poolW 64)), .test .rax .rax, .jcc .e s!"{l}_done", .pause, .jmp s!"{l}_wait",
    .label s!"{l}_done",
    .pop .r12, .ret]

/-- `lfa_worker(w)`, called from Lean as an `IO Unit`: worker `w ≥ 1` of the pool. Returns
when the pool is stopped. -/
def workerFn : Array Instr :=
  let l := ".Llfa_worker"
  #[.push .rbx, .push .r12, .push .r13, .push .r14, .push .r15,
    .mov .rbx (.reg .rdi),
    .lea .r12 (Mem.rip "lfa_pool"),
    .mov32 .r13 (poolW 0),
    .lockInc (poolW 136),
    .label s!"{l}_loop",
    .mov .r14 (.imm 20000),
    .label s!"{l}_spin",
    .mov32 .rax (poolW 0), .cmp .rax (.reg .r13), .jcc .ne s!"{l}_work",
    .pause, .dec .r14, .jcc .ne s!"{l}_spin",
    .lockInc (poolW 128)] ++
  futexCall 0 (.reg .r13) ++
  #[.lockDec (poolW 128), .jmp s!"{l}_loop",
    .label s!"{l}_work",
    .mov .r13 (.reg .rax),
    .mov .rax (.mem (poolW 192)), .test .rax .rax, .jcc .ne s!"{l}_exit",
    .mov .rdi (.mem (poolW 8)),
    .mov .rcx (.mem (Mem.b .rdi 8)),
    .mov .r9 (.mem (poolW 40)), .inc .r9,
    .mov .rax (.reg .rcx), .imul2 .rax (.reg .rbx), .mov .rdx (.imm 0), .div .r9,
    .mov .r8 (.reg .rax),
    .lea .rax (Mem.b .rbx 1), .imul2 .rax (.reg .rcx), .mov .rdx (.imm 0), .div .r9,
    .sub .rax (.reg .r8), .mov .r9 (.reg .rax),
    .mov .rsi (.mem (poolW 16)), .mov .rdx (.mem (poolW 24)), .mov .rcx (.mem (poolW 32)),
    .call "lfa_loop_range",
    .lockDec (poolW 64),
    .jmp s!"{l}_loop",
    .label s!"{l}_exit",
    .lockDec (poolW 136),
    .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbx,
    .mov .rdi (.imm 0), .jmp "lfa_ok_unit@PLT"]

/-- `lfa_pool_load(d)`, an `IO USize`: the word at byte `d` of the pool. -/
def poolLoadFn : Array Instr :=
  #[.lea .rax (Mem.rip "lfa_pool"), .mov .rdi (.mem (Mem.bi .rax .rdi 1)), .jmp "lfa_ok_usize@PLT"]

/-- `lfa_pool_store(d, v)`, an `IO Unit`. -/
def poolStoreFn : Array Instr :=
  #[.lea .rax (Mem.rip "lfa_pool"), .store (Mem.bi .rax .rdi 1) .rsi,
    .mov .rdi (.imm 0), .jmp "lfa_ok_unit@PLT"]

/-- `lfa_pool_wake`, an `IO Unit`: a new generation; wake the workers. -/
def poolWakeFn : Array Instr :=
  #[.push .r12, .lea .r12 (Mem.rip "lfa_pool"), .lockInc32 (poolW 0)] ++
  futexCall 1 (.imm 0x7fffffff) ++
  #[.pop .r12, .mov .rdi (.imm 0), .jmp "lfa_ok_unit@PLT"]

/-- `lfa_copyin`: when `in == out`, copy the input to the plan's buffer and read it there.

Record: `1`: bytes; `2`: the buffer; `3`: the child. -/
def copyinFn : Array Instr :=
  let l := ".Llfa_copyin"
  #[.cmp .rsi (.reg .rdx), .jcc .ne s!"{l}_go",
    .mov .r8 (.reg .rdi), .mov .r9 (.reg .rcx),
    .mov .rcx (.mem (Mem.b .rdi 8)),
    .mov .rax (.mem (Mem.b .rdi 16)), .add .rax (.reg .rdi),
    .mov .rdi (.reg .rax),
    .repMovsb,
    .mov .rsi (.reg .rax), .mov .rdi (.reg .r8), .mov .rcx (.reg .r9),
    .label s!"{l}_go",
    .add .rdi (.mem (Mem.b .rdi 24))] ++ dispatch true

/-- `lfa_call(record, in, out)`: run a plan (C calling convention). -/
def callFn : Array Instr := #[.mov .rcx (.imm 0)] ++ dispatch true

/-- `lfa_run(mem, root, in, out, reps)`, called from Lean as an `IO Unit`: run the record at
word `root` of the `FloatArray` `mem`, `reps` times. Returns through `lfa_ok_unit`, a Lean
function that builds the `IO` result. -/
def runFn : Array Instr :=
  let l := ".Llfa_run"
  #[.push .rbx, .push .r12, .push .r13, .push .r14, .push .r15,
    .lea .rbx (Mem.bi .rdi .rsi 8 24),
    .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8),
    .test .r14 .r14, .jcc .e s!"{l}_done",
    .label s!"{l}_rep",
    .mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .rdx (.reg .r13), .mov .rcx (.imm 0)] ++
  dispatch false ++
  #[.dec .r14, .jcc .ne s!"{l}_rep",
    .label s!"{l}_done",
    .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbx,
    .mov .rdi (.imm 0),
    .jmp "lfa_ok_unit@PLT"]

/-- `lfa_addr(a)`: the address of the data of a `FloatArray` (Lean scalar arrays keep their
data 24 bytes after the object header). -/
def addrFn : Array Instr := #[.lea .rax (Mem.b .rdi 24), .ret]

/-- `lfa_zero(p, n)`, called from Lean as an `IO Unit`: store `n` zero words at address `p`. -/
def zeroFn : Array Instr :=
  #[.mov .rcx (.reg .rsi), .mov .rax (.imm 0), .repStosq, .mov .rdi (.imm 0), .jmp "lfa_ok_unit@PLT"]

/-! ## The functions of the engine

`lfa_table[i]` is the address of function `i` of `registry`; records name functions by this
index. -/

/-- Choices of the generator that do not change what a function computes. -/
structure GenOpts where
  /-- a load with at most this many uses is used as a memory operand -/
  foldLimit : Nat := 2
  /-- instruction order (`ACfg.sched`) -/
  sched : Nat := 1
  deriving Repr, Inhabited

/-- Add a function written in `KM`. -/
def addKM (f : AsmFile) (name : String) (body : KM Unit) (o : GenOpts := {}) :
    Except String AsmFile :=
  f.addFn name (do let _ ← body.run {}; pure ()) o.foldLimit true o.sched

structure FnDef where
  name : String
  add : AsmFile → GenOpts → Except String AsmFile

instance : Inhabited FnDef := ⟨"", fun f _ => pure f⟩

def FnDef.km (name : String) (body : KM Unit) : FnDef :=
  ⟨name, fun f o => addKM f name body o⟩

def FnDef.raw (name : String) (body : Array Instr) : FnDef :=
  ⟨name, fun f _ => pure (f.addRaw name body)⟩

def leafRadices : List Nat := [8, 16, 32]
def ditRadices : List Nat := [2, 4, 8, 16, 32]

/-- Prefetch variants of the leaf passes (`leafFn`): none, and the next outputs. -/
def leafPrefetch : List Nat := [0, 2]

/-- Sizes of the one-butterfly transforms. -/
def csmallSizes : List Nat :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30,
   33, 35, 36, 39, 40, 42, 44, 45, 48, 49, 50, 52, 54, 55, 56, 60, 63]

/-- `(R1, R2, VLc)` of the two-pass transforms in registers. -/
def cfusedSet : List (Nat × Nat × Nat) :=
  [(2, 2, 2), (2, 4, 2), (4, 2, 2), (4, 4, 2), (4, 4, 4), (4, 8, 4), (8, 4, 4), (8, 8, 4),
   (4, 16, 4), (16, 4, 4), (8, 16, 4), (16, 8, 4),
   -- sizes that are not powers of two, up to 100
   (6, 3, 2), (2, 9, 2), (4, 5, 4), (2, 11, 2), (4, 6, 4), (2, 13, 2), (4, 7, 4), (2, 15, 2),
   (6, 5, 2), (4, 9, 4), (4, 10, 4), (8, 5, 4), (6, 7, 2), (14, 3, 2), (4, 11, 4), (12, 4, 4),
   (4, 12, 4), (10, 5, 2), (4, 13, 4), (6, 9, 2), (18, 3, 2), (8, 7, 4), (4, 15, 4), (12, 5, 4),
   (6, 11, 2), (10, 7, 2), (14, 5, 2), (12, 6, 4), (8, 9, 4), (6, 13, 2), (20, 4, 4),
   (8, 10, 4), (12, 7, 4), (8, 11, 4), (6, 15, 2), (10, 9, 2), (24, 4, 4), (12, 8, 4),
   (14, 7, 2), (20, 5, 4)]

/-- `(R1, R2, VLc)` of the two-pass transforms through a work array. -/
def ctwoSet : List (Nat × Nat × Nat) :=
  [(8, 16, 4), (16, 8, 4), (4, 32, 4), (32, 4, 4), (16, 16, 4), (8, 32, 4), (32, 8, 4),
   (16, 32, 4), (32, 16, 4), (32, 32, 4),
   -- sizes that are not powers of two, from 64 to 256
   (6, 11, 2), (10, 7, 2), (14, 5, 2), (12, 6, 4), (8, 9, 4), (6, 13, 2), (20, 4, 4),
   (8, 10, 4), (12, 7, 4), (8, 11, 4), (6, 15, 2), (10, 9, 2), (24, 4, 4), (12, 8, 4),
   (14, 7, 2), (20, 5, 4), (8, 13, 4), (12, 9, 4), (10, 11, 2), (28, 4, 4), (16, 7, 4),
   (8, 15, 4), (12, 10, 4), (14, 9, 2), (18, 7, 2), (20, 7, 4), (12, 12, 4), (10, 15, 2),
   (40, 4, 4), (18, 9, 2), (24, 7, 4), (12, 15, 4), (48, 4, 4), (28, 7, 4), (20, 10, 4),
   (14, 15, 2), (36, 6, 4), (56, 4, 4), (20, 12, 4), (36, 7, 4),
   (16, 6, 4), (16, 9, 4), (16, 10, 4), (16, 12, 4), (16, 15, 4), (16, 5, 4)]

/-- Radices of the Stockham passes. -/
def stkRadices : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16]

/-- Radices of the first pass of the blocked Stockham schedule (the later passes have the
radices `stkRadices`). At least 4: the pads of a run are fewer than its numbers. -/
def bstk0Radices : List Nat :=
  [5, 6, 7, 8, 12, 14, 15, 16, 20, 21, 22, 24, 25, 27, 28, 30, 32, 35, 36, 39, 40, 44, 45, 48,
   54, 55, 56, 60, 63, 64]

/-- The functions records can name, in table order. -/
def registry : Array FnDef := Id.run do
  let mut r : Array FnDef := #[.raw "lfa_loop" loopFn, .raw "lfa_copyin" copyinFn,
    .raw "lfa_ploop" ploopFn]
  for fwd in [true, false] do
    for R in leafRadices do
      for pf in leafPrefetch do r := r.push (.km (leafName R fwd pf) (leafFn R fwd pf))
    for R in ditRadices do
      r := r.push (.km (ditName R fwd false) (ditFn R fwd false))
      r := r.push (.km (ditName R fwd true) (ditFn R fwd true))
    for N in csmallSizes do r := r.push (.km (csmallName N fwd) (csmallFn N fwd))
    for (R1, R2, vlc) in cfusedSet do
      r := r.push (.km (cfusedName R1 R2 vlc fwd) (cfusedFn R1 R2 vlc fwd false))
    for (R1, R2, vlc) in ctwoSet do
      r := r.push (.km (ctwoName R1 R2 vlc fwd) (cfusedFn R1 R2 vlc fwd true))
    for R in stkRadices do
      r := r.push (.km (stk0Name R fwd) (stk0Fn R fwd))
      r := r.push (.km (stkName R fwd) (stkFn R fwd))
    for R in bstk0Radices do r := r.push (.km (bstk0Name R fwd) (bstk0Fn R fwd))
    for R in stkRadices do
      r := r.push (.km (bstkName R fwd false) (bstkFn R fwd))
      r := r.push (.km (bstkName R fwd true) (bstkLastFn R fwd))
  return r

/-- Index of a function in `lfa_table`. -/
def fnIndex : Std.HashMap String Nat :=
  (List.range registry.size).foldl (fun m i => m.insert registry[i]!.name i) {}

/-- The functions of the engine. -/
def engineFile (opts : String → GenOpts := fun _ => {}) : Except String AsmFile := do
  let mut f : AsmFile := {}
  for d in registry do f ← d.add f (opts d.name)
  f := f.addRaw "lfa_call" callFn
  f := f.addRaw "lfa_run" runFn
  f := f.addRaw "lfa_addr" addrFn
  f := f.addRaw "lfa_zero" zeroFn
  f := f.addRaw "lfa_loop_range" loopRangeFn
  f := f.addRaw "lfa_worker" workerFn
  f := f.addRaw "lfa_pool_load" poolLoadFn
  f := f.addRaw "lfa_pool_store" poolStoreFn
  f := f.addRaw "lfa_pool_wake" poolWakeFn
  let mut tab := "\t.section .data.rel.ro,\"aw\"\n\t.p2align 3\n\t.globl lfa_table\nlfa_table:\n"
  for d in registry do tab := tab ++ s!"\t.quad {d.name}\n"
  let pool := "\t.bss\n\t.p2align 6\nlfa_pool:\n\t.zero 256\n"
  return { f with extra := (f.extra.push tab).push pool }

/-- The assembly file of the engine, with the numbers of blocks of vector code that were
checked against a specification and that have none. -/
def engineAsm (opts : String → GenOpts := fun _ => {}) : Except String (String × Nat × Nat) := do
  let f ← engineFile opts
  let checked := f.fns.foldl (fun n fn => n + fn.checked) 0
  let unchecked := f.fns.foldl (fun n fn => n + fn.unchecked) 0
  return (f.print, checked, unchecked)

end LeanFFTW.Asm
