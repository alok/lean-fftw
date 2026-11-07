/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Native.Kernels
import LeanFFTW.Gen.InPlace

/-!
# A transform compiled by Lean

`exec p x` is defined as the proved in-place schedule `inplaceWith floatArith` of the plan
`p` (so `LeanFFTW/Proof/Native.lean` can prove it equals the binary64 reference
`refTransform`, and over the reals the DFT). Its compiled implementation `execU` runs the
generated straight-line kernels of `LeanFFTW/Native/Kernels.lean` over one unboxed
`FloatArray`, written in place: Lean's compiler turns each butterfly into C `double`
arithmetic on registers and each array access into a plain load or store.

The unsafe part is small and removable: `execU` indexes without bounds checks, relying on
the plan's invariants (`Plan.valid`, the leaf offsets and twiddle tables computed by
`Plan.make?`) and on the size check of its input. Replacing `implemented_by execU` by
nothing gives the same function, only slower. The two are checked bit for bit by
`scripts/NativeCheck.lean`.
-/

namespace LeanFFTW.Native

open LeanFFTW LeanFFTW.Gen

/-- Radix sequences the Lean backend runs: radices in `leanRadices` (2, 4, 8, 16), product `N`. -/
def validPlan (N : Nat) (rs : Array Nat) : Bool :=
  0 < rs.size && rs.all (· ∈ [2, 4, 8, 16]) && rs.toList.prod == N

/-- The twiddle tables of the passes (as `refTransform` computes them). -/
def refTw (fwd : Bool) (N : Nat) (rs : Array Nat) (t : Nat) : Array Float :=
  (passTwiddles (Trig.cosSin2PiTable N) fwd N (rs.getD t 1) (passNs rs t)).data

/-- A plan of the Lean backend, with its tables precomputed. -/
structure Plan where
  fwd : Bool
  N : Nat
  rs : Array Nat
  /-- Leaf `d` writes at `ofs[d]` (`leafOffsets`, exact in binary64). -/
  ofs : FloatArray
  /-- Twiddle table of pass `t` (`tws[0]` is unused). -/
  tws : Array FloatArray
  valid : validPlan N rs = true
  hofs : ofs = ⟨(leafOffsets N rs).map (·.toFloat)⟩
  htws : tws = (Array.range rs.size).map fun t => ⟨refTw fwd N rs t⟩

def Plan.make? (fwd : Bool) (N : Nat) (rs : Array Nat) : Option Plan :=
  if h : validPlan N rs = true then
    some { fwd, N, rs, ofs := _, tws := _, valid := h, hofs := rfl, htws := rfl }
  else none

/-- The transform of plan `p`: the proved in-place schedule. -/
def execRef (p : Plan) (x : @& FloatArray) : FloatArray :=
  ⟨inplaceWith floatArith p.fwd p.N p.rs (refTw p.fwd p.N p.rs) x.data⟩

/-- A `FloatArray` of `n` zeros. -/
def zeros (n : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  for _ in [0:n] do
    a := a.push 0.0
  return a

unsafe def passesU (p : Plan) (t : Nat) (y : FloatArray) : FloatArray :=
  if t < p.rs.size then
    let R := p.rs[t]!
    let ns := passNs p.rs t
    let tw := p.tws[t]!
    let nB := (p.N / (ns * R)).toUSize
    let y := if p.fwd then ditPassf R tw ns.toUSize nB y else ditPassb R tw ns.toUSize nB y
    passesU p (t + 1) y
  else y

/-- The transform written into `y` (consumed; reused in place when it is unshared and has
size `2·N`, so a caller that threads its output buffer allocates nothing). -/
unsafe def execIntoU (p : Plan) (x : @& FloatArray) (y : FloatArray) : FloatArray :=
  if x.size != 2 * p.N then execRef p x
  else
    let R0 := p.rs[0]!
    let n := (p.N / R0).toUSize
    let y := own (if y.size == 2 * p.N then y else zeros (2 * p.N))
    let y := if p.fwd then leafPassf R0 x p.ofs n n y else leafPassb R0 x p.ofs n n y
    passesU p 1 y

unsafe def execU (p : Plan) (x : @& FloatArray) : FloatArray :=
  execIntoU p x (zeros (2 * p.N))

/-- Stockham passes `t, t+1, …`: pass `t - 1` left its output in `a`; `b` is free. -/
unsafe def stPassesU (p : Plan) (bInnerBelow : Nat) (t : Nat) (a b : FloatArray) : FloatArray :=
  if t < p.rs.size then
    let R := p.rs[t]!
    let ns := passNs p.rs t
    let tw := p.tws[t]!
    let m := (p.N / R).toUSize
    let nB := (p.N / (ns * R)).toUSize
    let bi := ns < bInnerBelow
    let b := if p.fwd then stPassf R a tw m ns.toUSize nB bi b else stPassb R a tw m ns.toUSize nB bi b
    stPassesU p bInnerBelow (t + 1) b a
  else a

/-- The Stockham schedule (`refTransform`), out of place: pass `t` reads one buffer and writes
the other, and the last pass writes `y`. -/
unsafe def execStU (p : Plan) (bInnerBelow : Nat) (x : @& FloatArray) (y : FloatArray) : FloatArray :=
  if x.size != 2 * p.N then execRef p x
  else
    let n := (2 * p.N).toUSize
    let y := own (if y.size == 2 * p.N then y else alloc n)
    let w := alloc n
    let (a, b) := if p.rs.size % 2 == 1 then (y, w) else (w, y)
    let R0 := p.rs[0]!
    let m := (p.N / R0).toUSize
    let tw := p.tws[0]!
    let a := if p.fwd then stPassf R0 x tw m 1 m false a else stPassb R0 x tw m 1 m false a
    stPassesU p bInnerBelow 1 a b

/-- `exec p x` by the Stockham schedule, written into `y`; the loop over blocks is innermost
in the passes with fewer than `bInnerBelow` butterflies per block. -/
@[implemented_by execStU]
def execStInto (p : Plan) (_bInnerBelow : Nat) (x : @& FloatArray) (_y : FloatArray) : FloatArray :=
  execRef p x

/-- Interleaved `x` (`2h` floats) to split `y` (real parts, then imaginary parts). -/
unsafe def splitU (x : @& FloatArray) (h i : USize) (y : FloatArray) : FloatArray :=
  if i < h then splitU x h (i + 1) (wr (wr y i (rd x (2 * i))) (h + i) (rd x (2 * i + 1))) else y

/-- Split `x` to interleaved `y`. -/
unsafe def mergeU (x : @& FloatArray) (h i : USize) (y : FloatArray) : FloatArray :=
  if i < h then mergeU x h (i + 1) (wr (wr y (2 * i) (rd x i)) (2 * i + 1) (rd x (h + i))) else y

/-- Split-format Stockham passes `t, t+1, …`: the previous pass left its output in `a`. -/
unsafe def svPassesU (p : Plan) (t : Nat) (a b : FloatArray) : FloatArray × FloatArray :=
  if t < p.rs.size then
    let R := p.rs[t]!
    let ns := passNs p.rs t
    let m := (p.N / R).toUSize
    let nB := (p.N / (ns * R)).toUSize
    let h := p.N.toUSize
    let b := if p.fwd then svPassf R a p.tws[t]! h m ns.toUSize nB b
      else svPassb R a p.tws[t]! h m ns.toUSize nB b
    svPassesU p (t + 1) b a
  else (a, b)

/-- The Stockham schedule on split data: deinterleave, run the passes with the lane-batched
kernels, interleave into `y`. -/
unsafe def execSvU (p : Plan) (x : @& FloatArray) (y : FloatArray) : FloatArray :=
  if x.size != 2 * p.N then execRef p x
  else
    let n := (2 * p.N).toUSize
    let h := p.N.toUSize
    let y := own (if y.size == 2 * p.N then y else alloc n)
    let a := splitU x h 0 (alloc n)
    let (a, _) := svPassesU p 0 a (alloc n)
    mergeU a h 0 y

/-- `exec p x` by the Stockham schedule on split data with lane-batched kernels, into `y`. -/
@[implemented_by execSvU]
def execSvInto (p : Plan) (x : @& FloatArray) (_y : FloatArray) : FloatArray := execRef p x

/-- The transform of plan `p` on interleaved complex data of length `2·p.N`. -/
@[implemented_by execU]
def exec (p : Plan) (x : @& FloatArray) : FloatArray := execRef p x

/-- `exec p x`, written into the buffer `y` (its contents are ignored). -/
@[implemented_by execIntoU]
def execInto (p : Plan) (x : @& FloatArray) (_y : FloatArray) : FloatArray := execRef p x

end LeanFFTW.Native
