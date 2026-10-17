/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.FastExec

/-!
# FFTW problems on strided buffers (generic engine)

This module executes the whole FFTW problem space (as parsed by libbench2 / FFTW's guru
interface) on top of the 1-D complex algorithms of `Alg.lean`:

* complex DFTs of any rank and vector rank, any sizes and strides, interleaved or split
  storage, in-place or out-of-place;
* r2c / c2r (FFTW's `rdft2`), multi-dimensional, with the half-length last dimension;
* all eleven r2r kinds, separably in every dimension, via exact symmetric embeddings into
  complex DFTs (see `R2RKind.embed`).

Data are first gathered into a contiguous logical row-major array over
`vector dims ++ transform dims`, transformed one dimension at a time, and scattered to the
output. Every buffer address is `offset + Σ index·stride`, with separate offsets for the
real and imaginary parts, which describes interleaved and split storage alike.
-/

namespace LeanFFTW

/-- One tensor dimension: size and input/output strides, in units of `Float`s. -/
structure IODim where
  n : Nat
  is : Int
  os : Int
  deriving Inhabited, Repr

/-- FFTW's r2r kinds, in libbench2/FFTW order. -/
inductive R2RKind where
  | r2hc | hc2r | dht | redft00 | redft01 | redft10 | redft11
  | rodft00 | rodft01 | rodft10 | rodft11
  deriving Inhabited, Repr, BEq

/-- Problem kinds. -/
inductive Kind where
  /-- complex DFT; `fwd` is FFTW_FORWARD (sign −1). -/
  | dft (fwd : Bool)
  /-- real-input forward (r2c) when `fwd`, complex-to-real backward (c2r) otherwise. -/
  | rdft2 (fwd : Bool)
  /-- real-to-real with one kind per transform dimension. -/
  | r2r (kinds : Array R2RKind)
  deriving Inhabited, Repr

/-- A problem: transform tensor `sz`, vector tensor `vecsz`, and the offsets of the real
and imaginary parts of the input and output in their buffers. Real data use `inRe`/`outRe`
only. For rdft2, `sz` gives the *real* sizes; strides are those of each side. -/
structure Problem where
  kind : Kind
  sz : Array IODim
  vecsz : Array IODim
  inRe : Int
  inIm : Int
  outRe : Int
  outIm : Int
  deriving Inhabited, Repr

namespace R2RKind

/-- Size of the complex forward DFT used by the embedding of a size-`n` transform of
this kind (`r2hc`, `hc2r`, `dht` use a size-`n` DFT, backward for `hc2r`). -/
def embedSize (k : R2RKind) (n : Nat) : Nat :=
  match k with
  | .r2hc | .hc2r | .dht => n
  | .redft00 => 2 * (n - 1)
  | .rodft00 => 2 * (n + 1)
  | .redft10 | .redft01 | .rodft10 | .rodft01 => 4 * n
  | .redft11 | .rodft11 => 8 * n

/-- The real sequence `z` of length `embedSize` whose forward DFT contains the
transform of `x` (see `extract`). Exact symmetric extensions; no arithmetic. -/
def embed (k : R2RKind) (n : Nat) (x : Nat → Float) (i : Nat) : Float :=
  let M := k.embedSize n
  match k with
  | .r2hc | .hc2r | .dht => x i
  | .redft00 => if i < n then x i else if i < M then x (M - i) else 0
  | .rodft00 =>
      if 1 ≤ i ∧ i ≤ n then x (i - 1)
      else if n + 2 ≤ i ∧ i < M then -(x (M - i - 1)) else 0
  | .redft10 => if i % 2 == 1 then (if i < 2 * n then x (i / 2) else x ((M - i) / 2)) else 0
  | .rodft10 => if i % 2 == 1 then (if i < 2 * n then x (i / 2) else -(x ((M - i) / 2))) else 0
  | .redft11 =>
      if i % 2 == 1 then
        (if i < 2 * n then x (i / 2) else if 6 * n < i then x ((M - i) / 2) else 0)
      else 0
  | .rodft11 =>
      if i % 2 == 1 then
        (if i < 2 * n then x (i / 2) else if 6 * n < i then -(x ((M - i) / 2)) else 0)
      else 0
  | .redft01 =>
      if i < n then x i else if 3 * n < i ∧ i < M then x (M - i) else 0
  | .rodft01 =>
      if 1 ≤ i ∧ i ≤ n then x (i - 1)
      else if 3 * n < i ∧ i < M then -(x (M - i - 1)) else 0

/-- Read output `k` of the transform from the forward DFT `F` of the embedding. -/
def extract (k : R2RKind) (n : Nat) (F : Nat → FC) (j : Nat) : Float :=
  match k with
  | .r2hc => if j ≤ n / 2 then (F j).re else (F (n - j)).im
  | .hc2r => (F j).re
  | .dht => (F j).re - (F j).im
  | .redft00 | .redft10 => (F j).re
  | .redft01 | .redft11 => (F (2 * j + 1)).re
  | .rodft00 | .rodft10 => -(F (j + 1)).im
  | .rodft01 | .rodft11 => -(F (2 * j + 1)).im

end R2RKind

/-- A 1-D line operation with its precomputed plan. -/
inductive LineOp where
  /-- complex DFT of size `n` → `n`. -/
  | cdft (p : Plan CArr)
  /-- real `n` → complex `n/2+1` (forward). -/
  | r2c (n : Nat) (p : Plan CArr)
  /-- complex `n/2+1` → real `n` (backward), FFTW's c2r. -/
  | c2r (n : Nat) (p : Plan CArr)
  /-- real `n` → real `n`. -/
  | r2r (k : R2RKind) (n : Nat) (p : Plan CArr)
  deriving Inhabited

/-- A 1-D binary64 plan of size `n` (prime-factor mixed radix). -/
def plan1d (fwd : Bool) (n : Nat) : Plan CArr :=
  mkPlan floatOps fwd (primeFactors n)

/-- Input and output lengths of a line operation. -/
def LineOp.lens : LineOp → Nat × Nat
  | .cdft p => (p.size, p.size)
  | .r2c n _ => (n, n / 2 + 1)
  | .c2r n _ => (n / 2 + 1, n)
  | .r2r _ n _ => (n, n)

/-- The Hermitian extension of a half-length array `h` (length `n/2+1`). -/
def hermExt (n : Nat) (h : Nat → FC) (k : Nat) : FC :=
  if k ≤ n / 2 then h k else let z := h (n - k); ⟨z.re, -z.im⟩

/-- Apply a line operation to an input view. Real outputs are returned with zero
imaginary parts. -/
def LineOp.apply (op : LineOp) (x : Nat → FC) : CArr :=
  match op with
  | .cdft p => execFloat p x
  | .r2c n p =>
      let F := execFloat p (fun j => ⟨(x j).re, 0.0⟩)
      CArr.ofFn (n / 2 + 1) F.get
  | .c2r n p =>
      let G := execFloat p (hermExt n x)
      CArr.ofFn n fun j => ⟨(G.get j).re, 0.0⟩
  | .r2r k n p =>
      match k with
      | .hc2r =>
          -- halfcomplex input: r_k at k (k ≤ n/2), i_k at n-k (0 < k < n-k)
          let hc : Nat → FC := fun j =>
            ⟨(x j).re, if 0 < j ∧ j < n - j then (x (n - j)).re else 0.0⟩
          let G := execFloat p (hermExt n hc)
          CArr.ofFn n fun j => ⟨(G.get j).re, 0.0⟩
      | _ =>
          let M := k.embedSize n
          let z := CArr.ofFn M fun i => ⟨k.embed n (fun j => (x j).re) i, 0.0⟩
          let F := execFloat p z.get
          CArr.ofFn n fun j => ⟨k.extract n F.get j, 0.0⟩

/-- Row-major product of sizes. -/
def prodSizes (ns : List Nat) : Nat := ns.foldl (· * ·) 1

/-- Apply `op` along axis `ax` of a logical row-major array with shape `shape`. Returns the
new array and shape (the axis length becomes the op's output length). -/
def alongAxis (shape : Array Nat) (ax : Nat) (op : LineOp) (data : CArr) : CArr × Array Nat :=
  let nIn := shape.getD ax 1
  let nOut := op.lens.2
  let outer := prodSizes (shape.toList.take ax)
  let inner := prodSizes (shape.toList.drop (ax + 1))
  let lines : Array CArr := (Array.range (outer * inner)).map fun l =>
    let a := l / inner
    let b := l % inner
    op.apply fun i => data.get (a * nIn * inner + i * inner + b)
  let shape' := shape.set! ax nOut
  let res := CArr.ofFn (outer * nOut * inner) fun L =>
    let b := L % inner
    let i := (L / inner) % nOut
    let a := L / (inner * nOut)
    (lines.getD (a * inner + b) default).get i
  (res, shape')

/-- Address of logical index `L` in a buffer, for dims with sizes `ns` (row-major) and
strides `ss`, from offset `off`. -/
def addrOf (ns : Array Nat) (ss : Array Int) (off : Int) (L : Nat) : Int := Id.run do
  let mut a := off
  let mut rem := L
  for d' in [0:ns.size] do
    let d := ns.size - 1 - d'
    let nd := ns.getD d 1
    a := a + ((rem % nd : Nat) : Int) * ss.getD d 0
    rem := rem / nd
  return a

/-- A planned problem. -/
structure ProblemPlan where
  prob : Problem
  /-- line operations, applied in order, each with the axis (into the logical shape) it
  acts on. -/
  ops : Array (Nat × LineOp)
  /-- logical shapes of the input and output (vector dims first). -/
  inShape : Array Nat
  outShape : Array Nat
  /-- whether input / output are real arrays. -/
  inReal : Bool
  outReal : Bool
  deriving Inhabited

/-- Plan a problem, ignoring empty vector dimensions. -/
def planProblemCore (p : Problem) : Option ProblemPlan :=
  let v := p.vecsz.size
  let r := p.sz.size
  let ns := p.sz.map (·.n)
  let vs := p.vecsz.map (·.n)
  if ns.any (· == 0) then none else
  match p.kind with
  | .dft fwd =>
      let ops := (Array.range r).map fun d => (v + d, LineOp.cdft (plan1d fwd (ns.getD d 1)))
      some ⟨p, ops, vs ++ ns, vs ++ ns, false, false⟩
  | .rdft2 fwd =>
      if r == 0 then none else
      let nl := ns.getD (r - 1) 1
      let half := ns.set! (r - 1) (nl / 2 + 1)
      if fwd then
        -- r2c along the last axis, then complex forward along the others
        let last := (v + r - 1, LineOp.r2c nl (plan1d true nl))
        let rest := (Array.range (r - 1)).map fun d =>
          (v + d, LineOp.cdft (plan1d true (ns.getD d 1)))
        some ⟨p, #[last] ++ rest, vs ++ ns, vs ++ half, true, false⟩
      else
        let first := (Array.range (r - 1)).map fun d =>
          (v + d, LineOp.cdft (plan1d false (ns.getD d 1)))
        let last := (v + r - 1, LineOp.c2r nl (plan1d false nl))
        some ⟨p, first ++ #[last], vs ++ half, vs ++ ns, false, true⟩
  | .r2r kinds =>
      if kinds.size != r then none
      else if (Array.range r).any (fun d => kinds.getD d .r2hc == .redft00 && ns.getD d 1 < 2)
      then none
      else
        let ops := (Array.range r).map fun d =>
          let k := kinds.getD d .r2hc
          let n := ns.getD d 1
          let fwd := k != .hc2r
          (v + d, LineOp.r2r k n (plan1d fwd (k.embedSize n)))
        some ⟨p, ops, vs ++ ns, vs ++ ns, true, true⟩

/-- Plan a problem. Returns `none` when the problem is outside the supported domain. As in
FFTW, transform dimensions must have `n ≥ 1`, while a vector dimension of size 0 is allowed
and makes the problem empty: nothing is read or written. -/
def planProblem (p : Problem) : Option ProblemPlan :=
  (planProblemCore p).map fun pp =>
    if p.vecsz.any (·.n == 0) then { pp with ops := #[] } else pp

/-- Execute a planned problem: read `inp`, write into (a copy of) `out`. -/
def execProblem (pp : ProblemPlan) (inp : FloatArray) (out : FloatArray) : FloatArray := Id.run do
  let p := pp.prob
  let istr : Array Int := p.vecsz.map (·.is) ++ p.sz.map (·.is)
  let ostr : Array Int := p.vecsz.map (·.os) ++ p.sz.map (·.os)
  let nIn := prodSizes pp.inShape.toList
  let rd (a : Int) : Float := inp.get! a.toNat
  let data := CArr.ofFn nIn fun L =>
    let re := rd (addrOf pp.inShape istr p.inRe L)
    let im := if pp.inReal then 0.0 else rd (addrOf pp.inShape istr p.inIm L)
    ⟨re, im⟩
  let mut cur := data
  let mut shape := pp.inShape
  for (ax, op) in pp.ops do
    let (c, s) := alongAxis shape ax op cur
    cur := c
    shape := s
  let nOut := prodSizes pp.outShape.toList
  let mut o := out
  for L in [0:nOut] do
    let z := cur.get L
    o := o.set! (addrOf pp.outShape ostr p.outRe L).toNat z.re
    if !pp.outReal then
      o := o.set! (addrOf pp.outShape ostr p.outIm L).toNat z.im
  return o

end LeanFFTW
