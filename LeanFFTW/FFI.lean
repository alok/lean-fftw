/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.Problem

/-!
# C entry points of the generic engine

Problems arrive from C encoded as a `FloatArray` of small integers (exact in binary64):

```
[kind, sign, rank, vrank, inRe, inIm, outRe, outIm,
 (n, is, os) × rank, (n, is, os) × vrank, r2rkind × rank (r2r only)]
```

`kind` is 0 = complex DFT, 1 = rdft2, 2 = r2r; `sign` is −1 (forward) or +1; strides and
offsets are in units of `double`s. r2r kinds use libbench2's numbering (`R2R_R2HC = 0` …).
-/

namespace LeanFFTW.FFI

/-- libbench2's r2r kind numbering. -/
def kindOfNat : Nat → R2RKind
  | 0 => .r2hc | 1 => .hc2r | 2 => .dht | 3 => .redft00 | 4 => .redft01 | 5 => .redft10
  | 6 => .redft11 | 7 => .rodft00 | 8 => .rodft01 | 9 => .rodft10 | _ => .rodft11

/-- Decode a problem specification. -/
def decode (s : FloatArray) : Option Problem := do
  let gi (i : Nat) : Int := (s.get! i).toInt64.toInt
  let gn (i : Nat) : Nat := (s.get! i).toUInt64.toNat
  let kind := gn 0
  let fwd := gi 1 < 0
  let r := gn 2
  let v := gn 3
  let dim (i : Nat) : IODim := ⟨gn i, gi (i + 1), gi (i + 2)⟩
  let sz := (Array.range r).map fun d => dim (8 + 3 * d)
  let vecsz := (Array.range v).map fun d => dim (8 + 3 * r + 3 * d)
  let k ← match kind with
    | 0 => some (Kind.dft fwd)
    | 1 => some (Kind.rdft2 fwd)
    | 2 => some (Kind.r2r ((Array.range r).map fun d => kindOfNat (gn (8 + 3 * (r + v) + d))))
    | _ => none
  return ⟨k, sz, vecsz, gi 4, gi 5, gi 6, gi 7⟩

/-- Plan a problem; `none` if unsupported. -/
@[export lfftw_generic_plan]
def planFFI (spec : FloatArray) : Option ProblemPlan :=
  (decode spec).bind planProblem

/-- Execute a plan, reading `inp` and returning `out` with the output entries written.
All arguments are owned (the C caller passes references it has incremented). -/
@[export lfftw_generic_exec]
def execFFI (pp : ProblemPlan) (inp : FloatArray) (out : FloatArray) : FloatArray :=
  execProblem pp inp out

end LeanFFTW.FFI
