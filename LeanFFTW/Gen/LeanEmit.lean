/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Stockham

/-!
# Printing kernels as Lean code

The same CSE'd kernels that `Emit.lean` prints as SIMD C, printed instead as Lean
definitions over unboxed `Float` and `FloatArray`, for a backend that Lean's own compiler
builds (`LeanFFTW/Native`). Each in-place butterfly becomes one straight-line `unsafe def`
that reads its inputs from the array, runs the kernel's operations in order (one `let` per
operation, so the compiled code keeps them in registers as C `double`s) and writes its
outputs back. Constants are printed as `cst` (`Float.ofBits`, compiled to a C literal) of their exact bits, and the
operations are those of `floatArith`, so the printed code computes exactly
`Kernel.eval floatArith` (checked bit for bit by `LeanFFTW/Native/Check.lean`).
-/

namespace LeanFFTW.Gen

/-- Lean expression for one kernel operation (as `floatArith`). -/
def KOp.toLean (n : Nat → String) : KOp → String
  | .cst c => s!"cst {c.toFloat.toBits}"
  | .zero => "0.0"
  | .add a b => s!"{n a} + {n b}"
  | .sub a b => s!"{n a} - {n b}"
  | .mul a b => s!"{n a} * {n b}"
  | .neg a => s!"-{n a}"
  | .fma a b c => s!"Float.fma {n a} {n b} {n c}"
  | .fms a b c => s!"Float.fma {n a} {n b} (-{n c})"
  | .fnma a b c => s!"Float.fma (-{n a}) {n b} {n c}"

def leanBflyName (R : Nat) (tw fwd : Bool) : String :=
  s!"bfly{R}{if tw then "t" else "n"}{if fwd then "f" else "b"}"

/-- A butterfly of radix `R` as a Lean definition. Untwiddled (the leaf pass): reads complex
inputs `x[src + r·sstr]` and writes output `r` to `y[dst + r·dstr]`. Twiddled (in place):
reads `y[c + r·ns]` and the twiddles of column `q` of `tw` (rows of length `ns`), and writes
output `r` back to `y[c + r·ns]`. All reads happen before the first write, so `y` stays
unshared and every write is in place. -/
def emitLeanBfly (R : Nat) (twd fwd : Bool) : String := Id.run do
  let k := butterflyK fwd R twd
  let nIn := k.nIn
  let name (i : Nat) : String := if i < nIn then s!"i{i}" else s!"t{i}"
  let mut ls : List String := if twd then [
    s!"@[inline] unsafe def {leanBflyName R twd fwd} (tw : @& FloatArray) (y : FloatArray) (c ns q : USize) : FloatArray :="]
    else [
    s!"@[inline] unsafe def {leanBflyName R twd fwd} (x : @& FloatArray) (y : FloatArray) (src sstr dst dstr : USize) : FloatArray :="]
  for r in [0:R] do
    if twd then
      ls := ls ++ [s!"  let i{2 * r} := rd y (2 * (c + {r} * ns))",
                   s!"  let i{2 * r + 1} := rd y (2 * (c + {r} * ns) + 1)"]
    else
      ls := ls ++ [s!"  let i{2 * r} := rd x (2 * (src + {r} * sstr))",
                   s!"  let i{2 * r + 1} := rd x (2 * (src + {r} * sstr) + 1)"]
  if twd then
    for r in [1:R] do
      ls := ls ++ [s!"  let i{2 * R + 2 * (r - 1)} := rd tw ({2 * (r - 1)} * ns + q)",
                   s!"  let i{2 * R + 2 * (r - 1) + 1} := rd tw ({2 * (r - 1) + 1} * ns + q)"]
  for i in [0:k.ops.size] do
    ls := ls ++ [s!"  let {name (nIn + i)} := {k.ops[i]!.toLean name}"]
  for r in [0:R] do
    let pos := if twd then s!"2 * (c + {r} * ns)" else s!"2 * (dst + {r} * dstr)"
    ls := ls ++ [s!"  let y := wr y ({pos}) {name k.outs[2 * r]!}",
                 s!"  let y := wr y ({pos} + 1) {name k.outs[2 * r + 1]!}"]
  ls := ls ++ ["  y", ""]
  return joinLines ls

/-- A twiddled butterfly of radix `R`, out of place (the Stockham schedule): reads
`x[src + r·sstr]` and the twiddles of column `k` of `tw` (rows of length `ns`), and writes
output `r` to `y[dst + r·dstr]`. -/
def emitLeanBflyS (R : Nat) (fwd : Bool) : String := Id.run do
  let k := butterflyK fwd R true
  let nIn := k.nIn
  let name (i : Nat) : String := if i < nIn then s!"i{i}" else s!"t{i}"
  let mut ls : List String := [
    s!"@[inline] unsafe def bfly{R}s{if fwd then "f" else "b"} (x tw : @& FloatArray) (y : FloatArray) (src sstr dst dstr ns k : USize) : FloatArray :="]
  for r in [0:R] do
    ls := ls ++ [s!"  let i{2 * r} := rd x (2 * (src + {r} * sstr))",
                 s!"  let i{2 * r + 1} := rd x (2 * (src + {r} * sstr) + 1)"]
  for r in [1:R] do
    ls := ls ++ [s!"  let i{2 * R + 2 * (r - 1)} := rd tw ({2 * (r - 1)} * ns + k)",
                 s!"  let i{2 * R + 2 * (r - 1) + 1} := rd tw ({2 * (r - 1) + 1} * ns + k)"]
  for i in [0:k.ops.size] do
    ls := ls ++ [s!"  let {name (nIn + i)} := {k.ops[i]!.toLean name}"]
  for r in [0:R] do
    let pos := s!"2 * (dst + {r} * dstr)"
    ls := ls ++ [s!"  let y := wr y ({pos}) {name k.outs[2 * r]!}",
                 s!"  let y := wr y ({pos} + 1) {name k.outs[2 * r + 1]!}"]
  ls := ls ++ ["  y", ""]
  return joinLines ls

/-- The loops of the Stockham schedule for radix `R`. Pass `(R, ns)` of size `N` (`m = N/R`):
butterfly `j = b·ns + k` reads `x[j + r·m]` and writes output `r` to `y[b·ns·R + k + r·ns]`.
The first pass (`ns = 1`, untwiddled) loops over `j`; the others loop over `k` inside `b`
when `ns` is large and over `b` inside `k` when it is small, so the inner loop is the long
one. Loads and stores go to different arrays, which the C compiler checks with one range
test per loop before vectorizing it. -/
def emitLeanLoopsS (R : Nat) (fwd : Bool) : String :=
  let d := if fwd then "f" else "b"
  s!"unsafe def stFirst{R}{d} (x : @& FloatArray) (m j : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if j < m then stFirst{R}{d} x m (j + 1) ({leanBflyName R false fwd} x y j m (j * {R}) 1) else y\n\n" ++
  s!"unsafe def stK{R}{d} (x tw : @& FloatArray) (m ns ib ob k : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if k < ns then stK{R}{d} x tw m ns ib ob (k + 1) (bfly{R}s{d} x tw y (ib + k) m (ob + k) ns ns k) else y\n\n" ++
  s!"unsafe def stKB{R}{d} (x tw : @& FloatArray) (m ns nB b : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if b < nB then stKB{R}{d} x tw m ns nB (b + 1) (stK{R}{d} x tw m ns (b * ns) (b * (ns * {R})) 0 y) else y\n\n" ++
  s!"unsafe def stB{R}{d} (x tw : @& FloatArray) (m ns nB k b : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if b < nB then stB{R}{d} x tw m ns nB k (b + 1) (bfly{R}s{d} x tw y (b * ns + k) m (b * (ns * {R}) + k) ns ns k) else y\n\n" ++
  s!"unsafe def stBK{R}{d} (x tw : @& FloatArray) (m ns nB k : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if k < ns then stBK{R}{d} x tw m ns nB (k + 1) (stB{R}{d} x tw m ns nB k 0 y) else y\n\n"

/-- A butterfly of radix `R` on `V` adjacent lanes, on split data (real parts at `[0, h)`,
imaginary parts at `[h, 2h)`): lane `l` reads `x[src + l + r·sstr]` (and, if twiddled, the
twiddles of column `k + l`) and writes output `r` to `y[dst + l + r·dstr]`. The lanes' copies
of each operation are printed next to each other, every lane's loads and stores are
contiguous, and all loads come before all stores, so the C compiler's straight-line (SLP)
vectorizer packs them into `V`-wide vector instructions with no alias checks. -/
def emitLeanBflyV (R V : Nat) (twd fwd : Bool) : String := Id.run do
  let k := butterflyK fwd R twd
  let nIn := k.nIn
  let name (i l : Nat) : String := if i < nIn then s!"i{i}_{l}" else s!"t{i}_{l}"
  let nm := s!"bfly{R}{if twd then "t" else "n"}v{V}{if fwd then "f" else "b"}"
  let mut ls : List String := [
    if twd then s!"@[inline] unsafe def {nm} (x tw : @& FloatArray) (y : FloatArray) (h src sstr dst dstr ns k : USize) : FloatArray :="
    else s!"@[inline] unsafe def {nm} (x _tw : @& FloatArray) (y : FloatArray) (h src sstr dst dstr _ns _k : USize) : FloatArray :="]
  for r in [0:R] do
    for l in [0:V] do
      ls := ls ++ [s!"  let i{2 * r}_{l} := rd x (src + {l} + {r} * sstr)"]
    for l in [0:V] do
      ls := ls ++ [s!"  let i{2 * r + 1}_{l} := rd x (h + src + {l} + {r} * sstr)"]
  if twd then
    for r in [1:R] do
      for l in [0:V] do
        ls := ls ++ [s!"  let i{2 * R + 2 * (r - 1)}_{l} := rd tw ({2 * (r - 1)} * ns + k + {l})"]
      for l in [0:V] do
        ls := ls ++ [s!"  let i{2 * R + 2 * (r - 1) + 1}_{l} := rd tw ({2 * (r - 1) + 1} * ns + k + {l})"]
  for i in [0:k.ops.size] do
    for l in [0:V] do
      ls := ls ++ [s!"  let {name (nIn + i) l} := {k.ops[i]!.toLean (name · l)}"]
  for r in [0:R] do
    for l in [0:V] do
      ls := ls ++ [s!"  let y := wr y (dst + {l} + {r} * dstr) {name k.outs[2 * r]! l}"]
    for l in [0:V] do
      ls := ls ++ [s!"  let y := wr y (h + dst + {l} + {r} * dstr) {name k.outs[2 * r + 1]! l}"]
  ls := ls ++ ["  y", ""]
  return joinLines ls

/-- Loops of the split-format Stockham schedule for radix `R`, lanes `V`. -/
def emitLeanLoopsV (R V : Nat) (fwd : Bool) : String :=
  let d := if fwd then "f" else "b"
  s!"unsafe def svFirst{R}{d} (x : @& FloatArray) (h m j : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if j < m then svFirst{R}{d} x h m (j + 1) (bfly{R}nv1{d} x x y h j m (j * {R}) 1 0 0) else y\n\n" ++
  s!"unsafe def svK{R}{d} (x tw : @& FloatArray) (h m ns ib ob k : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if k < ns then svK{R}{d} x tw h m ns ib ob (k + {V}) (bfly{R}tv{V}{d} x tw y h (ib + k) m (ob + k) ns ns k) else y\n\n" ++
  s!"unsafe def svKB{R}{d} (x tw : @& FloatArray) (h m ns nB b : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if b < nB then svKB{R}{d} x tw h m ns nB (b + 1) (svK{R}{d} x tw h m ns (b * ns) (b * (ns * {R})) 0 y) else y\n\n" ++
  s!"unsafe def sv1K{R}{d} (x tw : @& FloatArray) (h m ns ib ob k : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if k < ns then sv1K{R}{d} x tw h m ns ib ob (k + 1) (bfly{R}tv1{d} x tw y h (ib + k) m (ob + k) ns ns k) else y\n\n" ++
  s!"unsafe def sv1KB{R}{d} (x tw : @& FloatArray) (h m ns nB b : USize) (y : FloatArray) : FloatArray :=\n" ++
  s!"  if b < nB then sv1KB{R}{d} x tw h m ns nB (b + 1) (sv1K{R}{d} x tw h m ns (b * ns) (b * (ns * {R})) 0 y) else y\n\n"

/-- Lanes of the split-format kernels. -/
def leanLanes : Nat := 4

/-- The radices of the Lean backend. -/
def leanRadices : List Nat := [2, 4, 8, 16]

/-- The generated module `LeanFFTW/Native/Kernels.lean`. -/
def emitLeanKernels : String := Id.run do
  let mut out := "/- Generated by scripts/GenLeanKernels.lean from the kernels of LeanFFTW.Gen.Stockham.\n" ++
    "   Do not edit. -/\nimport LeanFFTW.Native.Prim\n\nset_option maxRecDepth 100000\n\nnamespace LeanFFTW.Native\n\n"
  for fwd in [true, false] do
    for twd in [false, true] do
      for R in leanRadices do
        out := out ++ emitLeanBfly R twd fwd
    for R in leanRadices do
      out := out ++ emitLeanBflyS R fwd
    for R in leanRadices do
      out := out ++ emitLeanBflyV R 1 false fwd ++ emitLeanBflyV R 1 true fwd ++
        emitLeanBflyV R leanLanes true fwd
  -- one loop per radix, with the butterfly inlined into it
  for fwd in [true, false] do
    let d := if fwd then "f" else "b"
    for R in leanRadices do
      out := out ++ s!"/-- Leaf pass, radix {R}: leaf `j < n` reads `x[j + i·sstr]` and writes at `ofs[j]`. -/\n" ++
        s!"unsafe def leafLoop{R}{d} (x ofs : @& FloatArray) (sstr n j : USize) (y : FloatArray) : FloatArray :=\n" ++
        s!"  if j < n then\n    leafLoop{R}{d} x ofs sstr n (j + 1) ({leanBflyName R false fwd} x y j sstr (rd ofs j).toUSize 1)\n" ++
        "  else y\n\n"
      out := out ++ s!"/-- Butterflies `q < ns` of one block of an in-place pass, radix {R}, at `c + q`. -/\n" ++
        s!"unsafe def ditCol{R}{d} (tw : @& FloatArray) (ns c q : USize) (y : FloatArray) : FloatArray :=\n" ++
        s!"  if q < ns then ditCol{R}{d} tw ns c (q + 1) ({leanBflyName R true fwd} tw y (c + q) ns q) else y\n\n"
      out := out ++ s!"/-- In-place pass, radix {R}: blocks `b < nB` of `ns·{R}` points. -/\n" ++
        s!"unsafe def ditLoop{R}{d} (tw : @& FloatArray) (ns nB b : USize) (y : FloatArray) : FloatArray :=\n" ++
        s!"  if b < nB then ditLoop{R}{d} tw ns nB (b + 1) (ditCol{R}{d} tw ns (b * (ns * {R})) 0 y) else y\n\n"
    out := out ++ s!"unsafe def leafPass{d} (R : Nat) (x ofs : @& FloatArray) (sstr n : USize) (y : FloatArray) : FloatArray :=\n  match R with\n"
    for R in leanRadices do
      out := out ++ s!"  | {R} => leafLoop{R}{d} x ofs sstr n 0 y\n"
    out := out ++ "  | _ => y\n\n"
    out := out ++ s!"unsafe def ditPass{d} (R : Nat) (tw : @& FloatArray) (ns nB : USize) (y : FloatArray) : FloatArray :=\n  match R with\n"
    for R in leanRadices do
      out := out ++ s!"  | {R} => ditLoop{R}{d} tw ns nB 0 y\n"
    out := out ++ "  | _ => y\n\n"
  -- the Stockham schedule
  for fwd in [true, false] do
    let d := if fwd then "f" else "b"
    for R in leanRadices do
      out := out ++ emitLeanLoopsS R fwd
    out := out ++ s!"/-- One Stockham pass `(R, ns)`, from `x` into `y`; `bInner` puts the loop over blocks inside. -/\n" ++
      s!"unsafe def stPass{d} (R : Nat) (x tw : @& FloatArray) (m ns nB : USize) (bInner : Bool) (y : FloatArray) : FloatArray :=\n  match R with\n"
    for R in leanRadices do
      out := out ++ s!"  | {R} => if ns == 1 then stFirst{R}{d} x m 0 y else if bInner then stBK{R}{d} x tw m ns nB 0 y else stKB{R}{d} x tw m ns nB 0 y\n"
    out := out ++ "  | _ => y\n\n"
  -- the split-format Stockham schedule
  for fwd in [true, false] do
    let d := if fwd then "f" else "b"
    for R in leanRadices do
      out := out ++ emitLeanLoopsV R leanLanes fwd
    out := out ++ s!"/-- One pass of the split-format Stockham schedule, from `x` into `y`. -/\n" ++
      s!"unsafe def svPass{d} (R : Nat) (x tw : @& FloatArray) (h m ns nB : USize) (y : FloatArray) : FloatArray :=\n  match R with\n"
    for R in leanRadices do
      out := out ++ s!"  | {R} => if ns == 1 then svFirst{R}{d} x h m 0 y else if ns < {leanLanes} then sv1KB{R}{d} x tw h m ns nB 0 y else svKB{R}{d} x tw h m ns nB 0 y\n"
    out := out ++ "  | _ => y\n\n"
  out := out ++ s!"/-- `#V` lanes, as the split kernels use. -/\ndef lanes : Nat := {leanLanes}\n\n"
  return out ++ "end LeanFFTW.Native\n"

end LeanFFTW.Gen
