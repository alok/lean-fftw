/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Emit
import LeanFFTW.Core.FloatOps
import LeanFFTW.Core.FastPlan

/-!
# The fast engine: vectorized Stockham passes, generated from the generic algorithms

A transform of size `N = R₀ ⋯ R_{s-1}` runs `s` radix-`R` passes (Stockham autosort,
decimation in time). Pass `t` has `ns = R₀ ⋯ R_{t-1}` and, for every `j < N/R` with
`k = j mod ns`, `b = j / ns`,

```
v[r]  = in[j + r·N/R] · ω_{ns·R}^{r·k}        (r < R)
out[b·ns·R + k + r·ns] = (DFT_R v)[r]
```

The butterfly `DFT_R ∘ diag(ω)` is produced by running the proved generic `exec`/`mkPlan`
on symbolic inputs (`symOps`), so its straight-line code is a CSE'd image of the verified
algorithm. Passes are vectorized over `VL` consecutive `j` (one butterfly per lane) in
split real/imaginary format: lane-wise SIMD arithmetic performs, in every lane, exactly the
scalar operations of the kernel. The first pass reads FFTW's interleaved input,
deinterleaves it, and transposes `VL × VL` blocks (its outputs `out[j·R + r]` are strided
across lanes because `ns = 1`); the last pass writes interleaved output.

Pure data movement (loads, stores, deinterleave, transpose, interleave) is printed from the
templates below; these templates are the trusted part of the fast engine and are validated
bit for bit against `refTransform` (the same passes evaluated in Lean `Float`).
-/

namespace LeanFFTW.Gen

open LeanFFTW

/-! ## Butterflies -/

/-- The symbolic butterfly of a pass: inputs `x_r` (`r < R`, variables `2r, 2r+1`) and, when
`twiddled`, twiddles `w_r` (`1 ≤ r < R`, variables `2R + 2(r-1)`, `+1`). Returns the `2R`
output expressions `re y_0, im y_0, …`. -/
def butterfly (fwd : Bool) (R : Nat) (twiddled : Bool) : Array SExpr :=
  let x : Nat → SC := fun r =>
    let xr : SC := .val (.input (2 * r)) (.input (2 * r + 1))
    if twiddled && r ≥ 1 then
      SC.mulGen (.val (.input (2 * R + 2 * (r - 1))) (.input (2 * R + 2 * (r - 1) + 1))) xr
    else xr
  let y := exec symOps (mkPlan symOps fwd (primeFactors R)) x
  (Array.range R).foldl (fun acc k =>
    let (re, im) := (symOps.get y k).parts; (acc.push re).push im) #[]

/-- Input variable names of generated code. -/
def vName (i : Nat) : String := s!"v{i}"

/-- The CSE'd SSA of a butterfly. -/
def butterflySSA (fwd : Bool) (R : Nat) (twiddled : Bool) : SSA :=
  toSSA vName (butterfly fwd R twiddled)

/-! ## Fast evaluation of SSA code in Lean `Float` -/

/-- SSA with operands resolved to slots: slots `0 … nIn-1` are the inputs, slot
`nIn + i` is the result of instruction `i`. -/
inductive IOp where
  | cst (v : Float)
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  | fma (a b c : Nat)
  | fms (a b c : Nat)
  | fnma (a b c : Nat)
  deriving Inhabited

structure ISSA where
  nIn : Nat
  ops : Array IOp
  outs : Array Nat
  deriving Inhabited

/-- Resolve names to slots (inputs are named `vName i`, `i < nIn`). -/
def SSA.index (k : SSA) (nIn : Nat) : ISSA := Id.run do
  let mut slot : Std.HashMap String Nat := {}
  for i in [0:nIn] do
    slot := slot.insert (vName i) i
  let mut ops : Array IOp := #[]
  for ins in k.code do
    let s (v : String) : Nat := slot.getD v 0
    let (d, op) : String × IOp := match ins with
      | .cst d c => (d, .cst c.toFloat)
      | .zero d => (d, .cst 0.0)
      | .add d a b => (d, .add (s a) (s b))
      | .sub d a b => (d, .sub (s a) (s b))
      | .mul d a b => (d, .mul (s a) (s b))
      | .neg d a => (d, .neg (s a))
      | .fma d a b c => (d, .fma (s a) (s b) (s c))
      | .fms d a b c => (d, .fms (s a) (s b) (s c))
      | .fnma d a b c => (d, .fnma (s a) (s b) (s c))
    slot := slot.insert d (nIn + ops.size)
    ops := ops.push op
  return ⟨nIn, ops, k.outs.map fun v => slot.getD v 0⟩

/-- Binary64 evaluation; the operations are those of `SSA.evalF` / `SExpr.evalF`. -/
def ISSA.eval (k : ISSA) (inp : FloatArray) : FloatArray := Id.run do
  let mut env := inp
  for op in k.ops do
    let g (i : Nat) : Float := env[i]!
    let v := match op with
      | .cst v => v
      | .add a b => g a + g b
      | .sub a b => g a - g b
      | .mul a b => g a * g b
      | .neg a => -(g a)
      | .fma a b c => Float.fma (g a) (g b) (g c)
      | .fms a b c => Float.fma (g a) (g b) (-(g c))
      | .fnma a b c => Float.fma (-(g a)) (g b) (g c)
    env := env.push v
  let mut out := FloatArray.emptyWithCapacity k.outs.size
  for o in k.outs do
    out := out.push env[o]!
  return out

/-! ## Reference semantics in Lean `Float` (what the C engine must reproduce bit for bit) -/

/-- One Stockham pass on split arrays (`re`, `im` of length `N`). `tw` is the pass's
twiddle table (`passTwiddles`), or `none` for an untwiddled pass. -/
def refPass (k : ISSA) (R ns N : Nat) (tw : Option FloatArray) (re im : FloatArray) :
    FloatArray × FloatArray := Id.run do
  let NR := N / R
  let mut ore := FloatArray.mk (Array.replicate N 0.0)
  let mut oim := FloatArray.mk (Array.replicate N 0.0)
  for j in [0:NR] do
    let kk := j % ns
    let b := j / ns
    let mut inp := FloatArray.emptyWithCapacity (4 * R)
    for r in [0:R] do
      inp := (inp.push re[j + r * NR]!).push im[j + r * NR]!
    if let some t := tw then
      for r in [1:R] do
        inp := (inp.push t[2 * (r - 1) * ns + kk]!).push t[(2 * (r - 1) + 1) * ns + kk]!
    let y := k.eval inp
    for r in [0:R] do
      ore := ore.set! (b * ns * R + kk + r * ns) y[2 * r]!
      oim := oim.set! (b * ns * R + kk + r * ns) y[2 * r + 1]!
  return (ore, oim)

/-- The reference transform of a fast plan on interleaved data. A single radix (`s = 1`,
the small codelets) is one untwiddled pass with `ns = 1`. -/
def refTransform (fwd : Bool) (N : Nat) (rs : Array Nat) (inp : FloatArray) : FloatArray :=
  Id.run do
    let tab := Trig.cosSin2PiTable N
    let mut re := FloatArray.mk ((Array.range N).map fun i => inp[2 * i]!)
    let mut im := FloatArray.mk ((Array.range N).map fun i => inp[2 * i + 1]!)
    for t in [0:rs.size] do
      let R := rs.getD t 1
      let ns := passNs rs t
      let k := (butterflySSA fwd R (t ≥ 1)).index (if t ≥ 1 then 4 * R - 2 else 2 * R)
      let tw := if t ≥ 1 then some (passTwiddles tab fwd N R ns) else none
      (re, im) := refPass k R ns N tw re im
    let mut out := FloatArray.emptyWithCapacity (2 * N)
    for i in [0:N] do
      out := (out.push re[i]!).push im[i]!
    return out

/-- C entry point for differential tests: `spec = [N, fwd, s, R₀, …]`. -/
@[export lfftw_fast_reference]
def fastReferenceFFI (spec : FloatArray) (inp : FloatArray) : FloatArray :=
  let (N, fwd, rs) := decodeFastSpec spec
  refTransform fwd N rs inp

/-! ## C templates -/

def dirTag (fwd : Bool) : String := if fwd then "f" else "b"

def firstName (R vl : Nat) (fwd : Bool) : String := s!"lf_first_r{R}_v{vl}_{dirTag fwd}"
def midName (R vl : Nat) (fwd : Bool) : String := s!"lf_mid_r{R}_v{vl}_{dirTag fwd}"
def lastName (R vl : Nat) (fwd : Bool) : String := s!"lf_last_r{R}_v{vl}_{dirTag fwd}"
def smallName (N : Nat) (fwd : Bool) : String := s!"lf_small_n{N}_{dirTag fwd}"

/-- Body lines of SSA code. -/
def SSA.bodyLines (k : SSA) (t : Target) (ind : String) : List String :=
  k.code.toList.map fun i => ind ++ i.toC t

def joinLines (ls : List String) : String := String.join (ls.map (· ++ "\n"))

/-- Index vector constant for `_mm512_permutex2var_pd`. -/
def idx8 (l : List Nat) : String :=
  "_mm512_setr_epi64(" ++ ", ".intercalate (l.map toString) ++ ")"

/-- Data-movement helpers: deinterleave (`dre`, `dim`), interleave (`ilo`, `ihi`), and the
two halves `tA_h`, `tB_h` of the transpose stage that exchanges bit `h` of the row and
column index: `tA_h(a,b)[l] = (l&h)=0 ? a[l] : b[l-h]`, `tB_h(a,b)[l] = (l&h)=0 ? a[l+h] : b[l]`. -/
def prelude : String :=
  let st (h : Nat) (A : Bool) : List Nat := (List.range 8).map fun l =>
    if l &&& h == 0 then (if A then l else l + h) else (if A then 8 + l - h else 8 + l)
  let t8 := [4, 2, 1].map fun h =>
    s!"static inline __m512d lf8_tA{h}(__m512d a, __m512d b) " ++
      s!"\{ return _mm512_permutex2var_pd(a, {idx8 (st h true)}, b); }\n" ++
    s!"static inline __m512d lf8_tB{h}(__m512d a, __m512d b) " ++
      s!"\{ return _mm512_permutex2var_pd(a, {idx8 (st h false)}, b); }"
  joinLines ([
    "#include <immintrin.h>",
    "#include <stddef.h>",
    "#include <math.h>",
    "",
    "static inline __m512d lf8_dre(__m512d a, __m512d b) " ++
      s!"\{ return _mm512_permutex2var_pd(a, {idx8 [0,2,4,6,8,10,12,14]}, b); }",
    "static inline __m512d lf8_dim(__m512d a, __m512d b) " ++
      s!"\{ return _mm512_permutex2var_pd(a, {idx8 [1,3,5,7,9,11,13,15]}, b); }",
    "static inline __m512d lf8_ilo(__m512d re, __m512d im) " ++
      s!"\{ return _mm512_permutex2var_pd(re, {idx8 [0,8,1,9,2,10,3,11]}, im); }",
    "static inline __m512d lf8_ihi(__m512d re, __m512d im) " ++
      s!"\{ return _mm512_permutex2var_pd(re, {idx8 [4,12,5,13,6,14,7,15]}, im); }"] ++ t8 ++ [
    "static inline __m256d lf4_dre(__m256d a, __m256d b) " ++
      "{ return _mm256_permute4x64_pd(_mm256_unpacklo_pd(a, b), 0xD8); }",
    "static inline __m256d lf4_dim(__m256d a, __m256d b) " ++
      "{ return _mm256_permute4x64_pd(_mm256_unpackhi_pd(a, b), 0xD8); }",
    "static inline __m256d lf4_ilo(__m256d re, __m256d im) " ++
      "{ return _mm256_permute2f128_pd(_mm256_unpacklo_pd(re, im), _mm256_unpackhi_pd(re, im), 0x20); }",
    "static inline __m256d lf4_ihi(__m256d re, __m256d im) " ++
      "{ return _mm256_permute2f128_pd(_mm256_unpacklo_pd(re, im), _mm256_unpackhi_pd(re, im), 0x31); }",
    "static inline __m256d lf4_tA2(__m256d a, __m256d b) { return _mm256_permute2f128_pd(a, b, 0x20); }",
    "static inline __m256d lf4_tB2(__m256d a, __m256d b) { return _mm256_permute2f128_pd(a, b, 0x31); }",
    "static inline __m256d lf4_tA1(__m256d a, __m256d b) { return _mm256_unpacklo_pd(a, b); }",
    "static inline __m256d lf4_tB1(__m256d a, __m256d b) { return _mm256_unpackhi_pd(a, b); }",
    ""])

def targetOf (vl : Nat) : Target := if vl == 8 then .avx512 else .avx2

/-- Transpose the `VL × VL` block whose rows are `rows`; returns declarations and the
names of the transposed rows. -/
def transposeC (t : Target) (tag : String) (rows : Array String) : List String × Array String :=
  Id.run do
    let vl := t.vl
    let hs := if vl == 8 then [4, 2, 1] else [2, 1]
    let mut cur := rows
    let mut decls : List String := []
    for h in hs do
      let mut nxt := cur
      for i in [0:vl] do
        if i &&& h == 0 then
          let a := s!"{tag}_{h}_{i}"
          let b := s!"{tag}_{h}_{i + h}"
          decls := decls ++ [
            s!"    const {t.ty} {a} = lf{vl}_tA{h}({cur[i]!}, {cur[i + h]!});",
            s!"    const {t.ty} {b} = lf{vl}_tB{h}({cur[i]!}, {cur[i + h]!});"]
          nxt := (nxt.set! i a).set! (i + h) b
      cur := nxt
    return (decls, cur)

def indent (n : Nat) (s : String) : String :=
  String.join ((s.splitOn "\n").filter (· ≠ "") |>.map fun l => String.ofList (List.replicate n ' ') ++ l ++ "\n")

/-- First pass (`ns = 1`, untwiddled): interleaved `in` → split `ore`, `oim`. Requires
`VL ∣ R` and `VL ∣ N/R`. -/
def emitFirst (R vl : Nat) (fwd : Bool) : String := Id.run do
  let t := targetOf vl
  let ty := t.ty
  let p := t.pre
  let k := butterflySSA fwd R false
  let mut ls : List String := [
    s!"static void {firstName R vl fwd}(const double *restrict in, double *restrict ore, double *restrict oim, size_t N) \{",
    s!"  const size_t NR = N / {R};",
    s!"  for (size_t j = 0; j < NR; j += {vl}) \{"]
  for r in [0:R] do
    ls := ls ++ [
      s!"    const {ty} la{r} = {p}_loadu_pd(in + 2 * (j + {r} * NR));",
      s!"    const {ty} lb{r} = {p}_loadu_pd(in + 2 * (j + {r} * NR) + {vl});",
      s!"    const {ty} {vName (2 * r)} = lf{vl}_dre(la{r}, lb{r});",
      s!"    const {ty} {vName (2 * r + 1)} = lf{vl}_dim(la{r}, lb{r});"]
  ls := ls ++ k.bodyLines t "    "
  for (part, base) in [(0, "ore"), (1, "oim")] do
    for c in [0:R / vl] do
      let rows := (Array.range vl).map fun i => k.outs[2 * (c * vl + i) + part]!
      let (decls, cols) := transposeC t s!"q{part}_{c}" rows
      ls := ls ++ decls
      for l in [0:vl] do
        ls := ls ++ [s!"    {p}_storeu_pd({base} + (j + {l}) * {R} + {c * vl}, {cols[l]!});"]
  ls := ls ++ ["  }", "}", ""]
  return joinLines ls

/-- Shared body of twiddled passes: loads from split `ire`, `iim` and the twiddle table. -/
def twiddledLoads (R vl : Nat) : List String := Id.run do
  let t := targetOf vl
  let mut ls : List String := []
  for r in [0:R] do
    ls := ls ++ [
      s!"      const {t.ty} {vName (2 * r)} = {t.pre}_loadu_pd(ire + j + {r} * NR);",
      s!"      const {t.ty} {vName (2 * r + 1)} = {t.pre}_loadu_pd(iim + j + {r} * NR);"]
  for r in [1:R] do
    ls := ls ++ [
      s!"      const {t.ty} {vName (2 * R + 2 * (r - 1))} = {t.pre}_loadu_pd(tw + {2 * (r - 1)} * ns + k);",
      s!"      const {t.ty} {vName (2 * R + 2 * (r - 1) + 1)} = {t.pre}_loadu_pd(tw + {2 * (r - 1) + 1} * ns + k);"]
  return ls

/-- Middle pass: split → split, twiddled. Requires `VL ∣ ns`. -/
def emitMid (R vl : Nat) (fwd : Bool) : String := Id.run do
  let t := targetOf vl
  let k := butterflySSA fwd R true
  let mut ls : List String := [
    s!"static void {midName R vl fwd}(const double *restrict ire, const double *restrict iim, double *restrict ore, double *restrict oim, const double *restrict tw, size_t N, size_t ns) \{",
    s!"  const size_t NR = N / {R};",
    "  for (size_t b = 0; b < NR; b += ns) {",
    s!"    for (size_t k = 0; k < ns; k += {vl}) \{",
    "      const size_t j = b + k;",
    s!"      const size_t o = b * {R} + k;"]
  ls := ls ++ twiddledLoads R vl
  ls := ls ++ k.bodyLines t "      "
  for r in [0:R] do
    ls := ls ++ [
      s!"      {t.pre}_storeu_pd(ore + o + {r} * ns, {k.outs[2 * r]!});",
      s!"      {t.pre}_storeu_pd(oim + o + {r} * ns, {k.outs[2 * r + 1]!});"]
  ls := ls ++ ["    }", "  }", "}", ""]
  return joinLines ls

/-- Last pass: split → interleaved `out`, twiddled. Requires `VL ∣ ns`. -/
def emitLast (R vl : Nat) (fwd : Bool) : String := Id.run do
  let t := targetOf vl
  let k := butterflySSA fwd R true
  let mut ls : List String := [
    s!"static void {lastName R vl fwd}(const double *restrict ire, const double *restrict iim, double *restrict out, const double *restrict tw, size_t N, size_t ns) \{",
    s!"  const size_t NR = N / {R};",
    "  for (size_t b = 0; b < NR; b += ns) {",
    s!"    for (size_t k = 0; k < ns; k += {vl}) \{",
    "      const size_t j = b + k;",
    s!"      const size_t o = b * {R} + k;"]
  ls := ls ++ twiddledLoads R vl
  ls := ls ++ k.bodyLines t "      "
  for r in [0:R] do
    ls := ls ++ [
      s!"      {t.pre}_storeu_pd(out + 2 * (o + {r} * ns), lf{vl}_ilo({k.outs[2 * r]!}, {k.outs[2 * r + 1]!}));",
      s!"      {t.pre}_storeu_pd(out + 2 * (o + {r} * ns) + {vl}, lf{vl}_ihi({k.outs[2 * r]!}, {k.outs[2 * r + 1]!}));"]
  ls := ls ++ ["    }", "  }", "}", ""]
  return joinLines ls

/-- A whole small transform (one untwiddled butterfly, scalar), interleaved → interleaved.
All inputs are read before any output is written, so `in == out` is allowed. -/
def emitSmall (N : Nat) (fwd : Bool) : String := Id.run do
  let k := butterflySSA fwd N false
  let mut ls : List String := [
    s!"static void {smallName N fwd}(const double *in, double *out) \{"]
  for i in [0:2 * N] do
    ls := ls ++ [s!"  const double {vName i} = in[{i}];"]
  ls := ls ++ k.bodyLines .scalar "  "
  for i in [0:2 * N] do
    ls := ls ++ [s!"  out[{i}] = {k.outs[i]!};"]
  ls := ls ++ ["}", ""]
  return joinLines ls

/-- The kernel set of the fast engine. -/
structure KernelSet where
  /-- `(R, VL)` of first passes -/
  first : List (Nat × Nat)
  /-- `(R, VL)` of middle and last passes -/
  mid : List (Nat × Nat)
  /-- sizes of the scalar small transforms -/
  small : List Nat

def KernelSet.default : KernelSet where
  first := [(4, 4), (8, 4), (16, 4), (8, 8), (16, 8), (32, 8)]
  mid := [(2, 4), (4, 4), (8, 4), (2, 8), (4, 8), (8, 8), (16, 8), (32, 8)]
  small := [2, 4, 8]

/-- The whole generated C translation unit: kernels plus lookup functions. -/
def emitKernels (ks : KernelSet := .default) : String := Id.run do
  let mut s := "/* Generated by LeanFFTW.Gen.Stockham (Lean). Do not edit. */\n" ++ prelude
  let dirs := [true, false]
  for fwd in dirs do
    for (R, vl) in ks.first do s := s ++ emitFirst R vl fwd
    for (R, vl) in ks.mid do s := s ++ emitMid R vl fwd ++ emitLast R vl fwd
    for N in ks.small do s := s ++ emitSmall N fwd
  s := s ++ "#include \"lf_kernels.h\"\n\n"
  let look (ty fn : String) (xs : List (Nat × Nat)) (nm : Nat → Nat → Bool → String) : String :=
    joinLines ([s!"{ty} {fn}(int R, int vl, int fwd) \{"] ++
      (dirs.flatMap fun fwd => xs.map fun (R, vl) =>
        s!"  if (R == {R} && vl == {vl} && fwd == {if fwd then 1 else 0}) return {nm R vl fwd};") ++
      ["  return 0;", "}", ""])
  s := s ++ look "lf_first_fn" "lf_get_first" ks.first firstName
  s := s ++ look "lf_mid_fn" "lf_get_mid" ks.mid midName
  s := s ++ look "lf_last_fn" "lf_get_last" ks.mid lastName
  s := s ++ joinLines (["lf_small_fn lf_get_small(int N, int fwd) {"] ++
      (dirs.flatMap fun fwd => ks.small.map fun N =>
        s!"  if (N == {N} && fwd == {if fwd then 1 else 0}) return {smallName N fwd};") ++
      ["  return 0;", "}", ""])
  return s

end LeanFFTW.Gen
