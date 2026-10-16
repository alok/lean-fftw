/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Stockham

/-!
# Interleaved-complex vectorization of kernels

For small transforms the data stays in FFTW's interleaved layout (`re, im, re, im, …`): a
vector holds `VLc` complex numbers, and each operation of a kernel whose inputs and outputs
come in `(re, im)` pairs is executed on the real and imaginary lanes of every complex
number at once.

`vpair s₁ s₂` produces a vector whose low lane (of every complex number) holds kernel slot
`s₁` and whose high lane holds slot `s₂`. Each vector operation is chosen so that **in each
lane it performs exactly the kernel operation of that lane's slot**, operand for operand:

* `add`, `sub`, `mul`, `neg` (sign flip by `xor`) and the fused forms, lane-wise;
* mixed lanes: `fmaddsub(a, b, c)` is `a·b − c` in the low lane and `a·b + c` in the high
  lane, `fmsubadd` the reverse, each with one rounding; with `b = 1` they compute
  `a − c`, `a + c` exactly as `sub`, `add` do (the product by one is exact). A product
  whose sign differs between lanes negates one lane of a factor first (exact);
* data movement only otherwise (`shuffle_pd`, constants, loads and stores).

Commutative operands (`a + b`, `a · b`, and the factors of fused forms) may be taken in
either order; binary64 addition and multiplication are commutative, so lane values equal
`Kernel.eval floatArith` bit for bit. A pair that matches no vector operation is assembled
from two vectors by a shuffle. This is part of the trusted printing step (docs/TRUST.md),
checked by the bit-exact differential test.
-/

namespace LeanFFTW.Gen

open Std

/-- Vector type for `VLc` complex numbers (`VLc = 2`: AVX2 `__m256d`; `VLc = 4`: AVX-512). -/
structure CTarget where
  vlc : Nat

def CTarget.ty (t : CTarget) : String := if t.vlc == 4 then "__m512d" else "__m256d"
def CTarget.pre (t : CTarget) : String := if t.vlc == 4 then "_mm512" else "_mm256"

/-- A constant vector with lanes `lo, hi` in every complex number. -/
def CTarget.setPair (t : CTarget) (lo hi : String) : String :=
  let ls := String.intercalate ", " ((List.range t.vlc).flatMap fun _ => [lo, hi])
  s!"{t.pre}_setr_pd({ls})"

/-- `shuffle_pd(a, b)` with low lane `a[ia]`, high lane `b[ib]` in every complex number. -/
def CTarget.shuffle (t : CTarget) (a b : String) (ia ib : Nat) : String :=
  let s := ia + 2 * ib
  let imm := (List.range t.vlc).foldl (fun acc i => acc + s * 4 ^ i) 0
  s!"{t.pre}_shuffle_pd({a}, {b}, {imm})"

/-- A C literal denoting exactly the binary64 value `x` (finite). -/
def floatCLit (x : Float) : String :=
  let b := x.toBits
  let sign := if b >>> 63 == 1 then "-" else ""
  let frac := b &&& 0xFFFFFFFFFFFFF
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let hex := String.ofList ((Nat.toDigits 16 frac.toNat).leftpad 13 '0')
  if e == 0 then (if frac == 0 then s!"{sign}0.0" else s!"{sign}0x0.{hex}p-1022")
  else s!"{sign}0x1.{hex}p{(e : Int) - 1023}"

structure VState where
  lines : Array String := #[]
  memo : HashMap (Nat × Nat) String := {}
  /-- where a slot is available: vector name and lane (0 = low, 1 = high) -/
  loc : HashMap Nat (String × Nat) := {}
  cnt : Nat := 0

abbrev VM := StateM VState

structure VCtx where
  t : CTarget
  k : Kernel
  pfx : String
  ind : String

def VCtx.op (c : VCtx) (s : Nat) : Option KOp :=
  if s < c.k.nIn then none else c.k.ops[s - c.k.nIn]?

/-- Emit a new vector variable defined by `rhs`; it holds slots `s₁` (low) and `s₂` (high). -/
def VCtx.emit (c : VCtx) (s₁ s₂ : Nat) (rhs : String) : VM String := do
  let st ← get
  let v := s!"{c.pfx}u{st.cnt}"
  let loc := if st.loc.contains s₁ then st.loc else st.loc.insert s₁ (v, 0)
  let loc := if loc.contains s₂ then loc else loc.insert s₂ (v, 1)
  set { st with lines := st.lines.push s!"{c.ind}const {c.t.ty} {v} = {rhs};", cnt := st.cnt + 1,
                memo := st.memo.insert (s₁, s₂) v, loc := loc }
  return v

def VCtx.avail (s₁ s₂ : Nat) : VM Bool := do
  let st ← get
  return st.memo.contains (s₁, s₂) || (st.loc.contains s₁ && st.loc.contains s₂)

inductive FSign where
  | pp | pm | mp
  deriving BEq

/-- Product sign and addend sign of the fused forms: `fma` `+ab+c`, `fms` `+ab−c`,
`fnma` `−ab+c`. -/
def fsign : KOp → Option (Nat × Nat × Nat × Bool × Bool)
  | .fma a b c => some (a, b, c, true, true)
  | .fms a b c => some (a, b, c, true, false)
  | .fnma a b c => some (a, b, c, false, true)
  | _ => none

mutual

/-- A vector holding slot `s₁` in the low lane and `s₂` in the high lane. -/
partial def vpair (c : VCtx) (s₁ s₂ : Nat) : VM String := do
  let st ← get
  if let some v := st.memo[(s₁, s₂)]? then return v
  match st.loc[s₁]?, st.loc[s₂]? with
  | some (v, a), some (w, b) =>
      if v == w && a == 0 && b == 1 then return v
      c.emit s₁ s₂ (c.t.shuffle v w a b)
  | _, _ =>
    match c.op s₁, c.op s₂ with
    | some o₁, some o₂ =>
      match ← vmatch c s₁ s₂ o₁ o₂ with
      | some v => return v
      | none => vsplit c s₁ s₂
    | _, _ => vsplit c s₁ s₂

/-- Fallback: compute each slot in both lanes, then shuffle. -/
partial def vsplit (c : VCtx) (s₁ s₂ : Nat) : VM String := do
  let v ← vpair c s₁ s₁
  let w ← vpair c s₂ s₂
  if v == w then return v
  c.emit s₁ s₂ (c.t.shuffle v w 0 1)

/-- Operand order for a commutative pair of operations. -/
partial def vorder (a₁ b₁ a₂ b₂ : Nat) : VM (Nat × Nat × Nat × Nat) := do
  if (← VCtx.avail a₁ a₂) || (← VCtx.avail b₁ b₂) then return (a₁, a₂, b₁, b₂)
  if (← VCtx.avail a₁ b₂) || (← VCtx.avail b₁ a₂) then return (a₁, b₂, b₁, a₂)
  return (a₁, a₂, b₁, b₂)

/-- A vector operation performing `o₁` in the low lane and `o₂` in the high lane. -/
partial def vmatch (c : VCtx) (s₁ s₂ : Nat) (o₁ o₂ : KOp) : VM (Option String) := do
  let p := c.t.pre
  let one := s!"{p}_set1_pd(1.0)"
  let lit : KOp → Option String
    | .cst k => some k.cLiteral
    | .zero => some "0.0"
    | _ => none
  match o₁, o₂ with
  | .add a₁ b₁, .add a₂ b₂ => do
      let (x₁, x₂, y₁, y₂) ← vorder a₁ b₁ a₂ b₂
      let u ← vpair c x₁ x₂; let v ← vpair c y₁ y₂
      some <$> c.emit s₁ s₂ s!"{p}_add_pd({u}, {v})"
  | .mul a₁ b₁, .mul a₂ b₂ => do
      let (x₁, x₂, y₁, y₂) ← vorder a₁ b₁ a₂ b₂
      let u ← vpair c x₁ x₂; let v ← vpair c y₁ y₂
      some <$> c.emit s₁ s₂ s!"{p}_mul_pd({u}, {v})"
  | .sub a₁ b₁, .sub a₂ b₂ => do
      let u ← vpair c a₁ a₂; let v ← vpair c b₁ b₂
      some <$> c.emit s₁ s₂ s!"{p}_sub_pd({u}, {v})"
  | .sub a₁ b₁, .add a₂ b₂ => do
      -- low a₁ − b₁, high a₂ + b₂ (either order of the sum)
      let (a₂, b₂) := if (← VCtx.avail a₁ b₂) || (← VCtx.avail b₁ a₂) then (b₂, a₂) else (a₂, b₂)
      let u ← vpair c a₁ a₂; let v ← vpair c b₁ b₂
      some <$> c.emit s₁ s₂ s!"{p}_fmaddsub_pd({u}, {one}, {v})"
  | .add a₁ b₁, .sub a₂ b₂ => do
      let (a₁, b₁) := if (← VCtx.avail b₁ a₂) || (← VCtx.avail a₁ b₂) then (b₁, a₁) else (a₁, b₁)
      let u ← vpair c a₁ a₂; let v ← vpair c b₁ b₂
      some <$> c.emit s₁ s₂ s!"{p}_fmsubadd_pd({u}, {one}, {v})"
  | .neg a₁, .neg a₂ => do
      let u ← vpair c a₁ a₂
      some <$> c.emit s₁ s₂ s!"{p}_xor_pd({u}, {p}_set1_pd(-0.0))"
  | _, _ =>
    match lit o₁, lit o₂ with
    | some l₁, some l₂ =>
        if o₁ == .zero && o₂ == .zero then some <$> c.emit s₁ s₂ s!"{p}_setzero_pd()"
        else some <$> c.emit s₁ s₂ (c.t.setPair l₁ l₂)
    | _, _ =>
      match fsign o₁, fsign o₂ with
      | some (a₁, b₁, c₁, sp₁, sc₁), some (a₂, b₂, c₂, sp₂, sc₂) => do
          let (x₁, x₂, y₁, y₂) ← vorder a₁ b₁ a₂ b₂
          let u ← vpair c x₁ x₂; let v ← vpair c y₁ y₂; let w ← vpair c c₁ c₂
          -- make the product signs equal by negating lanes of the first factor (exact)
          let (u, sp) ←
            if sp₁ == sp₂ then pure (u, sp₁)
            else do
              let mask := if sp₁ then c.t.setPair "0.0" "-0.0" else c.t.setPair "-0.0" "0.0"
              let st ← get
              let n := s!"{c.pfx}u{st.cnt}"
              set { st with lines := st.lines.push s!"{c.ind}const {c.t.ty} {n} = {p}_xor_pd({u}, {mask});",
                            cnt := st.cnt + 1 }
              pure (n, true)
          let f := match sp, sc₁, sc₂ with
            | true, true, true => "fmadd"
            | true, false, false => "fmsub"
            | true, false, true => "fmaddsub"
            | true, true, false => "fmsubadd"
            | false, true, true => "fnmadd"
            | false, false, false => "fnmsub"
            | false, _, _ => ""
          if f == "" then
            -- −ab with mixed addend signs: negate the product in both lanes
            let st ← get
            let n := s!"{c.pfx}u{st.cnt}"
            set { st with lines := st.lines.push s!"{c.ind}const {c.t.ty} {n} = {p}_xor_pd({u}, {p}_set1_pd(-0.0));",
                          cnt := st.cnt + 1 }
            let g := if sc₁ then "fmsubadd" else "fmaddsub"
            some <$> c.emit s₁ s₂ s!"{p}_{g}_pd({n}, {v}, {w})"
          else some <$> c.emit s₁ s₂ s!"{p}_{f}_pd({u}, {v}, {w})"
      | _, _ => return none

end

/-- Place a kernel with interleaved vectors: input slot `i` is lane `i % 2` of vector
`bind (i / 2)`. Returns the lines and the output vectors (output pair `r` = slots
`outs[2r], outs[2r+1]`). -/
def Kernel.instC (k : Kernel) (t : CTarget) (ind pfx : String) (bind : Nat → String) :
    Array String × Array String := Id.run do
  let c : VCtx := ⟨t, k, pfx, ind⟩
  let mut st : VState := {}
  for i in [0:k.nIn] do
    st := { st with loc := st.loc.insert i (bind (i / 2), i % 2) }
  let mut outs : Array String := #[]
  for r in [0:k.outs.size / 2] do
    let (v, st') := (vpair c k.outs[2 * r]! k.outs[2 * r + 1]!).run st
    st := st'
    outs := outs.push v
  return (st.lines, outs)

def cfusedName (R1 R2 vlc : Nat) (fwd : Bool) : String := s!"lf_cfused_{R1}x{R2}_c{vlc}_{dirTag fwd}"

/-- Transpose a `VLc × VLc` block of complex numbers (rows are vectors). -/
def ctranspose (t : CTarget) (ind tag : String) (rows : Array String) : List String × Array String :=
  if t.vlc == 2 then
    ([s!"{ind}const __m256d {tag}_0 = _mm256_permute2f128_pd({rows[0]!}, {rows[1]!}, 0x20);",
      s!"{ind}const __m256d {tag}_1 = _mm256_permute2f128_pd({rows[0]!}, {rows[1]!}, 0x31);"],
     #[s!"{tag}_0", s!"{tag}_1"])
  else
    ([s!"{ind}const __m512d {tag}_a0 = _mm512_shuffle_f64x2({rows[0]!}, {rows[1]!}, 0x44);",
      s!"{ind}const __m512d {tag}_a1 = _mm512_shuffle_f64x2({rows[0]!}, {rows[1]!}, 0xEE);",
      s!"{ind}const __m512d {tag}_a2 = _mm512_shuffle_f64x2({rows[2]!}, {rows[3]!}, 0x44);",
      s!"{ind}const __m512d {tag}_a3 = _mm512_shuffle_f64x2({rows[2]!}, {rows[3]!}, 0xEE);",
      s!"{ind}const __m512d {tag}_0 = _mm512_shuffle_f64x2({tag}_a0, {tag}_a2, 0x88);",
      s!"{ind}const __m512d {tag}_1 = _mm512_shuffle_f64x2({tag}_a0, {tag}_a2, 0xDD);",
      s!"{ind}const __m512d {tag}_2 = _mm512_shuffle_f64x2({tag}_a1, {tag}_a3, 0x88);",
      s!"{ind}const __m512d {tag}_3 = _mm512_shuffle_f64x2({tag}_a1, {tag}_a3, 0xDD);"],
     #[s!"{tag}_0", s!"{tag}_1", s!"{tag}_2", s!"{tag}_3"])

/-- The whole transform of size `N = R1·R2` (plan `[R1, R2]`) on interleaved vectors of
`VLc` complex numbers, with the pass-2 twiddles as constants (the values of
`passTwiddles (cosSin2PiTable N) fwd N R2 R1`, exactly). It computes the operations of
`refTransform fwd N #[R1, R2]`. Requires `VLc ∣ R1` and `VLc ∣ R2`. All loads precede all
stores, so `in == out` is allowed. -/
def emitCFused (R1 R2 vlc : Nat) (fwd : Bool) : String := Id.run do
  let t : CTarget := ⟨vlc⟩
  let ty := t.ty
  let p := t.pre
  let N := R1 * R2
  let k1 := butterflyK fwd R1 false
  let k2 := butterflyK fwd R2 true
  let tw := passTwiddles (Trig.cosSin2PiTable N) fwd N R2 R1
  let mut ls : List String := [s!"static void {cfusedName R1 R2 vlc fwd}(const double *in, double *out) \{"]
  -- pass 1: lanes j = jb·VLc + l; input r of butterfly j is in[j + r·R2]
  let mut y : Array (Array String) := #[]
  for jb in [0:R2 / vlc] do
    for r in [0:R1] do
      ls := ls ++ [s!"  const {ty} x{jb}_{r} = {p}_loadu_pd(in + {2 * (jb * vlc + r * R2)});"]
  for jb in [0:R2 / vlc] do
    let (lines, outs) := k1.instC t "  " s!"p{jb}_" fun r => s!"x{jb}_{r}"
    ls := ls ++ lines.toList
    y := y.push outs
  -- pass 2 input r of butterfly k is pass-1 output k of butterfly r
  let mut X : Array (Array String) := Array.replicate (R1 / vlc) (Array.replicate R2 "")
  for kb in [0:R1 / vlc] do
    for rb in [0:R2 / vlc] do
      let rows := (Array.range vlc).map fun l => (y[rb]!)[kb * vlc + l]!
      let (decls, cols) := ctranspose t "  " s!"c{kb}_{rb}" rows
      ls := ls ++ decls
      for m in [0:vlc] do
        X := X.set! kb ((X[kb]!).set! (rb * vlc + m) cols[m]!)
  -- pass 2: lanes k = kb·VLc + l, twiddle (r, k) of the table of pass 1 (ns = R1)
  for kb in [0:R1 / vlc] do
    for r in [1:R2] do
      let lits := (List.range vlc).flatMap fun l =>
        let kk := kb * vlc + l
        [floatCLit tw[2 * (r - 1) * R1 + kk]!, floatCLit tw[(2 * (r - 1) + 1) * R1 + kk]!]
      ls := ls ++ [s!"  const {ty} w{kb}_{r} = {p}_setr_pd({String.intercalate ", " lits});"]
    let bind (i : Nat) : String := if i < R2 then (X[kb]!)[i]! else s!"w{kb}_{i - R2 + 1}"
    let (lines, outs) := k2.instC t "  " s!"q{kb}_" bind
    ls := ls ++ lines.toList
    for r in [0:R2] do
      ls := ls ++ [s!"  {p}_storeu_pd(out + {2 * (kb * vlc + r * R1)}, {outs[r]!});"]
  ls := ls ++ ["}", ""]
  return joinLines ls

end LeanFFTW.Gen

namespace LeanFFTW.Gen

/-- `(R1, R2, VLc)` of the interleaved fused transforms. -/
def cfusedSet : List (Nat × Nat × Nat) :=
  [(2, 2, 2), (2, 4, 2), (4, 2, 2), (4, 4, 2), (4, 4, 4), (4, 8, 4), (8, 4, 4), (8, 8, 4),
   (4, 16, 4), (16, 4, 4), (8, 16, 4), (16, 8, 4)]

/-- The interleaved fused kernels and their lookup function (appended after `emitKernels`). -/
def emitCFusedKernels (xs : List (Nat × Nat × Nat) := cfusedSet) : String := Id.run do
  let mut s := ""
  for fwd in [true, false] do
    for (R1, R2, vlc) in xs do s := s ++ emitCFused R1 R2 vlc fwd
  s := s ++ joinLines (["lf_cfused_fn lf_get_cfused(int R1, int R2, int vlc, int fwd) {"] ++
      ([true, false].flatMap fun fwd => xs.map fun (R1, R2, vlc) =>
        s!"  if (R1 == {R1} && R2 == {R2} && vlc == {vlc} && fwd == {if fwd then 1 else 0}) return {cfusedName R1 R2 vlc fwd};") ++
      ["  return 0;", "}", ""])
  return s

end LeanFFTW.Gen
