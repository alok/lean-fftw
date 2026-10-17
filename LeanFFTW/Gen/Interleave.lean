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
  /-- planned pairs (`slpPairs`): slot ↦ (partner, slot is the low lane) -/
  pp : HashMap Nat (Nat × Bool) := {}

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

/-- The operand pairings a lane-wise vector operation could use for slots `o₁, o₂`
(commutative operands in either order); `none` when no single vector operation applies. -/
def vcands : KOp → KOp → Option (List (List (Nat × Nat)))
  | .add a₁ b₁, .add a₂ b₂ | .mul a₁ b₁, .mul a₂ b₂ =>
      some [[(a₁, a₂), (b₁, b₂)], [(a₁, b₂), (b₁, a₂)]]
  | .sub a₁ b₁, .sub a₂ b₂ => some [[(a₁, a₂), (b₁, b₂)]]
  | .sub a₁ b₁, .add a₂ b₂ => some [[(a₁, a₂), (b₁, b₂)], [(a₁, b₂), (b₁, a₂)]]
  | .add a₁ b₁, .sub a₂ b₂ => some [[(a₁, a₂), (b₁, b₂)], [(b₁, a₂), (a₁, b₂)]]
  | .neg a₁, .neg a₂ => some [[(a₁, a₂)]]
  | o₁, o₂ =>
    match fsign o₁, fsign o₂ with
    | some (a₁, b₁, c₁, _), some (a₂, b₂, c₂, _) =>
        some [[(a₁, a₂), (b₁, b₂), (c₁, c₂)], [(a₁, b₂), (b₁, a₂), (c₁, c₂)]]
    | _, _ => none

/-- Operand slots of an operation. -/
def KOp.args : KOp → List Nat
  | .add a b | .sub a b | .mul a b => [a, b]
  | .neg a => [a]
  | .fma a b c | .fms a b c | .fnma a b c => [a, b, c]
  | _ => []

/-- Bottom-up pairing of kernel slots into vectors (SLP): input `2i` is paired with `2i+1`;
an operation is paired with an unpaired user of a partner of one of its operands when one
lane-wise vector operation computes both, preferring operand pairs that are already planned
(in either lane order; a reversed pair costs a lane exchange). This is only a plan that steers
`vpair`; correctness does not depend on it. -/
def slpPairs (k : Kernel) : HashMap Nat (Nat × Bool) := Id.run do
  let n := k.nIn + k.ops.size
  let op (s : Nat) : Option KOp := if s < k.nIn then none else k.ops[s - k.nIn]?
  let mut users : Array (List Nat) := Array.replicate n []
  for i in [0:k.ops.size] do
    for a in (k.ops[i]!).args do
      if a < n then users := users.set! a ((k.nIn + i) :: users[a]!)
  let mut pp : HashMap Nat (Nat × Bool) := {}
  for i in [0:k.nIn / 2] do
    pp := (pp.insert (2 * i) (2 * i + 1, true)).insert (2 * i + 1) (2 * i, false)
  let isConst (s : Nat) : Bool := match op s with
    | some (.cst _) | some .zero => true
    | _ => false
  for s in [k.nIn:n] do
    if pp.contains s then continue
    let some o := op s | continue
    if isConst s then continue
    -- candidate partners: users of the partners of the operands
    let mut cands : List Nat := []
    for a in o.args do
      if let some (a', _) := pp[a]? then
        for t in users[a']! do
          if t != s && !pp.contains t && !cands.contains t then cands := t :: cands
    let mut best : Option (Nat × Bool × Nat) := none
    for t in cands do
      let some o' := op t | continue
      for lowS in [true, false] do
        let (o₁, o₂) := if lowS then (o, o') else (o', o)
        let some cs := vcands o₁ o₂ | continue
        for cand in cs do
          let mut sc := 0
          for (x, y) in cand do
            sc := sc + (if x == y then 3
              else if isConst x && isConst y then 0
              else match pp[x]? with
                | some (x', true) => if x' == y then 0 else 3
                | some (x', false) => if x' == y then 1 else 3
                | none => 3)
          let better := match best with
            | none => true
            | some (_, _, b) => sc < b
          if better && sc < 3 then best := some (t, lowS, sc)
    if let some (t, lowS, _) := best then
      pp := (pp.insert s (t, lowS)).insert t (s, !lowS)
  return pp

/-- Estimated number of vector operations still needed to build the pair `(s₁, s₂)` in the
current state, looking `d` levels down (tree count, ignoring sharing below the horizon). -/
partial def vcost (c : VCtx) (d : Nat) (s₁ s₂ : Nat) (sw : Bool := true) : VM Nat := do
  let st ← get
  if st.memo.contains (s₁, s₂) then return 0
  match st.loc[s₁]?, st.loc[s₂]? with
  | some (v, a), some (w, b) => return if v == w && a == 0 && b == 1 then 0 else 1
  | _, _ =>
    match c.pp[s₁]? with
    | some (p, true) => if p == s₂ then return 1 else pure ()
    | some (p, false) => if p == s₂ then return 2 else pure ()
    | none => pure ()
    if d == 0 then return (if s₁ == s₂ then 4 else 3)
    let one (s : Nat) : VM Nat := do
      if (← get).loc.contains s then return 0 else vcost c (d - 1) s s
    let split : VM Nat := do
      let t := 1 + (← one s₁) + (← one s₂)
      -- build the swapped pair, then exchange the lanes
      if sw && s₁ != s₂ then return min t (1 + (← vcost c (d - 1) s₂ s₁ false)) else return t
    match c.op s₁, c.op s₂ with
    | some o₁, some o₂ =>
      match o₁, o₂ with
      | .cst _, .cst _ | .zero, .zero | .cst _, .zero | .zero, .cst _ => return 1
      | _, _ =>
      match vcands o₁ o₂ with
      | some cs =>
          let mut best := 1000000
          for cand in cs do
            let mut t := 1
            for (x, y) in cand do t := t + (← vcost c (d - 1) x y)
            if t < best then best := t
          return min best (← split)
      | none => split
    | _, _ => split

/-- Lookahead depth of the pairing cost estimate. -/
def vdepth : Nat := 3

/-- Index of the cheapest candidate pairing. -/
partial def vbest (c : VCtx) (cs : List (List (Nat × Nat))) : VM Nat := do
  let mut best := 0
  let mut bc := 1000000
  let mut i := 0
  for cand in cs do
    let mut t := 0
    for (x, y) in cand do t := t + (← vcost c vdepth x y)
    if t < bc then bc := t; best := i
    i := i + 1
  return best

mutual

/-- A vector holding slot `s₁` in the low lane and `s₂` in the high lane. -/
partial def vpair (c : VCtx) (s₁ s₂ : Nat) (sw : Bool := true) : VM String := do
  let st ← get
  if let some v := st.memo[(s₁, s₂)]? then return v
  match st.loc[s₁]?, st.loc[s₂]? with
  | some (v, a), some (w, b) =>
      if v == w && a == 0 && b == 1 then return v
      c.emit s₁ s₂ (c.t.shuffle v w a b)
  | _, _ =>
    -- building the swapped pair and exchanging lanes may be cheaper
    let swapped ← if sw && s₁ != s₂ && c.pp[s₁]? == some (s₂, false) then pure true
      else if sw && s₁ != s₂ && c.pp[s₁]? == some (s₂, true) then pure false
      else if sw && s₁ != s₂ then do
        let cs := 1 + (← vcost c vdepth s₂ s₁ false)
        let cd ← vcost c (vdepth + 1) s₁ s₂ false
        pure (decide (cs < cd))
      else pure false
    if swapped then
      let v ← vpair c s₂ s₁ false
      return ← c.emit s₁ s₂ (c.t.shuffle v v 1 0)
    match c.op s₁, c.op s₂ with
    | some o₁, some o₂ =>
      match ← vmatch c s₁ s₂ o₁ o₂ with
      | some v => return v
      | none => vsplit c s₁ s₂
    | _, _ => vsplit c s₁ s₂

/-- Fallback: compute each slot in both lanes, then shuffle. -/
partial def vsplit (c : VCtx) (s₁ s₂ : Nat) : VM String := do
  let get1 (s : Nat) : VM (String × Nat) := do
    if let some (v, a) := (← get).loc[s]? then return (v, a)
    return (← vpair c s s, 0)
  let (v, a) ← get1 s₁
  let (w, b) ← get1 s₂
  if v == w && a == 0 && b == 1 then return v
  c.emit s₁ s₂ (c.t.shuffle v w a b)

/-- Operand order for a commutative pair of operations. -/
partial def vorder (c : VCtx) (a₁ b₁ a₂ b₂ : Nat) : VM (Nat × Nat × Nat × Nat) := do
  if (← vbest c [[(a₁, a₂), (b₁, b₂)], [(a₁, b₂), (b₁, a₂)]]) == 0 then return (a₁, a₂, b₁, b₂)
  return (a₁, b₂, b₁, a₂)

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
      let (x₁, x₂, y₁, y₂) ← vorder c a₁ b₁ a₂ b₂
      let u ← vpair c x₁ x₂; let v ← vpair c y₁ y₂
      some <$> c.emit s₁ s₂ s!"{p}_add_pd({u}, {v})"
  | .mul a₁ b₁, .mul a₂ b₂ => do
      let (x₁, x₂, y₁, y₂) ← vorder c a₁ b₁ a₂ b₂
      let u ← vpair c x₁ x₂; let v ← vpair c y₁ y₂
      some <$> c.emit s₁ s₂ s!"{p}_mul_pd({u}, {v})"
  | .sub a₁ b₁, .sub a₂ b₂ => do
      let u ← vpair c a₁ a₂; let v ← vpair c b₁ b₂
      some <$> c.emit s₁ s₂ s!"{p}_sub_pd({u}, {v})"
  | .sub a₁ b₁, .add a₂ b₂ => do
      -- low a₁ − b₁, high a₂ + b₂ (either order of the sum)
      let (a₂, b₂) := if (← vbest c [[(a₁, a₂), (b₁, b₂)], [(a₁, b₂), (b₁, a₂)]]) == 1 then (b₂, a₂) else (a₂, b₂)
      let u ← vpair c a₁ a₂; let v ← vpair c b₁ b₂
      some <$> c.emit s₁ s₂ s!"{p}_fmaddsub_pd({u}, {one}, {v})"
  | .add a₁ b₁, .sub a₂ b₂ => do
      let (a₁, b₁) := if (← vbest c [[(a₁, a₂), (b₁, b₂)], [(b₁, a₂), (a₁, b₂)]]) == 1 then (b₁, a₁) else (a₁, b₁)
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
          let (x₁, x₂, y₁, y₂) ← vorder c a₁ b₁ a₂ b₂
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
  let c : VCtx := ⟨t, k, pfx, ind, slpPairs k⟩
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
def ctwoName (R1 R2 vlc : Nat) (fwd : Bool) : String := s!"lf_ctwo_{R1}x{R2}_c{vlc}_{dirTag fwd}"

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
def emitCFused (R1 R2 vlc : Nat) (fwd : Bool) (mem : Bool := false) : String := Id.run do
  let t : CTarget := ⟨vlc⟩
  let ty := t.ty
  let p := t.pre
  let N := R1 * R2
  let k1 := butterflyK fwd R1 false
  let k2 := butterflyK fwd R2 true
  let tw := passTwiddles (Trig.cosSin2PiTable N) fwd N R2 R1
  let mut ls : List String :=
    if mem then [s!"static void {ctwoName R1 R2 vlc fwd}(const double *in, double *mid, double *out) \{"]
    else [s!"static void {cfusedName R1 R2 vlc fwd}(const double *in, double *out) \{"]
  -- pass 1: lanes j = jb·VLc + l; input r of butterfly j is in[j + r·R2]. Each block is
  -- loaded, transformed and transposed in turn, to keep few vectors live.
  -- Pass 2 input r of butterfly k is pass-1 output k of butterfly r.
  let mut X : Array (Array String) := Array.replicate (R1 / vlc) (Array.replicate R2 "")
  for jb in [0:R2 / vlc] do
    for r in [0:R1] do
      ls := ls ++ [s!"  const {ty} x{jb}_{r} = {p}_loadu_pd(in + {2 * (jb * vlc + r * R2)});"]
    let (lines, outs) := k1.instC t "  " s!"p{jb}_" fun r => s!"x{jb}_{r}"
    ls := ls ++ lines.toList
    let rb := jb
    for kb in [0:R1 / vlc] do
      let rows := (Array.range vlc).map fun l => outs[kb * vlc + l]!
      let (decls, cols) := ctranspose t "  " s!"c{kb}_{rb}" rows
      ls := ls ++ decls
      for m in [0:vlc] do
        if mem then
          -- pass-2 input (kb, r) is stored at mid[kb·VLc + r·R1] (the Stockham position)
          ls := ls ++ [s!"  {p}_storeu_pd(mid + {2 * (kb * vlc + (rb * vlc + m) * R1)}, {cols[m]!});"]
          X := X.set! kb ((X[kb]!).set! (rb * vlc + m) s!"m{kb}_{rb * vlc + m}")
        else
          X := X.set! kb ((X[kb]!).set! (rb * vlc + m) cols[m]!)
  if mem then
    ls := ls ++ ["  __asm__ volatile(\"\" ::: \"memory\");"]
  -- pass 2: lanes k = kb·VLc + l, twiddle (r, k) of the table of pass 1 (ns = R1)
  for kb in [0:R1 / vlc] do
    for r in [1:R2] do
      let lits := (List.range vlc).flatMap fun l =>
        let kk := kb * vlc + l
        [floatCLit tw[2 * (r - 1) * R1 + kk]!, floatCLit tw[(2 * (r - 1) + 1) * R1 + kk]!]
      ls := ls ++ [s!"  const {ty} w{kb}_{r} = {p}_setr_pd({String.intercalate ", " lits});"]
    if mem then
      for r in [0:R2] do
        ls := ls ++ [s!"  const {ty} m{kb}_{r} = {p}_loadu_pd(mid + {2 * (kb * vlc + r * R1)});"]
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

/-- `(R1, R2, VLc)` of the interleaved two-pass transforms: as `emitCFused`, with the pass-1
results stored to memory (`mem := true`) because they do not fit in registers. -/
def ctwoSet : List (Nat × Nat × Nat) :=
  [(8, 16, 4), (16, 8, 4), (4, 32, 4), (32, 4, 4), (16, 16, 4), (8, 32, 4), (32, 8, 4),
   (16, 32, 4), (32, 16, 4), (32, 32, 4)]

/-- The interleaved fused kernels and their lookup function (appended after `emitKernels`). -/
def emitCFusedKernels (xs : List (Nat × Nat × Nat) := cfusedSet) : String := Id.run do
  let mut s := ""
  for fwd in [true, false] do
    for (R1, R2, vlc) in xs do s := s ++ emitCFused R1 R2 vlc fwd
  s := s ++ joinLines (["lf_cfused_fn lf_get_cfused(int R1, int R2, int vlc, int fwd) {"] ++
      ([true, false].flatMap fun fwd => xs.map fun (R1, R2, vlc) =>
        s!"  if (R1 == {R1} && R2 == {R2} && vlc == {vlc} && fwd == {if fwd then 1 else 0}) return {cfusedName R1 R2 vlc fwd};") ++
      ["  return 0;", "}", ""])
  for fwd in [true, false] do
    for (R1, R2, vlc) in ctwoSet do s := s ++ emitCFused R1 R2 vlc fwd (mem := true)
  s := s ++ joinLines (["lf_ctwo_fn lf_get_ctwo(int R1, int R2, int vlc, int fwd) {"] ++
      ([true, false].flatMap fun fwd => ctwoSet.map fun (R1, R2, vlc) =>
        s!"  if (R1 == {R1} && R2 == {R2} && vlc == {vlc} && fwd == {if fwd then 1 else 0}) return {ctwoName R1 R2 vlc fwd};") ++
      ["  return 0;", "}", ""])
  return s

end LeanFFTW.Gen
