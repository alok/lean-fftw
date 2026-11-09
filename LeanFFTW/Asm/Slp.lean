/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Build
import LeanFFTW.Gen.Interleave

/-!
# Interleaved-complex vectorization, to virtual registers

For small transforms the data stays in FFTW's interleaved layout: a vector holds `VLc`
complex numbers, and the real and imaginary operations of a kernel are paired so that one
vector operation performs, in each lane, the kernel operation of that lane's slot
(`LeanFFTW/Gen/Interleave.lean` describes the method and plans the pairs, `slpPairs`).

This file places a kernel that way as a block of virtual-register code. A vector made by
`vpair s₁ s₂` holds kernel slot `s₁` in the even lanes and `s₂` in the odd lanes.
-/

namespace LeanFFTW.Asm

open Std LeanFFTW.Gen

structure SState where
  /-- vectors already made, by the slots they hold -/
  memo : HashMap (Nat × Nat) VId := {}
  /-- where a slot is available: vector and lane parity -/
  loc : HashMap Nat (VId × Nat) := {}

abbrev SM := StateT SState BlockM

structure SCtx where
  vlc : Nat
  k : Kernel
  /-- planned pairs (`slpPairs`): slot ↦ (partner, slot is the low lane) -/
  pp : HashMap Nat (Nat × Bool) := {}

namespace SCtx

def op (c : SCtx) (s : Nat) : Option KOp :=
  if s < c.k.nIn then none else c.k.ops[s - c.k.nIn]?

/-- Define a vector holding slots `s₁` (even lanes) and `s₂` (odd lanes). -/
def emit (_c : SCtx) (s₁ s₂ : Nat) (op : VOp) : SM VId := do
  let v ← liftM (m := BlockM) (BlockM.df op)
  modify fun st =>
    let loc := if st.loc.contains s₁ then st.loc else st.loc.insert s₁ (v, 0)
    let loc := if loc.contains s₂ then loc else loc.insert s₂ (v, 1)
    { memo := st.memo.insert (s₁, s₂) v, loc }
  return v

/-- A vector that is not recorded as holding slots (an intermediate). -/
def tmp (_c : SCtx) (op : VOp) : SM VId := liftM (m := BlockM) (BlockM.df op)

/-- Even lanes `a[ia]`, odd lanes `b[ib]`, in every complex number. -/
def shuffle (c : SCtx) (a b : VId) (ia ib : Nat) : VOp :=
  .shufpd a b ((List.range c.vlc).foldl (fun acc i => acc + (ia + 2 * ib) * 4 ^ i) 0)

/-- Constants `lo`, `hi` in the even and odd lanes. -/
def pairBits (c : SCtx) (lo hi : UInt64) : Array UInt64 :=
  (Array.range (2 * c.vlc)).map fun i => if i % 2 == 0 then lo else hi

end SCtx

/-- Estimated number of vector operations still needed to build the pair `(s₁, s₂)`,
looking `d` levels down (as `LeanFFTW.Gen.vcost`). -/
partial def scost (c : SCtx) (d : Nat) (s₁ s₂ : Nat) (sw : Bool := true) : SM Nat := do
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
    let one (s : Nat) : SM Nat := do
      if (← get).loc.contains s then return 0 else scost c (d - 1) s s
    let split : SM Nat := do
      let t := 1 + (← one s₁) + (← one s₂)
      if sw && s₁ != s₂ then return min t (1 + (← scost c (d - 1) s₂ s₁ false)) else return t
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
            for (x, y) in cand do t := t + (← scost c (d - 1) x y)
            if t < best then best := t
          return min best (← split)
      | none => split
    | _, _ => split

/-- Index of the cheapest candidate pairing. -/
def sbest (c : SCtx) (cs : List (List (Nat × Nat))) : SM Nat := do
  let mut best := 0
  let mut bc := 1000000
  let mut i := 0
  for cand in cs do
    let mut t := 0
    for (x, y) in cand do t := t + (← scost c vdepth x y)
    if t < bc then bc := t; best := i
    i := i + 1
  return best


mutual

/-- A vector holding slot `s₁` in the even lanes and `s₂` in the odd lanes. -/
partial def spair (c : SCtx) (s₁ s₂ : Nat) (sw : Bool := true) : SM VId := do
  let st ← get
  if let some v := st.memo[(s₁, s₂)]? then return v
  match st.loc[s₁]?, st.loc[s₂]? with
  | some (v, a), some (w, b) =>
      if v == w && a == 0 && b == 1 then return v
      c.emit s₁ s₂ (c.shuffle v w a b)
  | _, _ =>
    -- building the swapped pair and exchanging lanes may be cheaper
    let swapped ← if sw && s₁ != s₂ && c.pp[s₁]? == some (s₂, false) then pure true
      else if sw && s₁ != s₂ && c.pp[s₁]? == some (s₂, true) then pure false
      else if sw && s₁ != s₂ then do
        let cs := 1 + (← scost c vdepth s₂ s₁ false)
        let cd ← scost c (vdepth + 1) s₁ s₂ false
        pure (decide (cs < cd))
      else pure false
    if swapped then
      let v ← spair c s₂ s₁ false
      return ← c.emit s₁ s₂ (c.shuffle v v 1 0)
    match c.op s₁, c.op s₂ with
    | some o₁, some o₂ =>
      match ← smatch c s₁ s₂ o₁ o₂ with
      | some v => return v
      | none => ssplit c s₁ s₂
    | _, _ => ssplit c s₁ s₂

/-- Fallback: compute each slot in both lanes, then shuffle. -/
partial def ssplit (c : SCtx) (s₁ s₂ : Nat) : SM VId := do
  let get1 (s : Nat) : SM (VId × Nat) := do
    if let some (v, a) := (← get).loc[s]? then return (v, a)
    return (← spair c s s, 0)
  let (v, a) ← get1 s₁
  let (w, b) ← get1 s₂
  if v == w && a == 0 && b == 1 then return v
  c.emit s₁ s₂ (c.shuffle v w a b)

/-- Operand order for a commutative pair of operations. -/
partial def sorder (c : SCtx) (a₁ b₁ a₂ b₂ : Nat) : SM (Nat × Nat × Nat × Nat) := do
  if (← sbest c [[(a₁, a₂), (b₁, b₂)], [(a₁, b₂), (b₁, a₂)]]) == 0 then return (a₁, a₂, b₁, b₂)
  return (a₁, b₂, b₁, a₂)

/-- A vector operation performing `o₁` in the even lanes and `o₂` in the odd lanes. -/
partial def smatch (c : SCtx) (s₁ s₂ : Nat) (o₁ o₂ : KOp) : SM (Option VId) := do
  let lit : KOp → Option UInt64
    | .cst k => some k.toFloat.toBits
    | .zero => some 0
    | _ => none
  match o₁, o₂ with
  | .add a₁ b₁, .add a₂ b₂ => do
      let (x₁, x₂, y₁, y₂) ← sorder c a₁ b₁ a₂ b₂
      let u ← spair c x₁ x₂; let v ← spair c y₁ y₂
      some <$> c.emit s₁ s₂ (.bin .add u v)
  | .mul a₁ b₁, .mul a₂ b₂ => do
      let (x₁, x₂, y₁, y₂) ← sorder c a₁ b₁ a₂ b₂
      let u ← spair c x₁ x₂; let v ← spair c y₁ y₂
      some <$> c.emit s₁ s₂ (.bin .mul u v)
  | .sub a₁ b₁, .sub a₂ b₂ => do
      let u ← spair c a₁ a₂; let v ← spair c b₁ b₂
      some <$> c.emit s₁ s₂ (.bin .sub u v)
  | .sub a₁ b₁, .add a₂ b₂ => do
      -- even lanes a₁ − b₁, odd lanes a₂ + b₂ (either order of the sum)
      let (a₂, b₂) := if (← sbest c [[(a₁, a₂), (b₁, b₂)], [(a₁, b₂), (b₁, a₂)]]) == 1 then (b₂, a₂) else (a₂, b₂)
      let u ← spair c a₁ a₂; let v ← spair c b₁ b₂
      some <$> c.emit s₁ s₂ (.addsub u v)
  | .add a₁ b₁, .sub a₂ b₂ => do
      let (a₁, b₁) := if (← sbest c [[(a₁, a₂), (b₁, b₂)], [(b₁, a₂), (a₁, b₂)]]) == 1 then (b₁, a₁) else (a₁, b₁)
      let u ← spair c a₁ a₂; let v ← spair c b₁ b₂
      some <$> c.emit s₁ s₂ (.subadd u v)
  | .neg a₁, .neg a₂ => do
      let u ← spair c a₁ a₂
      some <$> c.emit s₁ s₂ (.xorc u #[signBit])
  | _, _ =>
    match lit o₁, lit o₂ with
    | some l₁, some l₂ =>
        if l₁ == 0 && l₂ == 0 then some <$> c.emit s₁ s₂ .zero
        else if l₁ == l₂ then some <$> c.emit s₁ s₂ (.bcast l₁)
        else some <$> c.emit s₁ s₂ (.cvec (c.pairBits l₁ l₂))
    | _, _ =>
      match fsign o₁, fsign o₂ with
      | some (a₁, b₁, c₁, sp₁, sc₁), some (a₂, b₂, c₂, sp₂, sc₂) => do
          let (x₁, x₂, y₁, y₂) ← sorder c a₁ b₁ a₂ b₂
          let u ← spair c x₁ x₂; let v ← spair c y₁ y₂; let w ← spair c c₁ c₂
          -- make the product signs equal by negating lanes of the first factor (exact)
          let (u, sp) ←
            if sp₁ == sp₂ then pure (u, sp₁)
            else do
              let mask := if sp₁ then c.pairBits 0 signBit else c.pairBits signBit 0
              pure (← c.tmp (.xorc u mask), true)
          let f : Option VFma := match sp, sc₁, sc₂ with
            | true, true, true => some .fmadd
            | true, false, false => some .fmsub
            | true, false, true => some .fmaddsub
            | true, true, false => some .fmsubadd
            | false, true, true => some .fnmadd
            | false, _, _ => none
          match f with
          | some f => some <$> c.emit s₁ s₂ (.fma f u v w)
          | none => return none
      | _, _ => return none

end

/-- Place a kernel with interleaved vectors: input slot `i` is lane parity `i % 2` of
vector `bind (i / 2)`. Returns the output vectors (output `r` = slots `outs[2r]`,
`outs[2r+1]`). -/
def instC (k : Kernel) (vlc : Nat) (bind : Nat → VId) : BlockM (Array VId) := do
  let c : SCtx := ⟨vlc, k, slpPairs k⟩
  let mut st : SState := {}
  for i in [0:k.nIn] do
    st := { st with loc := st.loc.insert i (bind (i / 2), i % 2) }
  let mut outs : Array VId := #[]
  for r in [0:k.outs.size / 2] do
    let (v, st') ← (spair c k.outs[2 * r]! k.outs[2 * r + 1]!).run st
    st := st'
    outs := outs.push v
  return outs

end LeanFFTW.Asm
