/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Stockham

/-!
# Pairing kernel slots for interleaved-complex vectors

For small transforms the data stays in FFTW's interleaved layout (`re, im, re, im, …`): a
vector holds `VLc` complex numbers, and each operation of a kernel whose inputs and outputs
come in `(re, im)` pairs is executed on the real and imaginary lanes of every complex
number at once. `slpPairs` plans which slots share a vector; the assembly back end
(`LeanFFTW/Asm/Slp.lean`) emits the vector operations, and the checker of the emitted code
verifies them, so nothing here is trusted.
-/

namespace LeanFFTW.Gen

open Std

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

/-- How many levels of operands the pairing search looks ahead when it compares candidates. -/
def vdepth : Nat := 3

end LeanFFTW.Gen
