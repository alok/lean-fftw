/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Gen.Sym

/-!
# Symbolic DFTs for butterflies of non-power-of-two radix

The generic algorithm (`exec`/`mkPlan` of `LeanFFTW.Core.Alg`) evaluates a prime-size leaf
as the direct `O(p²)` sum, with one complex multiplication per term. For the generated
kernels of radices that are not powers of two, `symDFT` uses two classical refinements,
proved in `LeanFFTW/Proof/Butterfly.lean` (`symDFT_spec`):

* **Odd lengths** (`oddLeaf`). Terms `j` and `p - j` share the twiddle up to conjugation,
  `ω^{(p-j)k} = conj ω^{jk}`, so with `a_j = x_j + x_{p-j}`, `b_j = x_j - x_{p-j}`,
  `A_k = x_0 + Σ_j cos(2πjk/p) a_j` and `S_k = Σ_j sin(2πjk/p) b_j` (real coefficients),
  `X_k = A_k ± i S_k` and `X_{p-k} = A_k ∓ i S_k` (the sign is that of the transform).
  A length-`p` DFT then costs `p² - 1 + …` real fused operations instead of `≈ 4p²`.
* **Mixed radix** (`symDFT`). For `n = r·m`, the `r` sub-transforms of size `m` are
  twiddled and combined by `m` DFTs of size `r` (Cooley–Tukey with the combination
  factored as `DFT_r ∘ diag(ω_n^{j₁k₁})`), instead of the direct combination sum of `exec`.

Every constant is `cos` or `sin` of an angle in `[0, π/2]`, so it is nonnegative; the sign
of a term is carried by the fused operation (`fma` or `fnma`).
-/

namespace LeanFFTW.Gen

open SExpr

/-- `cos (2π m / n)` (`2m ≤ n`) as a sign (`true`: negative) and a constant of the first
quadrant. -/
def cosH (m n : Nat) : Bool × Cst :=
  if 4 * m ≤ n then (false, .cos m n) else (true, .cos (n - 2 * m) (2 * n))

/-- `cos (2π m / n)` (`m < n`) as a sign and a constant of the first quadrant. -/
def cosQ (m n : Nat) : Bool × Cst := cosH (if 2 * m ≤ n then m else n - m) n

/-- `sin (2π m / n)` (`2m ≤ n`), a constant of the first quadrant. -/
def sinH (m n : Nat) : Cst :=
  if 4 * m ≤ n then .sin m n else .sin (n - 2 * m) (2 * n)

/-- `sin (2π m / n)` (`m < n`) as a sign (`true`: negative) and a constant of the first
quadrant. -/
def sinQ (m n : Nat) : Bool × Cst :=
  if 2 * m ≤ n then (false, sinH m n) else (true, sinH (n - m) n)

/-- `acc ± c·a`. -/
def sfma (ng : Bool) (c : Cst) (a acc : SExpr) : SExpr :=
  if ng then mkFnmaC c a acc else mkFmaC c a acc

/-- `± c·a`. -/
def smul (ng : Bool) (c : Cst) (a : SExpr) : SExpr :=
  if ng then mkNeg (mkMulC c a) else mkMulC c a

/-- `init + Σ ±cᵢ aᵢ`, accumulated left to right with fused operations. -/
def lacc (init : SExpr) (ts : List (Bool × Cst × SExpr)) : SExpr :=
  ts.foldl (fun acc t => sfma t.1 t.2.1 t.2.2 acc) init

/-- `Σ ±cᵢ aᵢ`: the first term is a product, the others are fused into it. -/
def lsum : List (Bool × Cst × SExpr) → SExpr
  | [] => .zero
  | t :: ts => lacc (smul t.1 t.2.1 t.2.2) ts

/-! ### Odd lengths -/

/-- `x_j + x_{p-j}`, `j = i + 1`. -/
def pairA (p : Nat) (x : Nat → SC) (i : Nat) : SExpr × SExpr :=
  ((mkAdd (x (i + 1)).parts.1 (x (p - (i + 1))).parts.1),
   (mkAdd (x (i + 1)).parts.2 (x (p - (i + 1))).parts.2))

/-- `x_j - x_{p-j}`, `j = i + 1`. -/
def pairB (p : Nat) (x : Nat → SC) (i : Nat) : SExpr × SExpr :=
  ((mkSub (x (i + 1)).parts.1 (x (p - (i + 1))).parts.1),
   (mkSub (x (i + 1)).parts.2 (x (p - (i + 1))).parts.2))

/-- The terms `cos (2πjk/p) · part (x_j + x_{p-j})`, `1 ≤ j ≤ p/2`. -/
def cTerms (p k : Nat) (x : Nat → SC) (part : SExpr × SExpr → SExpr) : List (Bool × Cst × SExpr) :=
  (List.range (p / 2)).map fun i =>
    ((cosQ ((i + 1) * k % p) p).1, (cosQ ((i + 1) * k % p) p).2, part (pairA p x i))

/-- The terms `sin (2πjk/p) · part (x_j - x_{p-j})`, `1 ≤ j ≤ p/2`. -/
def sTerms (p k : Nat) (x : Nat → SC) (part : SExpr × SExpr → SExpr) : List (Bool × Cst × SExpr) :=
  (List.range (p / 2)).map fun i =>
    ((sinQ ((i + 1) * k % p) p).1, (sinQ ((i + 1) * k % p) p).2, part (pairB p x i))

/-- `A_k = x_0 + Σ_j cos(2πjk/p) (x_j + x_{p-j})`. -/
def oddA (p k : Nat) (x : Nat → SC) : SExpr × SExpr :=
  (lacc (x 0).parts.1 (cTerms p k x Prod.fst), lacc (x 0).parts.2 (cTerms p k x Prod.snd))

/-- `S_k = Σ_j sin(2πjk/p) (x_j - x_{p-j})`. -/
def oddS (p k : Nat) (x : Nat → SC) : SExpr × SExpr :=
  (lsum (sTerms p k x Prod.fst), lsum (sTerms p k x Prod.snd))

/-- `A_k + i S_k`. -/
def oddPlus (p k : Nat) (x : Nat → SC) : SC :=
  .val (mkSub (oddA p k x).1 (oddS p k x).2) (mkAdd (oddA p k x).2 (oddS p k x).1)

/-- `A_k - i S_k`. -/
def oddMinus (p k : Nat) (x : Nat → SC) : SC :=
  .val (mkAdd (oddA p k x).1 (oddS p k x).2) (mkSub (oddA p k x).2 (oddS p k x).1)

/-- `X_0 = x_0 + Σ_j (x_j + x_{p-j})`. -/
def oddX0 (p : Nat) (x : Nat → SC) : SC :=
  .val ((List.range (p / 2)).foldl (fun acc i => mkAdd acc (pairA p x i).1) (x 0).parts.1)
    ((List.range (p / 2)).foldl (fun acc i => mkAdd acc (pairA p x i).2) (x 0).parts.2)

/-- The length-`p` DFT (`p` odd) by pairing the terms `j` and `p - j`: `X_k = A_k ± i S_k`
and `X_{p-k} = A_k ∓ i S_k` for `1 ≤ k ≤ p/2` (upper signs for the anticlockwise
transform, `fwd = false`). -/
def oddLeaf (fwd : Bool) (p : Nat) (x : Nat → SC) : Array SC :=
  (Array.range p).map fun k =>
    if k = 0 then oddX0 p x
    else if k ≤ p / 2 then (if fwd then oddMinus p k x else oddPlus p k x)
    else (if fwd then oddPlus p (p - k) x else oddMinus p (p - k) x)

/-- A prime-length DFT leaf: `oddLeaf` for odd lengths, the direct sum of `exec` otherwise
(for `p = 2` the direct sum is `x₀ ± x₁`). -/
def leafSym (fwd : Bool) (p : Nat) (x : Nat → SC) : Array SC :=
  if p % 2 = 1 ∧ 3 ≤ p then oddLeaf fwd p x
  else exec symOps (.direct p (symOps.build p (symOps.tw fwd p))) x

/-! ### Mixed radix -/

/-- The symbolic DFT of size `fs.prod` of the view `x`. -/
def symDFT (fwd : Bool) : List Nat → (Nat → SC) → Array SC
  | [], x => leafSym fwd 1 x
  | [p], x => leafSym fwd p x
  | r :: s :: rest, x =>
      let m := (s :: rest).prod
      let ys : Array (Array SC) := (Array.range r).map fun j1 =>
        symDFT fwd (s :: rest) (fun j2 => x (j1 + r * j2))
      let cols : Array (Array SC) := (Array.range m).map fun k1 =>
        leafSym fwd r fun j1 => SC.mul (.tw fwd (r * m) (j1 * k1)) (symOps.get (ys.getD j1 #[]) k1)
      (Array.range (r * m)).map fun k => symOps.get (cols.getD (k % m) #[]) (k / m)

/-! ### Coprime factors (Good–Thomas) -/

/-- The prime-power factors of `n`, one per distinct prime: pairwise coprime, with product
`n` (the generator checks both before using them, `pfaOK`). -/
def ppBlocks (n : Nat) : List Nat :=
  let fs := primeFactors n
  fs.eraseDups.map fun p => p ^ fs.count p

/-- The conditions under which `pfaDFT` of the blocks `bs` is a DFT of size `n`. -/
def PfaOK (bs : List Nat) (n : Nat) : Prop :=
  bs.prod = n ∧ (∀ b ∈ bs, 0 < b) ∧ bs.Pairwise Nat.Coprime

instance (bs : List Nat) (n : Nat) : Decidable (PfaOK bs n) := by
  unfold PfaOK; infer_instance

/-- The DFT of size `bs.prod` by the prime factor algorithm (Good–Thomas): for coprime
`r = b` and `m = (c :: rest).prod`, the input `x_{(m j₁ + r j₂) mod n}` is a two-dimensional
`r × m` array whose 2-D DFT, read at `(k mod r, k mod m)`, is `X_k`, with no twiddle factors.
Each block is transformed by `symDFT` on its prime factors. -/
def pfaDFT (fwd : Bool) : List Nat → (Nat → SC) → Array SC
  | [], x => symDFT fwd [] x
  | [b], x => symDFT fwd (primeFactors b) x
  | b :: c :: rest, x =>
      let m := (c :: rest).prod
      let ys : Array (Array SC) := (Array.range b).map fun j1 =>
        pfaDFT fwd (c :: rest) (fun j2 => x ((m * j1 + b * j2) % (b * m)))
      let cols : Array (Array SC) := (Array.range m).map fun k2 =>
        symDFT fwd (primeFactors b) fun j1 => symOps.get (ys.getD j1 #[]) k2
      (Array.range (b * m)).map fun k => symOps.get (cols.getD (k % m) #[]) (k % b)

end LeanFFTW.Gen
