/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/

/-!
# Scalar-generic FFT algorithms

The algorithms are written once, over an abstract scalar type `C` with the operations in
`Ops C V`, where `V` is a materialized vector type. The same definitions are

* instantiated with exact complex numbers in the proofs (`V := ℕ → ℂ`), where they are
  shown to equal the DFT (`LeanFFTW/Proof/Exact.lean`), and
* instantiated with binary64 `Float` pairs stored in `FloatArray`s for execution
  (`LeanFFTW/Core/FloatOps.lean`).

Vectors are passed around as index functions `ℕ → C` ("views") and materialized with
`Ops.build` at the end of every stage, so each stage is computed exactly once.

Twiddle factors live in tables inside the plan, so the twiddle computation (which is
expensive and exact, see `Trig.lean`) happens once at planning time.
-/

namespace LeanFFTW

/-- Operations needed by the FFT algorithms.

* `add`, `sub`, `mul`, `zero`: complex arithmetic,
* `tw fwd n k`: the twiddle `exp (∓ 2πi k / n)` (`-` when `fwd`),
* `build n f` / `get v i`: materialize the first `n` values of a view, and read it back.
  The required law is `get (build n f) i = f i` for `i < n`. -/
structure Ops (C V : Type) where
  zero : C
  add : C → C → C
  sub : C → C → C
  mul : C → C → C
  tw : Bool → Nat → Nat → C
  build : Nat → (Nat → C) → V
  get : V → Nat → C

/-- An FFT plan for a 1-D complex transform: a tree of Cooley–Tukey steps over
direct (quadratic) DFT leaves, carrying its twiddle tables. -/
inductive Plan (V : Type) where
  /-- Direct DFT of size `n`; `w[k] = ω_n^k` for `k < n`. -/
  | direct (n : Nat) (w : V)
  /-- Decimation-in-time Cooley–Tukey with radix `r` over a sub-plan of size `m`:
  `n = r * m`, `w[k] = ω_n^k` for `k < n`. -/
  | ct (r : Nat) (w : V) (sub : Plan V)
  deriving Inhabited

namespace Plan

variable {V : Type}

/-- The transform size of a plan. -/
def size : Plan V → Nat
  | .direct n _ => n
  | .ct r _ sub => r * sub.size

end Plan

variable {C V : Type}

/-- `Σ_{j < n} f j` with the scalar addition of `O`, summed left to right from `zero`. -/
@[inline] def sumRange (O : Ops C V) (n : Nat) (f : Nat → C) : C :=
  Nat.fold n (fun j _ acc => O.add acc (f j)) O.zero

/-- Build a plan from a factorization `fs` (the transform size is `fs.prod`).
The last factor becomes a direct leaf. -/
def mkPlan (O : Ops C V) (fwd : Bool) : List Nat → Plan V
  | [] => .direct 1 (O.build 1 (O.tw fwd 1))
  | [p] => .direct p (O.build p (O.tw fwd p))
  | r :: rest@(_ :: _) =>
      let sub := mkPlan O fwd rest
      let n := r * rest.prod
      .ct r (O.build n (O.tw fwd n)) sub

/-- Execute a plan on an input view. -/
def exec [Inhabited V] (O : Ops C V) : Plan V → (Nat → C) → V
  | .direct n w, x =>
      O.build n fun k => sumRange O n fun j => O.mul (O.get w (j * k % n)) (x j)
  | .ct r w sub, x =>
      let m := sub.size
      let n := r * m
      -- the r decimated sub-transforms: ys[j1] = DFT_m (x[j1 + r*j2])_{j2}
      let ys : Array V := (Array.range r).map fun j1 => exec O sub (fun j2 => x (j1 + r * j2))
      O.build n fun k =>
        sumRange O r fun j1 => O.mul (O.get w (j1 * k % n)) (O.get (ys.getD j1 default) (k % m))

/-- Direct DFT of a view (reference, quadratic). -/
def dftDirect (O : Ops C V) (fwd : Bool) (n : Nat) (x : Nat → C) : V :=
  let w := O.build n (O.tw fwd n)
  O.build n fun k => sumRange O n fun j => O.mul (O.get w (j * k % n)) (x j)

/-- Prime factors of `n` in nondecreasing order (`[]` for `n ≤ 1`). -/
def primeFactors (n : Nat) : List Nat :=
  go n 2 n
where
  go (n d fuel : Nat) : List Nat :=
    match fuel with
    | 0 => if n > 1 then [n] else []
    | fuel + 1 =>
      if n ≤ 1 then []
      else if d * d > n then [n]
      else if n % d == 0 then d :: go (n / d) d fuel
      else go n (d + 1) fuel

end LeanFFTW
