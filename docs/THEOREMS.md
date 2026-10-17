# Theorems

Every theorem below is checked by Lean's kernel with no `sorry`, no `admit` and no new
axioms. `scripts/Axioms.lean` prints the axioms of each one; all of them depend only on
`propext`, `Classical.choice` and `Quot.sound` (the standard axioms Mathlib uses).

```
lake env lean scripts/Axioms.lean
```

[TRUST.md](TRUST.md) says which parts of the running library these theorems cover and
which links are established by testing instead.

## 1. Specification

`LeanFFTW/Spec/DFT.lean`

```lean
def twiddle (fwd : Bool) (n k : ℕ) : ℂ        -- exp(∓2πi·k/n), sign − when fwd
def dftSum (fwd : Bool) (n : ℕ) (x : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range n, twiddle fwd n (j * k) * x j
```

`dftSum` is FFTW's unnormalized transform. It is tied to Mathlib's independently written
DFT on `ZMod n` (`Mathlib/Analysis/Fourier/ZMod.lean`):

| Theorem | Statement |
|---|---|
| `dftSum_true_eq_dft` | `k < n → dftSum true n x k = 𝓕 (fun j : ZMod n => x j.val) k` |
| `dftSum_false_eq_invDft` | `k < n → dftSum false n x k = n * 𝓕⁻ (fun j : ZMod n => x j.val) k` |

## 2. Exact-arithmetic correctness

### Cooley–Tukey and the generic engine's algorithm (`Proof/Exact.lean`)

| Theorem | Statement |
|---|---|
| `dftSum_ct` | `0 < r → 0 < m → dftSum fwd (r*m) x k = ∑ j1<r, twiddle fwd (r*m) (j1*k) * dftSum fwd m (fun j2 => x (j1 + r*j2)) (k % m)` |
| `exec_mkPlan_exact` | for factors `fs` (all positive) and `k < fs.prod`: `exec exactOps (mkPlan exactOps fwd fs) x k = dftSum fwd fs.prod x k` |
| `exec_mkPlan_exact_eq_dft` | the same, stated against `ZMod.dft` |

`mkPlan`/`exec` (`Core/Alg.lean`) are the generic engine's mixed-radix algorithm, written
once over an abstract `Ops` interface; `exactOps` instantiates it with exact complex
numbers.

### Generated kernels (`Proof/Kernel.lean`, `Proof/Butterfly.lean`)

The codelet generator builds symbolic expressions (`SExpr`), simplifies them, and
common-subexpression-eliminates them into straight-line `Kernel`s (`cst`, `add`, `sub`,
`mul`, `neg`, `fma`, `fms`, `fnma`). A `Kernel` evaluates over any `Arith`.

| Theorem | Statement |
|---|---|
| `cse_correct` | for a commutative `Arith` and outputs whose inputs are in range: `(cse nIn outs).eval A inp = outs.map (SExpr.evalWith A inp)` |
| `exec_sym` | running the algorithm over symbolic complex values and reading them back equals running it over exact complex values, and the symbolic values stay well formed |
| `butterflyK_correct` | `0 < R → inp.size = butterflyInputs R twiddled → (butterflyK fwd R twiddled).eval realArith inp` is the size-`R` DFT of the (optionally twiddled) inputs, re/im interleaved |

`butterflyK fwd R tw` is the exact kernel that the C code generator prints as SIMD C.

The generator's optimizations are part of what these theorems cover, because
`butterflyK_correct` is about the kernel after every rewrite. Two of them have their own
lemmas:

| Lemma | Statement |
|---|---|
| `ev_contract` | FMA contraction (`SExpr.contract`) does not change an expression's real value |
| `evC_rotQ` | the twiddle rotation `SC.rotQ k n a b` denotes `(a + ib) · exp(2πik/n)` for `4k < n`. Since i7 a rotation by `θ ∉ (π/4)ℤ` is generated as `cos θ · (a − tan θ · b) + i · cos θ · (b + tan θ · a)` (one fused operation per part; the product by `cos θ` fuses into the butterfly additions), and the proof uses `tan θ · cos θ = sin θ` with `cos θ > 0` (`cos_two_pi_div_pos`) |

### The Stockham schedule (`Proof/Stockham.lean`)

`stockhamWith A fwd N rs twOf z` (`Gen/Stockham.lean`) runs the passes of a plan with radices
`rs` over interleaved data `z`, each pass applying `butterflyK` to every butterfly with the
twiddle table `twOf t`. It is the reference semantics of the fast engine.

| Theorem | Statement |
|---|---|
| `stockInv_pass` | one pass of radix `R` maps the invariant `StockInv fwd N ns x` to `StockInv fwd N (ns*R) x` (the data holds the size-`ns` sub-DFTs, in Stockham order) |
| `stockhamWith_exact` | for positive radices with `N = ∏ rs` and `z.size = 2N`, over exact reals with exact twiddles `exactTwOf`, `stockhamWith realArith fwd N rs (exactTwOf fwd N rs) z` is exactly `dftSum fwd N` of `z`, re/im interleaved |

### The generic engine's compiled code (`Core/FastExec.lean`)

`execFloat p x = exec floatOps p x` is the generic algorithm run on binary64 values. The
compiled library runs a different function, `execFloatFast`, which materializes the input
once, reads sub-transforms at an offset and stride, and sums each output in an unboxed
loop. `@[csimp]` makes the compiler substitute it for `execFloat`; the attribute is only
accepted with a proof that the two functions are equal.

| Theorem | Statement |
|---|---|
| `execFloat_eq_fast` | `@execFloat = @execFloatFast` (so the fast code computes exactly, bit for bit, what the specification computes) |
| `Fast.execArr_eq` | `execArr p X off st = exec floatOps p (fun j => X.get (off + st*j))` |
| `exec_congr` | `exec O p` reads its input only at indices below `p.size` |

The proof needs only Lean core (the executable library does not depend on Mathlib). It
holds because the fast loops perform the same `Float` operations as `exec floatOps`, in
the same order, from the same starting value `0`.

## 3. Floating-point error bounds

### Abstract rounding model (`Proof/RoundError.lean`)

`StdModel A v fin u κ ℓ` says that the arithmetic `A`, read through `v : α → ℝ`, rounds
each finite `add/sub/mul/fma/fms/fnma` result with relative error `u` plus an absolute
floor `u·ℓ` (underflow), negates exactly, and reads constants with error `κ(|c| + ℓ)`.
Three shadow arithmetics compute bounds by running the same kernel or schedule:

* `magArith ℓ`: magnitudes (every operation replaced by its absolute-value version, plus `ℓ`);
* `errArith u κ`: relative-error factors;
* `depthArith`: for each value, the pair (number of roundings on its longest path, number of
  constants/twiddles on it).

| Theorem | Statement (hypotheses abbreviated) |
|---|---|
| `Kernel.eval_error` | if inputs are within `φᵢ·mᵢ` of exact values `x` with `|xᵢ| ≤ mᵢ`, and every intermediate slot is finite, then each output is within `errArith(φ)ₒ · magArith(m)ₒ` of `k.eval realArith x` |
| `Kernel.eval_error_depth` | the same with the closed form `((1+u)^a (1+t)^b − 1) · magArith(m)ₒ`, where `(a, b)` is the `depthArith` depth and `t ≥ κ, φᵢ` |
| `stockhamWith_err` | the per-output error invariant through every pass of the schedule, with twiddle tables accurate to `τ` |
| `stockhamWith_error_dft` | combines the above with `stockhamWith_exact`: the computed schedule is within `errArith · magArith` of the exact DFT of the inputs |
| `stockhamWith_errArith_le_depth` | the schedule's `errArith` bound is at most `(1+u)^a (1+t)^b − 1` for `t ≥ κ, τ` |

### IEEE binary64 instance (`Proof/FloatError.lean`)

Lean 4.35 defines `Float` arithmetic through `Float.Model`, so a Lean `Float` value can be
read as a FloatLib binary64 value (`toReal64`). FloatLib proves round-to-nearest-even for
`+ − ×`; the fused multiply-add lemma was missing and is proved here.

| Theorem | Statement |
|---|---|
| `toReal_ofModel_fma_toModel_eq_roundAt` | for an IEEE format and finite `x, y, z` with a finite result, the model's `fma` is `roundAt(x·y + z)` (one rounding) |
| `floatArith_stdModel` | `floatArith` (Lean `Float` with fma) satisfies `StdModel` with `u = 2⁻⁵³`, `ℓ = 2⁻¹⁰²²`, given constant accuracy `κ` (`hcst`) |
| `Kernel.eval_float_error`, `Kernel.eval_float_error_depth` | the kernel bounds for `Float` |
| `stockhamWith_float_error_dft` | the schedule bound for `Float`, against the exact DFT |
| `refTransform_error` | for the executable reference `refTransform fwd N rs inp` (the function the C fast engine is tested against bit for bit): every output is within `errArith(0) · magArith(|inp|)` of the exact DFT of the binary64 inputs |
| `refTransform_error_depth` | the same in closed form: error ≤ `((1+2⁻⁵³)^a (1+max τ κ)^b − 1) · magArith(|inp|)ᵢ` |

Hypotheses of the binary64 theorems, stated explicitly:

* `hfin` (`StockhamSlotsOK`): every value the run touches (each butterfly's inputs,
  twiddles and intermediate results, in every pass) is finite, i.e. finite inputs and no
  overflow. Subnormals are allowed; their effect is the floor `ℓ`.
* `hcst`: each generated constant (e.g. `cos(π/8)`) is stored with relative error `κ`.
* `htw`: each twiddle-table entry produced by `Trig.cosSin2PiTable` is within `τ` of the
  exact `cos`/`sin`. The accuracy of `Trig` itself is not analysed in Lean.

## Not proved

* The generic engine's executable path (`floatOps`, `Core/FloatOps.lean`, used for
  non-power-of-two sizes, r2c/c2r, r2r, multi-dimensional and strided problems) has an
  exact-arithmetic algorithm proof (`exec_mkPlan_exact`) and a proof that its compiled
  fast form computes the same function (`execFloat_eq_fast`), but no floating-point bound, and
  the r2r/r2c embeddings (`Core/Problem.lean`) are not proved; they are validated by FFTW's
  own test harness.
* The accuracy of the twiddle generator (`Trig`) and of decimal constants (`τ`, `κ` above).
* The C code: see [TRUST.md](TRUST.md).
