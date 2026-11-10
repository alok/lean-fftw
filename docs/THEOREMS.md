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

Kernels whose radix is not a power of two (3, 5, 6, 7, 9–13, 15, and the whole-transform
kernels of composite sizes up to 64) are built from three classical algorithms
(`Gen/SymDFT.lean`), each proved to denote the DFT. `butterflyK_correct` covers them through
`bflySym_spec`, so every downstream theorem holds for them unchanged.

| Theorem | Statement |
|---|---|
| `oddLeaf_spec` | for odd `p`, the paired form `X_k = A_k ± i·S_k`, `X_{p-k} = A_k ∓ i·S_k` with `A_k = x₀ + Σ cos(2πjk/p)(x_j + x_{p-j})` and `S_k = Σ sin(2πjk/p)(x_j − x_{p-j})` (real coefficients, every constant in the first quadrant, signs carried by `fma`/`fnma`) is the length-`p` DFT |
| `symDFT_spec` | the mixed-radix recursion `symDFT` (sub-transforms of the decimated inputs, twiddles, then length-`r` DFTs) over a list of positive factors is the DFT of size `fs.prod` |
| `sum_pfa_index` | for coprime `r`, `m`, `(j₁, j₂) ↦ (m·j₁ + r·j₂) mod rm` is a bijection `[0,r) × [0,m) → [0,rm)`, as a statement about sums |
| `dftSum_pfa` | **Good–Thomas:** for coprime `r`, `m`, `dftSum fwd (r·m) x k = Σ_{j₁<r} ω_r^{j₁·(k mod r)} · dftSum fwd m (j₂ ↦ x((m·j₁ + r·j₂) mod rm)) (k mod m)`, with no twiddle factors |
| `pfaDFT_spec` | the prime factor algorithm `pfaDFT` over pairwise coprime blocks (each block by `symDFT`) is the DFT of size `bs.prod` |
| `bflySym_spec` | the symbolic butterfly is the DFT of its inputs for every `R > 0`: `mkPlan`/`exec` for powers of two, `pfaDFT` over the prime-power blocks of `R` when the generator's decidable check `PfaOK` passes (product `R`, positive, pairwise coprime), `symDFT` otherwise |

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

### The in-place schedule (`Proof/InPlace.lean`)

`inplaceWith A fwd N rs twOf x` (`Gen/InPlace.lean`) is the schedule the C engine's `LF_INPLACE`
mode runs: the leaf pass writes leaf `d`'s outputs at `digitRev(d)·R₀ + r` (mixed-radix digit
reversal), and every later pass rewrites its butterflies' positions in place. The proof carries
a layout invariant (`IPInv`) through the passes.

| Theorem | Statement |
|---|---|
| `ipLeaf_scatter` | position `digitRev L d · R₀ + r` after the leaf pass holds output `r` of the leaf DFT of `x[d + i·N/R₀]` (this is the address table the C executor now reads from Lean, `leafOffsets`) |
| `inplaceWith_eq_stockhamWith` | for any arithmetic `A`, positive radices with `N = ∏ rs`: `inplaceWith A fwd N rs twOf x = stockhamWith A fwd N rs twOf x`. Over binary64 the two schedules agree bit for bit |
| `inplaceWith_exact` | over the reals, the in-place schedule computes the DFT |

### The cost model as a CSLib query program (`Proof/Cost.lean`)

The Stockham schedule is also written as a program in CSLib's free-monad query framework
(`Cslib.Algorithms.Lean.Query`), whose queries are a kernel operation, a load and a store
(`EngineQ`). Evaluating it with the honest oracle gives the transform; counting its queries
with weights gives its cost. The planner ranks candidates by these counts.

| Theorem | Statement |
|---|---|
| `eval_stockhamQ` | `FreeM.eval (EngineQ.honest A) (stockhamQ fwd N rs twOf z) = stockhamWith A fwd N rs twOf z` |
| `cost_stockhamQ` | for every oracle, `FreeM.cost oracle (EngineQ.weight W) (stockhamQ …) = stockhamCost W fwd N rs`, the closed-form count (`Gen/OpCount.lean`) the planner computes |
| `stockhamQ_dft_and_cost` | over the reals with exact twiddles, the same program computes the DFT **and** costs `stockhamCost W fwd N rs` |

### The cost of the emitted code (`Proof/Ports.lean`)

A block of emitted instructions is a query program whose only query is "run this
instruction on this state" (`blockQ`). Three handlers give it its semantics, its checker
run and its cost, and the cost is proved to be a lower bound on the running time of the
block in a port model of the processor. [COST_MODEL.md](COST_MODEL.md) has the model, the
measurements against it and what it does not see.

| Theorem | Statement |
|---|---|
| `eval_blockQ_machine` | `FreeM.eval (machine M ad) (blockQ is s) = run M ad is s`: answered by the processor model, the program is the semantics of `Asm/Sem.lean` |
| `eval_blockQ_checker` | `FreeM.eval (checker cx) (blockQ is s) = s.bind (crun cx is)`: answered by the symbolic step, it is the run of the checker that `check_sound` is about |
| `cost_blockQ` | for every oracle, `FreeM.cost oracle uopWeight (blockQ is s) = portsOf is`: the cost is the vector of micro-operation counts by port class, whatever the data |
| `Schedule.bound_le` | every assignment of a list of micro-operations to cycles and ports they may use, with no port used twice in a cycle, takes at least `(Ports.ofList us).bound` cycles |
| `block_cycles_ge` | for a block `is`: `(portsOf is).bound ≤ T` for every `Schedule (uopsOf is) T` |

### The Lean-compiled backend (`Proof/Native.lean`)

`LeanFFTW.Native.exec p x` (`Native/Exec.lean`) is defined as `inplaceWith floatArith` of its
plan. The compiler runs generated straight-line Lean kernels instead (`@[implemented_by]`,
see [TRUST.md](TRUST.md)).

| Theorem | Statement |
|---|---|
| `exec_eq_refTransform` | for every plan `p` of the backend, `exec p x = refTransform p.fwd p.N p.rs x` |
| `execInto_eq_refTransform` | the same for the variant that writes into a caller's buffer |

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
  1-D complex sizes with a prime factor above 13, r2c/c2r, r2r, multi-dimensional and strided problems) has an
  exact-arithmetic algorithm proof (`exec_mkPlan_exact`) and a proof that its compiled
  fast form computes the same function (`execFloat_eq_fast`), but no floating-point bound, and
  the r2r/r2c embeddings (`Core/Problem.lean`) are not proved; they are validated by FFTW's
  own test harness.
* The accuracy of the twiddle generator (`Trig`) and of decimal constants (`τ`, `κ` above).
* The C code: see [TRUST.md](TRUST.md).
