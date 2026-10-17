# Semantic contract

Lean FFTW computes the same transforms as FFTW 3.3.10, with FFTW's conventions.
This file fixes what "correct" means, the supported domain, and what is excluded.
The coverage status of every item is tracked in [FFTW_INVENTORY.md](FFTW_INVENTORY.md).

## Transform semantics (FFTW conventions)

All transforms are **unnormalized**. For a complex array `x` of length `n`:

* Forward DFT (FFTW_FORWARD, sign −1):
  `Y[k] = Σ_{j=0}^{n-1} x[j] · exp(−2πi·j·k/n)`.
  In Lean this is Mathlib's independently defined `ZMod.dft` (`𝓕`, file
  `Mathlib/Analysis/Fourier/ZMod.lean`, by D. Loeffler), transported to `Fin n → ℂ`.
* Backward DFT (FFTW_BACKWARD, sign +1):
  `Y[k] = Σ_j x[j] · exp(+2πi·j·k/n)`, equal to `n · 𝓕⁻ x` (Mathlib's inverse DFT
  scaled by `n`).
* Multi-dimensional DFT of rank d with sizes n₁…n_d: the separable product of 1-D
  DFTs along every axis, row-major indexing as in FFTW.
* r2c (real input, forward): the forward DFT of a real array, returning the
  `⌊n_d/2⌋+1` non-redundant outputs of the last dimension. c2r (backward): the
  backward DFT of the Hermitian-symmetric array determined by those outputs;
  as in FFTW, the imaginary parts of the self-conjugate entries are ignored.
* r2r kinds R2HC, HC2R, DHT, REDFT00/01/10/11, RODFT00/01/10/11: the formulas in
  FFTW manual §4.8 ("What FFTW Really Computes"). They are implemented by reduction to a
  complex DFT (`embed`/`extract` in `LeanFFTW/Core/Problem.lean`); the formulas are not
  yet stated as Lean theorems, and these kinds are validated by FFTW's test harness
  (see [TRUST.md](TRUST.md)).

## Data layout and problem space

The problem space is FFTW's guru interface, as parsed by libbench2:
transform tensor (rank ≥ 0, each dimension `n`, input stride, output stride),
vector ("howmany") tensor of any rank, in-place or out-of-place, interleaved or
split real/imaginary storage, "destroy input allowed", element type `double`.

## Supported input domain and error cases

* Sizes: any `n ≥ 1` per dimension, total size fitting in `int` (FFTW's limit for
  the non-64 guru interface). Rank-0 transforms are copies, as in FFTW.
* Inputs: finite IEEE binary64 values. Behavior on NaN/Inf inputs is unspecified
  by FFTW and only "propagates non-finite values" here; the floating-point error
  theorem assumes finite inputs and no overflow (stated hypotheses).
* Planning fails (returns a null plan, `can_do` false) for unsupported problems;
  it never silently computes a different transform.
* As in FFTW, transform dimensions need `n ≥ 1` and REDFT00 needs `n ≥ 2`; a vector
  dimension of size 0 is allowed and makes the problem empty (nothing is read or written).

## Accuracy

* Exact-arithmetic semantics: the fast engine's schedule and the generic engine's
  mixed-radix algorithm are proved equal to the specification ([THEOREMS.md](THEOREMS.md)).
* Floating-point: each binary64 operation is modeled as IEEE round-to-nearest-even
  (FloatLib's binary64 model). For the fast engine's reference semantics the proved bound
  is stated in [THEOREMS.md](THEOREMS.md) with its hypotheses (finite values, no
  overflow, constant and twiddle accuracy); subnormals are covered. The generic engine
  has no proved floating-point bound.
* Empirical acceptance: libbench2 `--verify` tolerance, the same tolerance FFTW's
  own tests apply to FFTW.

## Exclusions (not part of the compatibility surface)

* FFTW's single, long-double and quad precision variants (`fftwf_`, `fftwl_`,
  `fftwq_`).
* MPI transforms, the Fortran API, and the wisdom file format (no wisdom
  import/export; Lean FFTW has its own planner).
* Multi-threaded execution is out of the primary scope; reported separately if
  added.
* Bit-for-bit identity with FFTW outputs is **not** a goal; agreement is within
  floating-point tolerance, as between any two FFTW plans.
