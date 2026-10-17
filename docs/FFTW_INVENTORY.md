# FFTW 3.3.10 feature and test inventory

This is the complete surface of FFTW 3.3.10 (source: Ubuntu archive
`fftw3_3.3.10.orig.tar.gz`, sha256 `5499874012aa6ea6c597b8c3807494e271ab2426a889e95d5cc4d154b825e8a0`)
and, for each item, whether Lean FFTW covers it. "Covered" means implemented and passing
FFTW's own test harness (libbench2 `--verify` driven by `tests/check.pl`). Nothing here
calls FFTW: FFTW is only built as a competitor and as the source of the test harness.

## Declared compatibility surface

Lean FFTW's compatibility surface is **FFTW's double-precision transform semantics as
exposed by the guru interface**, exercised through libbench2 (the harness FFTW's
`make check` uses):

| Area | FFTW | Lean FFTW | Engine |
|---|---|---|---|
| Complex DFT, both signs, unnormalized | yes | **yes** | fast (1-D, 2^k, unit stride, vrank 0) / generic (all) |
| r2c / c2r ("rdft2"), any rank | yes | **yes** | generic |
| r2r: R2HC, HC2R, DHT, REDFT00/01/10/11, RODFT00/01/10/11 | yes | **yes**, all 11 | generic |
| Any rank (incl. rank 0), any vector rank, any strides (incl. negative) | yes | **yes** | generic |
| In-place / out-of-place | yes | **yes** | both |
| Split (separate re/im) arrays | yes | **yes** | generic |
| Interleaved complex | yes | **yes** | both |
| `FFTW_DESTROY_INPUT` problems (`d` prefix) | yes | **yes** (input preserved, which is allowed) | generic |
| Arbitrary sizes (any prime factors) | yes | **yes** (generic: direct DFT on primes) | generic |

## Outside the surface (not implemented; reported, not hidden)

| FFTW feature | Status |
|---|---|
| `float`, `long double`, `__float128` precisions (`fftwf_`, `fftwl_`, `fftwq_`) | not implemented |
| The `fftw3.h` C API itself (`fftw_plan_dft_1d`, guru64, new-array execute, `fftw_malloc`, …) | **not yet**: planned as a shim so FFTW's own `tests/bench` can link against Lean FFTW unchanged |
| Planner flags ESTIMATE / MEASURE / PATIENT / EXHAUSTIVE / WISDOM_ONLY, time limits | Lean FFTW's fast planner always measures; flags not modeled |
| Wisdom (export/import/forget, system wisdom, `fftw-wisdom`, `fftw-wisdom-to-conf`) | not implemented |
| Threads (pthreads, OpenMP, `fftw_plan_with_nthreads`) | not implemented (benchmark is single-threaded by protocol) |
| MPI distributed transforms (`fftw_mpi_*`) | not implemented |
| Fortran interfaces (legacy f77 and Fortran 2003) | not implemented |
| `fftw_flops`, `fftw_cost`, `fftw_print_plan`, `fftw_sprint_plan` | not implemented |
| SIMD back ends other than AVX2/AVX-512 (SSE2, AVX, KCVI, AltiVec, VSX, NEON) | not implemented; the generic engine is portable |
| Bit-identical results with FFTW | not a goal (different algorithms); accuracy is compared instead |

## FFTW's tests

| Test | What it checks | Applicable | Result |
|---|---|---|---|
| `tests/check.pl` (`make check`: `-r -c=30 -v`) | random problems over the whole guru space, libbench2 `--verify` (linearity, impulse, time-shift tests) | yes | **pass**: 434 problems, 0 failures (`results/checklocal-generic.log`, seed `srand(1)`) |
| `check.pl -a` (bigcheck) | exhaustive enumeration of problem shapes | yes | **pass**: 50,702 of 50,702 doable problems verify and all 30 must-be-undoable problems are rejected (seed 20261016; `tools/bigcheck.py`, `results/bigcheck/`). The first attempt found that empty vector dimensions (`n = 0`) were rejected; FFTW accepts them, and the generic planner was fixed before the run that is reported |
| `check.pl --validate-wisdom` | wisdom round trip | no (no wisdom) | n/a |
| threads checks (`--threads`, `-onthreads=`) | multithreaded plans | no (no threads) | n/a |
| MPI tests (`mpi/`) | distributed transforms | no | n/a |
| libbench2 `--accuracy` | error vs multiple-precision FFT | yes | reported per benchmark size |
| libbench2 `--can-do` for undoable problems | rejection of invalid problems (e.g. REDFT00 with n = 1) | yes | must print `#f` |

### Bigcheck problem classification

`tools/classify_problems.py` over the bigcheck enumeration (50,702 doable problems):

* kind: complex 28,394; rdft2 19,218; r2r 3,090
* rank: 1 → 7,756; 2 → 42,212; 3 → 330; 4 → 404
* vector rank: 0 → 44,016; 1 → 906; 3 → 5,780
* layout: split 19,218; in-place 22,336; destroy-input 578; explicit strides 5,780
* sizes with a prime factor > 13: 18,192

## Staged plan

1. Generic engine over the full double-precision surface, pure Lean (done; passes check.pl).
2. Fast engine for the benchmark workload: 1-D complex power-of-two, generated SIMD kernels (done; bit-exact against Lean reference; under optimization).
3. Fast engine coverage: vector rank 1, non-unit strides, mixed radices 3/5/7, Bluestein for large primes, multi-dimensional, r2c/c2r.
4. `fftw3.h` API shim (double precision) so FFTW's own `tests/bench` links against Lean FFTW.
5. Optional: wisdom, threads, other precisions.
