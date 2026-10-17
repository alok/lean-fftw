# Benchmark protocol (predeclared)

This file was written and committed **before any optimization of Lean FFTW** and
before any Lean FFTW timing existed. Later changes to it are visible in git history;
any change after the first optimized iteration is recorded in the
"Amendments" section with its reason, and results are reported under both the
original and amended protocol.

## Harness

* **libbench2** from the FFTW 3.3.10 release (the harness shared by FFTW's test
  suite and by benchFFT). Every implementation, including Lean FFTW, is linked as a
  libbench2 *backend* (`can_do` / `setup` / `doit` / `done`), so problem parsing,
  allocation, timing and reporting are identical across implementations.
* Speed mode: `bench -s <problem>` with libbench2 defaults: setup (planning) is
  timed once and reported separately; the timed work is `doit(iter, p)` with an
  iteration count doubled until one measurement takes at least `time_min` = 10 ms;
  8 such measurements are taken and libbench2 reports their minimum (benchFFT
  convention). Inputs are zeroed by libbench2 after setup for every implementation.
* Raw output of every process run is stored under `results/raw/`.

## Primary workload

benchFFT's standard **1D, double-precision, complex, power-of-two** set:

* problems `ocf<N>`: out-of-place, forward (sign −1, FFTW_FORWARD), unnormalized,
  interleaved complex, unit stride, single transform;
* N = 2^k for k = 1..18 (2 … 262144), i.e. 18 sizes;
* one thread for every implementation.

## Primary metric and aggregation

* Per process run r and size N: t_r(N) = libbench2's reported time per transform
  (minimum of 8 measurements).
* R = 10 process runs per (implementation, size), interleaved across
  implementations and sizes (round-robin) to spread machine drift.
* Per-size statistic: T(N) = median over runs of t_r(N).
* Primary metric: **elapsed time** (lower is better).
* Aggregate: G = geometric mean over the 18 sizes of T_lean(N) / T_comp(N).
* Uncertainty: 95% percentile bootstrap CI of G (10,000 resamples; each resample
  draws R runs with replacement independently per implementation and size,
  recomputes medians and the geometric mean).
* **Success criterion:** upper end of the 95% CI of G ≤ 0.90 against the strongest
  verified competitor (below). Per-size ratios, sizes where Lean FFTW is slower,
  and the comparison against the per-size best of all competitors are always
  reported alongside.

## Competitor selection

* Candidates are run on the same machine, same harness, same problem strings,
  one thread. A competitor is *verified compatible* if its backend passes
  libbench2 `--verify` on every primary problem (same semantics: unnormalized
  forward DFT, sign −1, interleaved complex double).
* The **strongest competitor** is the verified candidate with the lowest
  geometric-mean T over the 18 primary sizes (measured with this protocol).
  FFTW is always included and reported even if it is not the strongest.
* FFTW is measured with its best planner effort: for each size the faster of
  `FFTW_MEASURE`, `FFTW_PATIENT` and `FFTW_EXHAUSTIVE` (planning time excluded
  from timed work but reported). MKL with the sequential threading layer.

## Accuracy constraint

* Every timed Lean FFTW build must pass libbench2 `--verify` on all primary problems
  and on the regression suite.
* libbench2 `--accuracy` (against libbench2's multiple-precision reference FFT)
  is reported per size for every implementation; Lean FFTW's L2 relative error
  must be no worse than 2× FFTW's at every primary size.
* The proved floating-point error bound (see docs/THEOREMS.md) must cover the
  benchmarked code path.

## Secondary workloads (reported, not used for the success criterion)

* In-place forward `icf<N>` and backward `ocb<N>` for the same sizes.
* benchFFT non-power-of-two sizes: 6, 9, 12, 15, 18, 24, 36, 80, 108, 210, 504,
  1000, 1960, 4725, 10368, 27000, 75600, 165375.
* 2D complex power-of-two (`ocf<N>x<N>`) and 1D r2c when supported.

## Environment recording

Each results file records: CPU model and flags (`lscpu`), kernel, compiler
versions and flags, library versions/commits, the Lean toolchain, the lean-fftw
commit, environment variables affecting threading (`MKL_THREADING_LAYER`,
`OMP_NUM_THREADS`), and the date.

## Amendments

1. *2026-10-17, before the final run.* The cloud machine changed between iterations i4 and
   i5 (Sapphire Rapids, 2.1 GHz → Cascade Lake, 2.8 GHz; the container was re-provisioned).
   No protocol rule changes: the final run re-measures **every** iteration binary (i0–i5),
   FFTW in all three planner modes (with wisdom regenerated on the new CPU) and MKL on the
   same machine in one interleaved run, so all comparisons stay within one machine. The
   i0 baseline run on Sapphire Rapids is kept and reported separately.
2. *2026-10-17, measurement hygiene only.* The whole run is pinned to one CPU
   (`taskset -c 0`) for every implementation, and no other heavy work runs on the machine
   during it. This applies equally to all implementations and does not change the metric.
3. *2026-10-17, after the first final run, before measuring i7.* The machine changed back
   to Sapphire Rapids (family 6 model 207, 2.1 GHz) when the container was re-provisioned,
   and a further iteration (i7) was added. No protocol rule changes: as in amendment 1, a
   new run re-measures every iteration binary (i0–i7), FFTW in all three modes with wisdom
   generated from scratch on this CPU, and MKL, in one interleaved run on one machine. The
   Cascade Lake run (`results/clx-final`) stays in the repository as the earlier result.
