# Results

Two runs of the predeclared protocol ([BENCHMARK_PROTOCOL.md](BENCHMARK_PROTOCOL.md)) are
reported. The machine is a cloud VM whose CPU changed when the container was
re-provisioned (amendments 1 and 3), so each run re-measures every iteration and every
competitor on one machine, and numbers are only compared within a run.

* **Current: Sapphire Rapids, i0–i7** (2026-10-17, [`results/spr-i7/`](../results/spr-i7)).
* Earlier: Cascade Lake, i0–i6 (2026-10-17, [`results/clx-final/`](../results/clx-final)),
  below.

![optimization history](../results/optimization.gif)

## Current run: Sapphire Rapids

### Setup

* Machine: KVM guest, Intel Xeon @ 2.10 GHz (family 6 model 207, Sapphire Rapids),
  4 vCPUs, AVX-512, L2 2 MiB per core. Linux 6.18, gcc 13.3.
* Everything else as in the earlier run: every process pinned to CPU 0, one thread,
  workload `ocf<N>` for N = 2…2^18, 12 implementations × 18 sizes × 10 process runs in
  shuffled order (2,160 runs, all exit 0), median over runs of libbench2's minimum of 8
  timings. FFTW wisdom was generated from scratch on this CPU for each mode.

### Primary result

**G = time(Lean FFTW i7) / time(FFTW, best mode per size), geometric mean over the 18
sizes: 0.809, 95% bootstrap CI [0.795, 0.868].** The success criterion (upper end of the
CI ≤ 0.90) is met on this CPU too. Geometric-mean times: Lean FFTW i7 0.93 µs, FFTW best
mode 1.15 µs, MKL 1.63 µs. Against the per-size best of all four competitor
configurations, G = 0.819.

| N | Lean i7 | FFTW best | ratio | | N | Lean i7 | FFTW best | ratio |
|---|---|---|---|---|---|---|---|---|
| 2 | 1.47 ns | 5.64 ns | 0.26 | | 1024 | 1.22 µs | 1.18 µs | 1.04 |
| 4 | 1.7 ns | 5.7 ns | 0.30 | | 2048 | 2.95 µs | 2.77 µs | 1.07 |
| 8 | 3.04 ns | 6.32 ns | 0.48 | | 4096 | 8.34 µs | 7.26 µs | 1.15 |
| 16 | 6.04 ns | 12.8 ns | 0.47 | | 8192 | 18.6 µs | 17 µs | 1.09 |
| 32 | 17.8 ns | 29.6 ns | 0.60 | | 16384 | 40.6 µs | 36.9 µs | 1.10 |
| 64 | 41.2 ns | 51.7 ns | 0.80 | | 32768 | 86.9 µs | 91.9 µs | 0.95 |
| 128 | 95.1 ns | 106 ns | 0.90 | | 65536 | 279 µs | 236 µs | 1.19 |
| 256 | 232 ns | 228 ns | 1.02 | | 131072 | 805 µs | 590 µs | 1.36 |
| 512 | 524 ns | 482 ns | 1.09 | | 262144 | 1.61 ms | 1.44 ms | 1.12 |

The whole margin comes from small sizes. On this CPU Lean FFTW is faster than FFTW for
N ≤ 128 and slower from N = 256 on, except at N = 32768. **For N ≥ 1024 alone the
geometric-mean ratio is 1.11, so FFTW is 11% faster there.** On Cascade Lake the same
ratio was 0.94. At N ≥ 2^15 a fixed plan's time varies by ±20% between processes on this
VM, so those per-size ratios are the least certain.

### By iteration

G against FFTW's best mode, from the same run:

| Iteration | G | 95% CI | N ≥ 1024 only |
|---|---|---|---|
| i0 baseline | 1.263 | [1.249, 1.362] | 1.526 |
| i1 fused small transforms, in-place schedule | 1.032 | [1.012, 1.110] | 1.134 |
| i2 FMA contraction | 1.032 | [1.012, 1.103] | 1.147 |
| i3 interleaved kernels for small N | 0.951 | [0.935, 1.034] | 1.098 |
| i4 measuring planner, cache blocking | 0.941 | [0.919, 1.005] | 1.124 |
| i5 two-pass interleaved kernels, vectorizer | 0.896 | [0.876, 0.965] | 1.124 |
| i6 direct kernel dispatch, planning on the real arrays | 0.818 | [0.801, 0.876] | 1.102 |
| **i7** proved tan-factored twiddles | **0.809** | **[0.795, 0.868]** | **1.113** |
| *for reference:* MKL | 1.417 | [1.396, 1.523] | 1.304 |
| FFTW MEASURE only | 1.133 | [1.115, 1.218] | 1.189 |
| FFTW PATIENT only | 1.026 | [1.011, 1.115] | 1.025 |
| FFTW EXHAUSTIVE only | 1.067 | [1.033, 1.145] | 1.079 |

i7 against i6 directly: G = 0.990, 95% CI [0.949, 1.037]. The kernel change removes 5% of
the operations of the radix-16 kernels and 9% of the radix-32 kernels, but it makes no
difference to the benchmark that this run can detect. The planner mostly picks radix 4
and 8 passes, which did not change, and the sizes where radix 16/32 are used are the
memory-bound ones. See i7 in [ITERATIONS.md](ITERATIONS.md).

Planning time (medians, not part of G): Lean FFTW 0.013 s at N = 2, 0.34 s at N = 1024 and
25 s at N = 2^18; FFTW from wisdom 2.5 ms or less.

### Accuracy

Accuracy of the i7 kernels: being measured (libbench2 `--accuracy`, as in the earlier run).

### Non-power-of-two sizes (generic engine)

Secondary workload, `ocf<N>` for N = 6, 15, 80, 210, 1000, 4725, 10368: 5 process runs
each, same method ([`results/spr-nonpow2/`](../results/spr-nonpow2)). These sizes run in
the pure-Lean generic engine. In i7 its compiled code is the `@[csimp]` fast executor
(`execFloat_eq_fast`).

| N | Lean i6 | Lean i7 | FFTW MEASURE | i7 / FFTW |
|---|---|---|---|---|
| 6 | 5.1 µs | 3.1 µs | 6.35 ns | 490 |
| 15 | 15.2 µs | 5.87 µs | 20.0 ns | 290 |
| 80 | 122 µs | 43.8 µs | 78.9 ns | 550 |
| 210 | 320 µs | 117 µs | 408 ns | 290 |
| 1000 | 2.43 ms | 505 µs | 1.84 µs | 270 |
| 4725 | 9.98 ms | 3.03 ms | 20.2 µs | 150 |
| 10368 | 22.9 ms | 8.58 ms | 25.7 µs | 330 |

i7 is 2.8× faster than i6 on these sizes (geometric mean; CI [2.5, 3.2]). It is still
about 300× slower than FFTW, because the generic engine evaluates each Cooley–Tukey step
as a full sum (`O(n · Σ factors)` complex multiply-adds) in scalar Lean. Making these
sizes fast means running them through the C engine with generated radix-3/5/7 kernels,
which has not been done.

### Correctness of the benchmarked build

* Differential test against the Lean reference (`test_fast 14 18`): 3,726 plans, 0
  mismatches.
* libbench2 `--verify`: `ocf` at all 18 primary sizes and `icf`, `ocb`, `icb` at 9 of
  them pass.
* FFTW's bigcheck enumeration on the i7 library: running.

## Earlier run: Cascade Lake (i0–i6)

Data: [`results/clx-final/`](../results/clx-final). GIF:
[`results/optimization-clx.gif`](../results/optimization-clx.gif).

### Setup

* Machine: KVM guest, Intel Xeon @ 2.80 GHz (family 6 model 85, Cascade Lake), 4 vCPUs,
  AVX-512, L2 1 MiB per core, L3 33 MiB shared. Linux 6.18, gcc 13.3.
* Every process pinned to CPU 0 (`taskset -c 0`); one thread everywhere; nothing else
  heavy ran during the run.
* Workload: `ocf<N>`: 1-D complex double, forward, out of place, N = 2…2^18 (18 sizes).
* 11 implementations × 18 sizes × 10 process runs, in an order shuffled per round
  (1,980 runs, all exit 0). libbench2 reports the minimum of 8 timings per process run;
  the statistic per size is the median over the 10 runs.
* Competitors: FFTW 3.3.10 (built from source with SSE2/AVX/AVX2/AVX-512/FMA; MEASURE,
  PATIENT and EXHAUSTIVE, wisdom generated on this CPU) and Intel MKL 2026.2
  (sequential). The Lean FFTW iterations i0–i6 are the binaries recorded in
  [ITERATIONS.md](ITERATIONS.md).

### Primary result

**G = time(Lean FFTW i6) / time(FFTW, best mode per size), geometric mean over the 18
sizes: 0.748, 95% bootstrap CI [0.739, 0.760].** The success criterion (upper end of the
CI ≤ 0.90) is met. FFTW is the strongest competitor (geometric-mean time: FFTW best mode
1.74 µs, MKL 2.46 µs; Lean FFTW i6 1.30 µs). Against the per-size best of all four
competitor configurations, G = 0.755 [0.747, 0.768].

| N | Lean i6 | FFTW best | ratio | | N | Lean i6 | FFTW best | ratio |
|---|---|---|---|---|---|---|---|---|
| 2 | 2.73 ns | 6.08 ns | 0.45 | | 1024 | 1.83 µs | 1.94 µs | 0.94 |
| 4 | 3.33 ns | 7.28 ns | 0.46 | | 2048 | 4.32 µs | 4.73 µs | 0.91 |
| 8 | 5.29 ns | 11.4 ns | 0.46 | | 4096 | 10.0 µs | 11.3 µs | 0.89 |
| 16 | 11.5 ns | 21.2 ns | 0.54 | | 8192 | 22.6 µs | 25.5 µs | 0.89 |
| 32 | 25.0 ns | 48.9 ns | 0.51 | | 16384 | 49.8 µs | 54.5 µs | 0.91 |
| 64 | 51.3 ns | 84.4 ns | 0.61 | | 32768 | 135 µs | 137 µs | 0.98 |
| 128 | 119 ns | 158 ns | 0.75 | | 65536 | 325 µs | 338 µs | 0.96 |
| 256 | 272 ns | 340 ns | 0.80 | | 131072 | 761 µs | 801 µs | 0.95 |
| 512 | 737 ns | 749 ns | 0.98 | | 262144 | 2.21 ms | 2.20 ms | **1.01** |

How the margin is distributed: most of it comes from N ≤ 256, where whole transforms
are single generated kernels. For N ≥ 1024 alone, the geometric-mean ratio is 0.94.
N = 2^18 is at parity (1.01; Lean FFTW is slower there by 0.7%). At N ≥ 2^15 a single
plan's time varies by ±20% between processes on this machine (see i6 in
ITERATIONS.md), so those per-size ratios are the least certain.

### By iteration

G against FFTW's best mode, from the same run:

| Iteration | G | 95% CI | N ≥ 1024 only |
|---|---|---|---|
| i0 baseline | 1.303 | [1.292, 1.320] | 1.486 |
| i1 fused small transforms, in-place schedule | 0.950 | [0.942, 0.965] | 0.988 |
| i2 FMA contraction | 0.963 | [0.952, 0.973] | 0.997 |
| i3 interleaved kernels for small N | 0.883 | [0.875, 0.896] | 0.985 |
| i4 measuring planner, cache blocking | 0.853 | [0.846, 0.864] | 0.954 |
| i5 two-pass interleaved kernels, vectorizer | 0.832 | [0.821, 0.853] | 0.960 |
| **i6** direct kernel dispatch, planning on the real arrays | **0.748** | **[0.739, 0.760]** | **0.938** |
| *for reference:* MKL | 1.414 | [1.401, 1.433] | 1.183 |
| FFTW MEASURE only | 1.076 | [1.069, 1.086] | 1.129 |
| FFTW PATIENT only | 1.027 | [1.016, 1.038] | 1.035 |
| FFTW EXHAUSTIVE only | 1.012 | [1.003, 1.023] | 1.020 |

i2 is slightly slower than i1 on this CPU; it was tuned on the earlier machine (see
the hardware note in ITERATIONS.md). The baseline measured on that earlier machine
(Sapphire Rapids, [`results/i0-baseline`](../results/i0-baseline)) was G = 1.252
[1.248, 1.267].

Planning time is reported separately, as the protocol requires, and is not part of G.
Lean FFTW has no wisdom: its planner measures every candidate plan on every run, which
takes 0.014 s at N = 2, 0.35 s at N = 1024 and about 40 s at N = 2^18 (medians). FFTW
planned from wisdom it had accumulated on this CPU, which takes 5 µs to 9 ms. So Lean FFTW
is far more expensive to plan, which matters for programs that plan often.

### Accuracy

libbench2 `--accuracy` (10 random inputs per size, against libbench2's
multiple-precision FFT), forward relative L2 error. Data:
[`results/clx-final/accuracy.json`](../results/clx-final/accuracy.json).

| N | Lean i6 | FFTW (measure / patient / exhaustive) | MKL |
|---|---|---|---|
| 8 | 6.3e-17 | 7.1e-17 / 7.1e-17 / 7.1e-17 | 5.6e-17 |
| 64 | 1.2e-16 | 1.3e-16 / 1.3e-16 / 1.2e-16 | 1.2e-16 |
| 1024 | 1.8e-16 | 1.9e-16 / 1.8e-16 / 1.9e-16 | 1.8e-16 |
| 16384 | 2.3e-16 | 2.2e-16 / 2.2e-16 / 2.3e-16 | 2.3e-16 |
| 262144 | 2.8e-16 | 2.8e-16 / 2.7e-16 / 2.7e-16 | 3.7e-16 |

At every one of the 18 sizes, Lean FFTW's error is at most 1.07× the lowest of the three
FFTW modes; the protocol's limit is 2×. N = 2 and 4 are exact or nearly so for all
implementations.

### Correctness of the benchmarked builds

* Differential test, bit for bit against the Lean reference `refTransform`
  (`csrc/test_fast.c`, `test_fast 14 18`): 3,726 plans, 0 mismatches.
* libbench2 `--verify` for `ocf`, `icf`, `ocb`, `icb` at N = 1…2^18: 76 of 76 pass.
* FFTW's `check.pl` (random problems over the guru interface): 434 of 434 pass.
* FFTW's bigcheck enumeration (`check.pl -a`), on the final library: 50,702 of 50,702
  problems pass `--verify`, and all 30 problems that must be rejected are rejected.

The library after the benchmark differs from i6 only in the generic engine. Bigcheck
found that empty vector dimensions (`n = 0`) were rejected, and FFTW accepts them as empty
problems. The fix does not touch the fast engine's code or the benchmarked path.
