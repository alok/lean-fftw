# Results

Final run of the predeclared protocol ([BENCHMARK_PROTOCOL.md](BENCHMARK_PROTOCOL.md)),
2026-10-17. Data: [`results/clx-final/`](../results/clx-final) (`results.json` has every
timing, `raw/` has every process's output, `meta.json` has the environment, `summary.txt`
has the analysis printout).

![optimization history](../results/optimization.gif)

## Setup

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

## Primary result

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

## By iteration

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

## Accuracy

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

## Correctness of the benchmarked builds

* Differential test, bit for bit against the Lean reference `refTransform`
  (`csrc/test_fast.c`, `test_fast 14 18`): 3,726 plans, 0 mismatches.
* libbench2 `--verify` for `ocf`, `icf`, `ocb`, `icb` at N = 1…2^18: 76 of 76 pass.
* FFTW's `check.pl` (random problems over the guru interface): 434 of 434 pass. For the
  bigcheck enumeration, see [FFTW_INVENTORY.md](FFTW_INVENTORY.md).

The library after the benchmark differs from i6 only in the generic engine. Bigcheck
found that empty vector dimensions (`n = 0`) were rejected, and FFTW accepts them as empty
problems. The fix does not touch the fast engine's code or the benchmarked path.
