# Independent reproduction (2026-11-04)

> **Historical.** This document describes the library as of the date in its title, when
> the fast engine was C printed by Lean (`csrc/`, `tools/c/`). That engine was removed on
> 2026-11-10 in favour of assembly written by Lean (`LeanFFTW/Asm`); the files named here
> are in the history up to commit `7cc9489`. See [TRUST.md](TRUST.md) for the current state.

The claims in the README were re-checked from scratch on a fresh machine of the same CPU
model, with a separately built FFTW, and with a second benchmark harness that shares no
code with libbench2. The data is in
[`results/repro-2026-11-04/`](../results/repro-2026-11-04). This is the summary, including
the parts that did not reproduce.

## Verdict

| Claim (README at `b00286e`) | Reproduced? |
|---|---|
| Speed: 0.750× FFTW's best mode, CI [0.744, 0.765] | **Partly.** The protocol rerun gives **0.828×, CI [0.815, 0.853]**. That still meets the predeclared target (≤ 0.90), but it is a smaller win than the repo's figure. |
| "Also faster for N ≥ 1024 (0.93)" | **No.** In the rerun Lean FFTW is **1.03×** FFTW for N ≥ 1024 and **slower at every size from 4096 to 2^18** (1.02–1.09×). The independent harness puts large sizes at 0.94–0.97×. Treat large sizes as parity, not a win. |
| The margin comes mostly from small sizes | **Yes.** N ≤ 16: 0.49×. N ≥ 64: 0.99×. |
| 13-smooth sizes at parity (0.97, CI [0.95, 1.04], 7 sizes up to 10368) | **Yes on those sizes** (0.99 in the rerun). Over all 18 benchFFT 13-smooth sizes up to 165375, which the repo had not measured against FFTW, the rerun gives **1.04×, CI [1.03, 1.09]**. Per size it ranges from 0.49× (N = 6) to 1.74× (N = 75600). |
| Accuracy within 1.08× of FFTW's L2 error | **Yes.** libbench2 `--accuracy`: ≤ 1.04× at every primary size. |
| C kernels are what the proved generator prints | **Yes.** Regenerated `csrc/lf_kernels_gen.c` is byte-identical to the committed file. |
| C engine bit-for-bit equal to the proved reference | **Yes.** `test_fast 14 18`: 3,726 plans, 0 failures. `test_fast mixed 300` plus the 18 benchFFT 13-smooth sizes: 8,756 plans checked, 0 failures. That run was still going at N = 75600 when this was committed (`test_fast-mixed-partial.txt`). New: the plan the planner actually picks is bit-exact at all 36 benchmark sizes, in and out of place (see the harness below). |
| libbench2 `--verify` passes | **Yes**, on all 108 problems tried (ocf/icf/ocb/ibf at every power of two, ocf/icf/ocb at the 18 secondary sizes). |
| No `sorry`, standard axioms only | **Yes.** `lake build` succeeds (3,741 jobs, Mathlib compiled from source), and all 32 audited theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. |
| MKL slower than both | **Not checked.** MKL was not installed on the reproduction machine. |

So the defensible headline is: **much faster than FFTW on small transforms (about 2× at
N ≤ 16), at parity from N = 256 up, and a geometric mean of about 0.83× over the benchFFT
power-of-two sizes.**

## Setup

* Sapphire Rapids, family 6 model 207, 2.1 GHz, 4 vCPUs (KVM), the same model as the
  repo's `spr-i9` run. Every timed process was pinned to CPU 0 (`taskset -c 0`). The
  long Mathlib build and the bit-exact tests were paused with `SIGSTOP` for the whole timed
  session, so nothing else ran on the machine.
* FFTW 3.3.10 (`fftw3_3.3.10.orig.tar.gz`, sha256 `5499874…e8a0`, the same tarball as the
  inventory), built here with
  `./configure --enable-sse2 --enable-avx --enable-avx2 --enable-avx512 --enable-fma`,
  gcc 13.3, FFTW's default `CFLAGS` (`-O3 -fomit-frame-pointer -mtune=native …`).
  Wisdom was generated **from scratch on this machine** for each planner mode, for every
  benchmarked size. None of the repo's wisdom files was reused.
* Lean FFTW at `b00286e` (i9), built with `scripts/build.sh`.

## 1. Protocol rerun (libbench2)

`tools/bench.py run`, 10 shuffled process runs per (implementation, size). The
implementations are Lean FFTW and FFTW in MEASURE, PATIENT and EXHAUSTIVE. All 720 + 720
runs exited 0. As in the repo, "FFTW" is the per-size **minimum** of the three modes'
medians, which slightly favours FFTW.

Primary workload `ocf<N>`, N = 2…2^18:

| N | Lean | FFTW best | ratio | | N | Lean | FFTW best | ratio |
|---|---|---|---|---|---|---|---|---|
| 2 | 1.64 ns | 3.60 ns | 0.46 | | 1024 | 1.05 µs | 1.03 µs | 1.02 |
| 4 | 1.90 ns | 4.25 ns | 0.45 | | 2048 | 2.67 µs | 2.85 µs | 0.94 |
| 8 | 3.16 ns | 6.14 ns | 0.51 | | 4096 | 7.11 µs | 6.99 µs | 1.02 |
| 16 | 6.86 ns | 12.8 ns | 0.54 | | 8192 | 15.7 µs | 15.1 µs | 1.04 |
| 32 | 18.1 ns | 27.7 ns | 0.65 | | 16384 | 33.5 µs | 32.4 µs | 1.04 |
| 64 | 39.2 ns | 50.4 ns | 0.78 | | 32768 | 83.2 µs | 78.1 µs | 1.07 |
| 128 | 84.3 ns | 99.1 ns | 0.85 | | 65536 | 212 µs | 194 µs | 1.09 |
| 256 | 193 ns | 195 ns | 0.99 | | 131072 | 509 µs | 490 µs | 1.04 |
| 512 | 450 ns | 426 ns | 1.06 | | 262144 | 1.15 ms | 1.09 ms | 1.06 |

**G = 0.828, 95% bootstrap CI [0.815, 0.853]**. Against each mode alone: MEASURE 0.757,
PATIENT 0.803, EXHAUSTIVE 0.770. By band: N ≤ 16 0.487, N ≥ 64 0.994, N ≥ 1024 1.032.

The FFTW built here is faster than the one in the repo's `spr-i9` run at nearly every size,
for example 3.6 ns against 6.3 ns at N = 2 and 1.09 ms against 1.47 ms at N = 2^18. Lean FFTW
is also a little faster here, but by less. The difference is most likely the FFTW build or
the host (same CPU model, different VM), and it cannot be settled from the recorded
metadata, because the repo does not record FFTW's configure line or compiler flags. Future
runs should record them (see Recommendations).

Secondary workload `ocf<N>` at all 18 benchFFT 13-smooth sizes: **G = 1.042, CI [1.026,
1.085]**. On the repo's seven sizes (6, 15, 80, 210, 1000, 4725, 10368) it is 0.986. Lean FFTW is faster at 6–24, 504 and 1960, and slower at 36, 80, 108, 210, 1000, 4725,
10368 and 27000–165375. Its worst size is N = 75600 (0.42 ms against 0.24 ms).

## 2. Independent harness (`tools/c/xcheck.c`)

This harness does not use libbench2. It links Lean FFTW and FFTW into one process. Both
plan on their own arrays: Lean FFTW with its measuring planner, FFTW with
`fftw_plan_dft_1d` in PATIENT or EXHAUSTIVE mode (importing the wisdom from the runs
above). It then times both on the **same random input** (not zeros), in 21 interleaved
rounds of ≥ 10 ms blocks, and reports the median ratio. For each size it also checks:

* the **plan the planner actually chose** against the proved Lean reference
  (`refTransform` with the same radices), with `memcmp`, out of place and in place;
* both outputs against a long-double FFTW (`fftwl`, no SIMD, about 19 digits).

Results (`xcheck-patient.jsonl`, `xcheck-exhaustive.jsonl`, `xcheck-bits.jsonl`):

* **Bit-exact: all 36 sizes × both placements × 3 runs, 0 mismatches.**
* Speed against PATIENT / EXHAUSTIVE: powers of two **0.79 / 0.76**. N ≤ 16 0.47 / 0.47.
  N ≥ 64 0.96 / 0.90. N ≥ 1024 0.97 / 0.94. 13-smooth sizes 0.99 / 0.97.
  This harness compares against one FFTW mode at a time, not the per-size minimum of three,
  so it is a little kinder to Lean FFTW than the protocol is. It agrees with the protocol
  that the gain is concentrated at small N and that large sizes are about even.
* Relative L2 error against `fftwl`: Lean FFTW and FFTW agree within a factor of 1.6 at
  every size, and both are ≤ 3.1 × 10⁻¹⁶.

## 3. The hypotheses of the error theorem, measured

`refTransform_error` assumes, without proving, that the twiddle tables are accurate to `τ`
and the kernel constants to `κ`. Both were measured:

* **τ** (`tools/c/twcheck.c`, every base table of all 36 sizes, both directions, against
  long-double `cos`/`sin`): max absolute error **5.57 × 10⁻¹⁷ = 0.502 ulp of 1**
  (`twiddles.jsonl`).
* **κ** (`scripts/ErrorBound.lean consts 64` dumps all 237 distinct constants of every
  kernel `butterflyK fwd R tw` with R ≤ 64; `tools/kappa.py` compares them with a 200-bit
  reference): max relative error **1.05 × 10⁻¹⁶ = 0.945 u**, at `tan(2π·16/400)`. The
  constants are within one ulp but are not all correctly rounded (`kernel-constants.txt`).

## 4. The proved error bound, evaluated

`scripts/ErrorBound.lean bound N R…` evaluates the right-hand side of
`refTransform_error_depth` for a concrete plan: the rounding and constant depths `(a, b)`
from `depthArith` (exact), and the magnitude bound `magArith` on an all-ones input (a bound
for every input with |re|, |im| ≤ 1). With `t = max τ κ = 1.05 × 10⁻¹⁶`, the theorem gives
a **worst-case absolute error bound for every output and every input in that box**. The
table compares it with the largest error observed on one random input
(`bounds-table.txt`):

| N | plan | (a, b) | proved bound | observed | ratio |
|---|---|---|---|---|---|
| 16 | 4×4 | (6, 2) | 2.5 × 10⁻¹⁴ | 4.9 × 10⁻¹⁶ | 50 |
| 1024 | 8×8×8×2 | (19, 7) | 2.8 × 10⁻¹¹ | 1.6 × 10⁻¹⁴ | 1.7 × 10³ |
| 65536 | 8×4×4×8×8×8 | (30, 10) | 1.3 × 10⁻⁸ | 2.0 × 10⁻¹³ | 6.3 × 10⁴ |
| 262144 | 8×16×8×8×8×4 | (34, 13) | 9.3 × 10⁻⁸ | 4.9 × 10⁻¹³ | 1.9 × 10⁵ |
| 75600 | 16×3×5×5×7×9 | (40, 17) | 6.6 × 10⁻⁸ | 2.5 × 10⁻¹³ | 2.6 × 10⁵ |

The bound holds everywhere, which it must, since it is a theorem. But it is **loose**:
by 18× at N = 4, and by up to 2.6 × 10⁵ at the largest sizes. It is a worst-case
componentwise bound in which magnitudes add at every operation, so `magArith` grows faster
than N (35 × 2N at N = 2^18). It is good for "the error is bounded, explicitly, by a
theorem". It is not good for "the error is as small as FFTW's". That second claim rests on
the measurements (libbench2 `--accuracy`, `fftwl`), not on the theorem.

## Proofs

`lake build` compiled Mathlib from source on the reproduction machine, because the
Mathlib cache host is not reachable from it. It succeeded (3,741 jobs) with no `sorry`
warnings. `lake env lean scripts/Axioms.lean` reports `[propext, Classical.choice,
Quot.sound]` for all 32 theorems listed in THEOREMS.md (`proofs.txt`). The source contains
no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` declarations.

What the theorems cover, read against the code that runs: the kernel theorems are about
`butterflyK`, and the C file is printed from `butterflyK` (byte-identical on regeneration).
The schedule and error theorems are about `refTransform`, the function the C engine is
compared with bit for bit. The C executor and the SIMD printing are outside the proofs, as
TRUST.md says. They are covered only by the bit-exact tests, which are evidence for the
inputs they run and not a proof for every input.

## Recommendations

* State the speed claim as "≈ 2× faster for N ≤ 16, parity for N ≥ 256, geometric mean
  0.75–0.83× depending on run". Drop "also faster for N ≥ 1024": it did not reproduce.
* Record FFTW's configure line, `CFLAGS` and `fftw-wisdom` provenance in `meta.json`.
  The FFTW baseline moved by up to 1.4× between two VMs of the same CPU model.
* Advertise the error theorem as an explicit bound, not as an accuracy guarantee
  comparable to FFTW's. Its slack grows to about 10⁵ at large N.

## How to rerun

```sh
LEAN=… OUT=build FFTW_SRC=… scripts/build.sh
# FFTW and long-double FFTW installed under $FFTW (fftw3.h, libfftw3.a, libfftw3l.a):
gcc -O2 -ffp-contract=off -Icsrc -I$FFTW/include -c tools/c/xcheck.c -o build/xcheck.o
$LEAN/bin/leanc -o build/xcheck build/xcheck.o build/lf_lean.o build/lf_fast.o build/lf_kernels_gen.o \
  .lake/build/lib/liblean_x2dfftw_LeanFFTWExec.a $FFTW/lib/libfftw3.a $FFTW/lib/libfftw3l.a -lm
ulimit -s unlimited; taskset -c 0 build/xcheck -m patient -r 21 2 4 8 … 262144
gcc -O2 -Icsrc -c tools/c/twcheck.c -o build/twcheck.o && $LEAN/bin/leanc -o build/twcheck build/twcheck.o \
  build/lf_lean.o build/lf_fast.o build/lf_kernels_gen.o .lake/build/lib/liblean_x2dfftw_LeanFFTWExec.a -lm
lake env lean --run scripts/ErrorBound.lean consts 64 > consts.txt && python3 tools/kappa.py consts.txt
lake env lean --run scripts/ErrorBound.lean bound 1024 8 8 8 2
```
