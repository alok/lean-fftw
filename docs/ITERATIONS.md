# Optimization iterations

Every iteration is a commit. Each one passes the bit-exact differential test of every
enumerated plan against the Lean reference (`csrc/test_fast.c`) and libbench2 `--verify`.
The kernel correctness theorem (`butterflyK_correct`) is re-checked for every iteration.
"Quick" timings come from `tools/c/prof_fast.c` on an otherwise idle core; the protocol
measurements (docs/BENCHMARK_PROTOCOL.md) are in `results/`.

Times are for the forward complex transform `ocf<N>`, single thread.

## i0: baseline (commit 525cb2e + working tree, binary `bench-lean-i0`)

Stockham passes between two split (re/im) work arrays, generated AVX-512/AVX2 kernels,
measuring planner over radix sequences.

Protocol run `results/i0-baseline`: G(lean-i0 / FFTW best of MEASURE, PATIENT, EXHAUSTIVE)
= **1.252**, 95% CI [1.248, 1.267]. FFTW is the strongest verified competitor
(geometric-mean time 1.214 µs vs MKL 1.657 µs). Lean FFTW was faster than FFTW only at
N = 2, 4, 8.

Notes: the benchmark driver was pinned to CPU 0 partway through (row 500); a few
minutes of rows before that may be perturbed by profiling on the same core
(`results/i0-baseline/NOTES.txt`). The median over 10 interleaved runs limits the effect.

## i1: fused small transforms and the in-place schedule (commit 587ed30)

Hypotheses:

1. For N ≤ 512 the two passes of a plan `[R1, R2]` fit in registers; keeping the
   intermediate array in registers removes a store and reload of the whole array.
2. For N ≥ 1024 the working set (input, two split work arrays, output, twiddles) exceeds
   the 48 KB L1. Profiling individual passes (`tools/c/prof_pass.c`) showed each pass
   runs about 50% faster when only two arrays are live.

Change: fused kernels `lf_fused_R1xR2`; the in-place schedule `LF_INPLACE`: the first
pass reads the input in digit-reversed order and writes the output array in a blocked
layout (VL real parts, VL imaginary parts), then all passes run in place in the output
array; the last pass writes interleaved complex numbers. The butterflies and twiddles are
those of the Stockham schedule, so results are bit-identical to the Lean reference
(1782 plans, N ≤ 16384, out-of-place and in-place).

Quick timings (ns): N=64 75.7 → 50.3; 1024 1805 → 1191; 2048 4665 → 2949;
4096 10600 → 7546; 16384 52330 → 37376.

## i2: FMA contraction (commit f142764)

Hypothesis: the kernels are compute-bound for N ≤ 32768 and executed 5–27% more
operations than FFTW's genfft codelets, mostly standalone multiplications by constants.

Change: `SExpr.contract` rewrites `x*y ± c` and `c ± x*y` into single-rounding fused
operations before CSE. Exact values are unchanged (`ev_contract`), so
`butterflyK_correct` holds for the contracted kernels; binary64 results change (one
rounding fewer per contraction) and the Lean reference changes with them, since it
evaluates the same kernels.

Operation counts (twiddled radix-R butterfly, ours → genfft t1): R=8 80 (= 80),
R=16 216 (204), R=32 552 (496).

Quick timings (ns): N=512 563 → 533; 1024 1191 → 1140; 256 258 → 251.

Also in this commit: optional cache blocking of the in-place schedule
(`lf_set_blocking`), not yet used by the planner.

## i3: interleaved-complex kernels for whole small transforms (commit ea5260f)

Hypothesis: for N ≤ 128 the split re/im layout costs a deinterleave on input and a
re-interleave on output that are as expensive as the butterflies. FFTW's `n1fv` codelets
work directly on interleaved complex vectors.

Change: `LeanFFTW/Gen/Interleave.lean` vectorizes the same CSE'd straight-line kernel over
interleaved complex numbers (a vector holds whole complex values, so lanes mix real and
imaginary parts). Each output vector is built from scalar slots by `vpair`; operations whose
lanes need different add/sub use `fmaddsub`/`fmsubadd`, and anything else falls back to a
shuffle. A whole transform `N = R1·R2` becomes one function with constant twiddles
(`LF_CFUSED`). The arithmetic per scalar slot is the kernel's, so results stay bit-identical to
the Lean reference.

Quick timings (ns, i2 → i3): N=8 9.9 → 5.2; 16 19.1 → 9.2; 32 44.6 → 22.7; 64 49.9 → 48.6.

## i4: measuring planner over schedules and cache blocking (binary `bench-lean-i4`)

Hypotheses:

1. The planner chose among radix sequences but not among schedules; for several sizes the
   best schedule differs from the fixed choice.
2. For N ≥ 2^15 the in-place passes stream the whole array from L3 each time. Running the
   first T passes on groups of level-T blocks that fit in L2, and the later passes in
   chunks of Q columns, cuts L3 traffic.

Change: `lf_plan_measure` times every radix sequence under every applicable schedule (min of
5 runs of ≥ 0.2 ms), then for N ≥ 2^15 tries blocking (T from s−3 to s−1, Q ∈ {0, 32, 128})
on the 8 best in-place plans, and re-times the 4 leaders interleaved over 3 rounds to reduce
noise. Kernel signatures gained a twiddle stride (`tns`, `tq`) so column chunks index the
twiddle table directly. A buffered-chunk variant (copying each chunk to a small contiguous
buffer) and non-temporal stores were tried and removed: both were slower (per-row copy
overhead, then L2 set conflicts between power-of-two strided rows).

Tests: all 3,236 enumerated plans (both directions) for N ≤ 16384 (out-of-place and in-place) and every
blocking option of three radix sequences per size for N = 2^15 … 2^18 (470 plans) match the
Lean reference bit for bit; libbench2 `--verify` passes for N = 1 … 2^18, both directions,
in and out of place. Commands: `test_fast 14`, `test_fast -1 18`.

Quick timings (µs, i2 from the 3-run quick protocol → i4 single runs): N=32768 84.3 → 81.0; 65536 225 → 218; 131072 657 → 538;
262144 1543 → 1350.
