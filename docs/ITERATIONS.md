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
