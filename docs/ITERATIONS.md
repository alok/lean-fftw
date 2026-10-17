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

## Hardware change after i4

The container was restarted after i4 and now runs on a different host CPU: Intel Xeon
model 85 stepping 7 (Cascade Lake), 2.8 GHz, 32 KB L1d, 1 MB L2 per core, 33 MB L3, AVX-512
(i0–i4 were developed on a Sapphire Rapids host, `results/i0-baseline/meta.json`). All
comparisons below are within one machine; the protocol run re-measures every iteration and
every competitor together. FFTW wisdom was regenerated for this CPU.

Quick run `clx-quick1` (2 interleaved runs, all 18 sizes): geometric-mean time lean-i4
1.503 µs, FFTW best of MEASURE/PATIENT 1.794 µs (ratio 0.84), MKL 2.464 µs. Weakest sizes:
N = 256 (1.30× FFTW), 512 (1.07×), 262144 (0.98×).

## i5: interleaved two-pass kernels and a better vectorizer (commit below)

Hypotheses:

1. N = 128…512 lose because the split-format passes pay a deinterleave/reinterleave and a
   transpose; the whole-transform interleaved kernels of i3 do not fit in registers beyond
   N = 128.
2. On this CPU (shuffles and 512-bit FMAs share port 5) the interleaved kernels' shuffle
   count matters: the 256-point kernel issued 596 `shuffle_pd`, mostly from pairing
   operands of the scalar kernel lane by lane in an unlucky order.
3. Loading every block's inputs before the first butterfly kept 64 vectors live (327 stack
   spills/reloads in the 256-point kernel).

Changes:

* `LF_CTWO` (`emitCFused … (mem := true)`): the i3 kernel with the pass-1 results stored to
  memory after each block's transposes, so N = R1·R2 up to 32·32 runs as two interleaved
  passes with constant twiddles.
* Vectorizer (`Interleave.lean`): operand orders are chosen by a lookahead cost estimate
  (`vcost`, depth 3); a pair may be built in the opposite lane order and exchanged with one
  shuffle; a bottom-up SLP plan (`slpPairs`) pairs each scalar operation with the operation
  on the partner lane before code is generated; `vsplit` reuses lanes already present.
  Shuffles in the 256-point kernel: 596 → 368 (248 after the compiler folds shuffles of
  constants), arithmetic vector operations 1016 → 792.
* Per-block emission order: each block is loaded, transformed and transposed in turn.
  Stack spills in the 256-point kernel: 327 → 32.

Tried and removed: interleaved Stockham passes for N ≥ 512 (`LF_CSTOCK`, every pass a loop
over interleaved twiddled kernels with a duplicated twiddle table). With the per-butterfly
`j mod ns` removed it was still slower than the in-place split schedule (N = 1024: 2088 ns
vs 1778 ns; 4096: 11.5 µs vs 9.9 µs), likely from the three live arrays and power-of-two
strides; a lookahead depth of 4 in `vcost` produced more shuffles than depth 3 and took 12×
longer to generate.

Tests: `test_fast 14 18`: 3,726 plans (all enumerated plans N ≤ 16384 plus 470 blocked
plans N = 2^15…2^18), 0 mismatches against the Lean reference; libbench2 `--verify` max
error < 1e-14 for N = 1…2^18, forward and backward, in and out of place.

Quick timings on Cascade Lake (ns; i4 from `clx-quick1`, i5 from `prof_fast`, so only
indicative): N=32 34.6 → 27.2; 64 63.6 → 52.9; 128 149 → 123; 256 440 → 275;
512 819 → 754.

## i6: direct dispatch of whole-transform kernels; planning on the caller's arrays

The first round of the final protocol run (i0–i5, aborted after round 1 to add this
iteration; kept as `results/clx-protocol-aborted1`) put i5 at G ≈ 0.84 against FFTW's best
mode, with i5 *slower than i4* at N = 2 and 4 (4.85 ns vs 3.65 ns, reproducible).

Hypotheses:

1. At N ≤ 16 the fixed cost of `lf_execute` matters. It saved six registers and set up a
   stack frame on every call, because the multi-pass schedules share its body, before
   calling a kernel that does 4–100 flops. Why the i4 binary is faster at N = 2 was not
   established: its `lf_execute` is instruction for instruction the same, and its kernels
   were compiled on the earlier CPU (recompiling i5's kernels with that CPU's
   false-dependency tuning did not help).
2. At N ≥ 2^15 the planner's choice is unstable: the plan that wins during planning runs
   on freshly allocated arrays and is then rebuilt with new work arrays. The same plan's
   time varies by up to 40% with the physical pages it gets (power-of-two strides,
   L2/L3 set conflicts).

Changes:

* `lf_execute` is now a small function: plans that are one kernel (N ≤ 8 small kernels,
  `LF_CFUSED`) store it in `p->direct` and are reached by a tail call; `LF_CTWO` is a
  tail call too; the multi-pass schedules moved to a separate function. N = 2: 4.83 → 2.43
  ns; 4: 4.96 → 3.33; 8: 7.22 → 5.46; 16: 13.0 → 11.4 (bench, CPU 3, single runs).
* The planner keeps the four leading plans it built, re-times them, and returns the
  winner as timed, with its work arrays, instead of rebuilding it.
  `lf_plan_measure_arrays` times on the caller's arrays, as FFTW's planner does with the
  user's arrays; the libbench2 backend now uses it (libbench2 zeroes the arrays after
  setup, for every implementation).
* Work arrays and twiddle tables of 1 MiB or more are 2 MiB aligned with
  `madvise(MADV_HUGEPAGE)`.

Finding: hypothesis 2 is only partly right. A fixed plan at N = 2^18 still varies from
2.0 to 3.0 ms between processes and within one process (min of 8 timings). That is the
machine itself (other tenants' memory traffic on the shared L3), and it affects FFTW
equally. The planner changes remove one source of mismatch but cannot remove that noise.
The protocol's median of 10 interleaved runs is what handles it.

Tests: `test_fast 14 18`: 3,726 plans, 0 mismatches against the Lean reference;
libbench2 `--verify` passes for `ocf`, `icf`, `ocb`, `icb` at N = 1…2^18 (76 problems), max
L2 error 4.8e-16.

## Hardware change after i6

The container was re-provisioned on Sapphire Rapids again (model 207, 2.1 GHz, L2 2 MiB),
the CPU i0–i4 were developed on. Every binary still runs; i7 was developed and measured
here (protocol amendment 3).

## i7: verified optimizations (commit 4f4e8b2)

Two changes, each with a proof that it changes nothing but speed.

**Tan-factored twiddle rotations (fast engine).** Comparing operation counts with FFTW's
FMA codelets showed that the radix-16 and radix-32 kernels had 8% and 15% more operations
(156 vs 144 and 428 vs 372; radix 2–8 already matched). The difference came from the
twiddle rotations by angles that are not multiples of π/4. Each one cost two
multiplications and two fused operations, and the multiplications could not fuse into
the butterfly additions that consume them. The generator now writes the rotation of
`a + ib` by `θ` as `cos θ · (a − tan θ · b) + i · cos θ · (b + tan θ · a)`, with a new
exact constant `tan θ` (`Cst.tan`, binary64 value from the same integer trigonometry).
That is one fused operation per part, and FMA contraction folds the product by `cos θ`
into the next additions. Counts (additions, multiplications, fused): n16 (116, 8, 32) →
(100, 0, 48); n32 (292, 40, 96) → (212, 0, 176); t16 (116, 38, 62) → (100, 30, 78); t32
(292, 102, 158) → (212, 62, 238). The rotation lemma `evC_rotQ` was reproved, using
`tan θ · cos θ = sin θ` for `0 < θ < π/4`. `butterflyK_correct` and every downstream
theorem are unchanged and still hold for the new kernels.

**`@[csimp]` executor for the generic engine.** Profiling the generic engine
(non-power-of-two sizes and all other problem types) showed most of its time in closure
calls, boxed complex values, allocation and the composed closures that sub-transforms
read their input through. `Core/FastExec.lean` adds `execFloatFast`. It materializes the
input once, reads each sub-transform at an offset and stride, and sums every output in a
tail-recursive loop over unboxed `Float` accumulators, performing the same operations in
the same order as `exec floatOps`. `execFloat_eq_fast : @execFloat = @execFloatFast` is
proved with Lean core only, since the executable library does not depend on Mathlib.
`@[csimp]` then makes the compiler use the fast version wherever `execFloat` is called.

Results (protocol run on Sapphire Rapids, [RESULTS.md](RESULTS.md)):

* G(i7) = 0.809 [0.795, 0.868] against FFTW's best mode. Against i6 in the same run,
  G = 0.990 [0.949, 1.037], so **no detectable change**. The planner picks radix-16/32
  passes mainly at the large, memory-bound sizes, and the radix 2–8 kernels it uses
  elsewhere did not change. Single-plan timings with fixed radices were 5–30% faster at
  some sizes, but that is within this VM's run-to-run noise.
* Generic engine: 2.8× faster than i6 on N = 6…10368 (CI [2.5, 3.2]), still about 300×
  slower than FFTW.

Finding: on this CPU FFTW is faster than every Lean FFTW iteration for N ≥ 1024 (ratio
1.11 for i7), unlike on Cascade Lake (0.94). The success criterion still holds because of
the small sizes. The remaining gap is in the multi-pass schedules at mid and large N, not
in operation counts.

Tests: `test_fast 14 18`: 3,726 plans, 0 mismatches against the Lean reference; libbench2
`--verify` passes for `ocf` at all 18 primary sizes and for `icf`, `ocb`, `icb` at 9 of
them; bigcheck as reported in RESULTS.md.
