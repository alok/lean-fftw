# Lean-driven code generation (round of 2026-11-07)

> **Historical.** This document describes the library as of the date in its title, when
> the fast engine was C printed by Lean (`csrc/`, `tools/c/`). That engine was removed on
> 2026-11-10 in favour of assembly written by Lean (`LeanFFTW/Asm`); the files named here
> are in the history up to commit `7cc9489`. See [TRUST.md](TRUST.md) for the current state.

The goal of this round: Lean, not C, should drive the code generation and the optimization.
That means more of the library's decisions made and checked in Lean, and a test of how fast
Lean's own compiler can make an FFT. In the spirit of FFTW's genfft, but with proofs and
measurement doing the search.

## Where the code is

| | Lines | Notes |
|---|---|---|
| Hand-written Lean | 8,508 | spec, generator, proofs, planner, generic engine, Lean backend |
| Generated Lean | 1,897 | `LeanFFTW/Native/Kernels.lean` |
| Hand-written C, library | about 600 | executor loops, FFI glue (`csrc/lf_fast.c`, `lf_lean.c`, headers) |
| Hand-written C, tests and bench backends | about 1,200 | libbench2 backends, differential tests |
| Generated C | 193,499 | `csrc/lf_kernels_gen.c`, printed by the Lean generator (`linguist-generated`) |

For comparison, FFTW's generator (genfft) is OCaml and its runtime is C, at roughly 1 line of
OCaml to 5 of hand-written C. FFTW's git tree stores no generated codelets: its README says
building from git requires OCaml. Here the hand-written ratio is the other way round, about
14 lines of Lean to 1 line of library C. GitHub's language bar counts the committed generated
C unless it is marked generated, and it now is.

## What moved into Lean, and what it is proved to do

1. **Cost counting in the code, with CSLib.** The Stockham schedule is also a program in
   CSLib's query framework (`Cslib.Algorithms.Lean.Query.FreeM`). Its queries are a kernel
   operation, a load and a store. `Proof/Cost.lean` proves two facts about the program.
   Evaluating it gives the transform (`eval_stockhamQ`). Counting its queries gives the
   closed form the planner uses (`cost_stockhamQ`). For a given plan, the same program is
   proved both to compute the DFT and to cost `stockhamCost` (`stockhamQ_dft_and_cost`).
2. **The planner.** Enumeration, search order, pruning, measurement and the choice are now
   in `LeanFFTW/Plan/Planner.lean`. C only builds and runs the plan it is handed.
3. **The in-place schedule.** This is the schedule the planner picks for most power-of-two
   sizes from 1024 up. It is now a Lean definition, proved equal to the Stockham schedule
   for every arithmetic (`inplaceWith_eq_stockhamWith`). The C executor reads its
   digit-reversal address table from that Lean definition.
4. **A Lean-compiled backend.** The same kernels are also printed as Lean code and
   compiled by Lean's compiler, with no hand-written C (below).

## The search, and what the proved counts are good for

Exact operation counts are free in this design, so the first experiment asked whether a
cost model built on them could replace measurement. The answer is no.
`tools/costmodel.py` fits models on the planner's log of 7,265 measured candidates. One model
is linear in arithmetic operations, memory operations and passes; the other uses
per-radix weights. Both are fitted per schedule and cache regime. Ranked by either model,
the best measured plan among the model's top 4 is up to 2.3× slower than the true best
(geometric mean 1.22×, held-out sizes, `results/lean-driven/costmodel-holdout.txt`). The time
goes to memory traffic and schedule effects that operation counts do not see.

The counts are good at ordering and pruning the search, though. The planner now times
candidates in order of proved operations per vector lane. It skips any candidate whose
count is more than 1.5× the best of its schedule, and it drops a candidate after one
measurement if that measurement is 1.3× slower than the best so far. Pruning at 1.4× already
lost nothing at any benchmark size; 1.5× is the margin. Planning at 2^18 went from 24.5 s
(exhaustive) to 8.7 s, with plans of the same speed
(`results/lean-driven/planner-race-vs-exhaustive.txt`; `LF_PLANNER=exhaustive` keeps the old
search).

## How fast can Lean's own compiler make it?

`LeanFFTW/Native` is a second executor for powers of two, written only in Lean.

* `Gen/LeanEmit.lean` prints each kernel as one straight-line `unsafe def` over unboxed
  `Float` and `FloatArray`, one `let` per operation. These are the same CSE'd operations as
  the C kernels, with constants given by their exact bits. It also prints one loop per radix.
* `Native.exec` is defined as `inplaceWith floatArith`. `exec_eq_refTransform` proves that it
  equals the binary64 reference for every plan. The compiler runs the generated code instead,
  through `@[implemented_by]`.
* The unsafe surface is four primitives in `Native/Prim.lean`: an unchecked read, an
  unchecked store, an uninitialized allocation and a constant helper. Deleting the
  `implemented_by` attributes leaves the same functions, only slower.
* `scripts/NativeBench.lean check` compares the backend with `refTransform` bit for bit on
  2,236 plans: every radix order over {2, 4, 8, 16} up to 2^10, sorted orders up to 2^14,
  both directions. There were 0 failures.

The first version was 13× slower than the SIMD C engine. Each of the following changes came
from reading what Lean's compiler and clang actually produced:

| Change | Found by | Effect |
|---|---|---|
| compile with `-march=native` | `Float.fma` compiled to a libm call | about 3× faster |
| print constants as C literals (`cst`, `extern c inline` bit cast, `never_extract`) | each `Float.ofBits` constant became a lazily initialized global behind a once-check | removed a load and a branch per constant, and unblocked vectorization of radices 8 and 16 |
| store with no copy-on-write check (`wr`), after making the output unshared once (`own`) | the vectorizer's report: "call instruction cannot be vectorized" | radix-2 and radix-4 loops vectorized |
| allow more runtime alias checks (`-mllvm -runtime-memory-check-threshold`) | "too many memory checks needed" | radix-8 and radix-16 loops vectorized |
| mark the allocation `never_extract` | the bit-exact test: two `alloc n` were merged into one array | correctness fix |

Two schedules designed for the vectorizers were slower, and are kept only as a record in
draft PR #1 (branch `experiment/lean-vectorized-schedules`). One was an out-of-place
Stockham schedule (21 µs vs 16 µs at N = 4096): clang still re-checked aliasing on every
block. The other was a split-format schedule whose kernels process 4 or 8 butterflies
side by side for the straight-line vectorizer (27.6 µs): clang packed only parts of each
kernel.

Result on this machine (Granite Rapids; `results/native/native_times.txt`, best plan per
size; C times are the protocol medians of the same commit):

| N | Lean backend (plan) | C engine | ratio | reference (spec as code) |
|---|---|---|---|---|
| 2 | 13.2 ns (2) | 1.27 ns | 10.4× | 26.4 µs |
| 4 | 14.6 ns (4) | 1.57 ns | 9.3× | 30.9 µs |
| 8 | 19.5 ns (8) | 2.53 ns | 7.7× | 48.5 µs |
| 16 | 33.3 ns (16) | 5.94 ns | 5.6× | 205 µs |
| 32 | 80.5 ns (8×4) | 14 ns | 5.8× | 159 µs |
| 64 | 140 ns (8×8) | 32.1 ns | 4.4× | 324 µs |
| 128 | 288 ns (16×8) | 74.3 ns | 3.9× | 1.26 ms |
| 256 | 636 ns (16×8×2) | 168 ns | 3.8× | 2.54 ms |
| 512 | 1.42 µs (16×2×2×2×2×2) | 460 ns | 3.1× | 5.66 ms |
| 1024 | 2.89 µs (16×2×2×2×2×2×2) | 1.01 µs | 2.9× | 11.53 ms |
| 2048 | 6.6 µs (16×2×2×2×2×2×2×2) | 2.42 µs | 2.7× | 24.85 ms |
| 4096 | 16.2 µs (8×8×8×8) | 6.19 µs | 2.6× | 24.87 ms |
| 8192 | 35.5 µs (8×8×8×2×2×2×2) | 14.1 µs | 2.5× | — |
| 16384 | 84.8 µs (8×4×2×2×2×2×2×2×2×2×2) | 30.8 µs | 2.8× | — |
| 32768 | 174 µs (8×4×2×2×2×2×2×2×2×2×2×2) | 68 µs | 2.6× | — |
| 65536 | 500 µs (8×4×4×2×2×2×2×2×2×2×2×2) | 208 µs | 2.4× | — |
| 131072 | 1.30 ms (8×8×8×8×8×4) | 659 µs | 2.0× | — |
| 262144 | 2.31 ms (8×8×8×8×8×8) | 1.49 ms | 1.6× | — |

The Lean-compiled backend runs at about 2.5–3× the time of the hand-scheduled SIMD C from
N = 1024 up (1.6–2× at the two largest, memory-bound sizes), and 4–10× at small sizes, where a
fixed per-call overhead of about 12 ns dominates. It is far
from the C engine, but it is about 4,000× faster than the reference implementation (the
specification run as boxed `Array Float` code), and it is proved to compute the same
function. Closing the rest of the gap needs explicit vector types in Lean's compiler (an
unboxed `Float×4` with SIMD lowering) or a way to tell the C compiler that two arrays do not
alias. Lean has neither today, and both would be changes to Lean's compiler, not to this
library.

## What did not change

The fast engine's kernels are still printed as C by the Lean generator and checked bit for
bit against the proved reference. The headline numbers still come from that engine.

Protocol rerun for this round, on this machine (Granite Rapids, family 6 model 173, 2.3 GHz,
not the Sapphire Rapids of earlier runs, so every number was re-measured): FFTW wisdom was
generated from scratch per planner mode, then 10 interleaved runs of this commit (i10), the
previous release (i9) and FFTW in its three modes (`results/gnr-i10`). G(i10 / FFTW best mode)
= **0.814, 95% CI [0.794, 0.829]**, inside the predeclared ≤ 0.90. i10 / i9 = 0.990
[0.963, 1.008]: moving the planner into Lean and pruning it cost nothing measurable. As in
the reproduction, the whole margin is at small sizes: 0.28–0.58× for N ≤ 32. From N = 256 up
FFTW is ahead at most sizes on this CPU: 0.96–1.08× from 1024 to 32768, 1.22× at 512, 1.12×
at 65536, and 1.34× and 1.31× at 2^17 and 2^18 (i9: 1.31× and 1.48×). Large-size schedules
remain the open performance problem.
