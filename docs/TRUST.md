# Trust boundary

What a user of Lean FFTW relies on, split into what is proved in Lean, what is
established by testing, and what is trusted as is.

## The chain for the fast engine (1-D complex, N = 2^k, or N > 1 whose prime factors are all at most 13)

This is the path every benchmark size takes, primary and secondary.

| Link | From | To | How it is established |
|---|---|---|---|
| 1 | `dftSum` | Mathlib `ZMod.dft` | **proved** (`dftSum_true_eq_dft`, `dftSum_false_eq_invDft`) |
| 2 | `butterflyK` (generated kernels) | the size-R DFT | **proved** (`cse_correct`, `butterflyK_correct`) |
| 3 | `stockhamWith` over exact reals | `dftSum` | **proved** (`stockhamWith_exact`) |
| 4 | `refTransform` (Lean `Float`) | the exact DFT, within an explicit bound | **proved** (`refTransform_error`, `refTransform_error_depth`), under the stated hypotheses (finite values, constant accuracy κ, twiddle accuracy τ) |
| 5 | Lean `Float` semantics | IEEE binary64 round-to-nearest-even | **proved** on the Lean side: Lean 4.35 defines `Float` operations through `Float.Model`, and `floatArith_stdModel` reads them through FloatLib's binary64 model |
| 6 | compiled `Float` code | Lean's `Float` definitions | **trusted**: Lean compiles `Float` operations to C `double` via `@[extern]`; this relies on the C compiler and the CPU implementing IEEE binary64 |
| 7 | each block of vector code in the assembly engine (`LeanFFTW/Asm`) | its specification: the kernel of links 2–4, instantiated lane by lane | **checked by a checker proved sound** (`check_sound`), for 1,442 of 1,498 blocks; the other 56 (masked blocks) are tested only |
| 8 | the assembly engine as a whole | `refTransform` with the same radices | **tested bit for bit** (below) |

The library contains no C. The engine is AVX-512 assembly written by Lean, and Lean also
builds and runs the plans. (Until commit `7cc9489` the engine was C printed by Lean and
compiled by gcc, tested bit for bit but with nothing checked below the kernel. It was removed
on 2026-11-10.)

### Link 7: translation validation of the emitted code

The vectorizer, the scheduler of each block and the register allocator are ordinary
unverified Lean programs. What makes their output trustworthy is that it is checked:

* For each block the generator states a `Spec`: for every memory operand the block stores,
  the scalar each lane must hold, as a straight-line program over the words of the initial
  memory. The specifications are the proved kernels (`butterflyK` and its relatives)
  instantiated once per lane, plus the layout (which complex number sits in which lane).
* `check` runs the emitted instructions symbolically, including the loads, the
  deinterleaving and transposition shuffles, the spills and the stores, and accepts only if
  every stored lane is the required value. `gen_asm` refuses to write an engine with a
  rejected block.
* `check_sound` (`Asm/Sound.lean`, no `sorry`, standard axioms) proves that an accepted
  block, run in the instruction model of `Asm/Sem.lean` from any machine state, leaves the
  specified value in every specified lane. It holds for every lawful arithmetic, so for
  binary64 with the same rounding at every operation: an accepted block is bit-identical to
  the kernel, not merely close. Its memory hypotheses (`Sep`) are that distinct operands
  written by a block do not overlap and that spill slots and constants do not overlap the
  data; reads may overlap writes, as in an in-place transform.

The checker has caught a real bug: the register allocator released a dying value's spill
slot one instruction early, in the size-35 kernel. No test had failed.

What link 7 does **not** cover, and link 8 has to:

* the 56 masked blocks (tail iterations with masked loads and stores), which have no
  specification yet;
* the layout part of each specification (that lane `q` of operand `m` is the right complex
  number) and the `Sep` hypotheses for the addresses the engine actually uses;
* everything outside the vector blocks: loop counters and pointer arithmetic, the plan tree
  and its parameters, twiddle and address tables, the thread pool;
* the instruction model against the real CPU, the printer from instructions to assembler
  text, and `as`.

### Link 8: bit-exact tests

`scripts/AsmTest.lean` (`asm_test`) compares the engine's output with `refTransform` word
for word, in both directions, in place and out of place:

* `asm_test K`: every radix sequence of every N = 2^6 … 2^K, with and without cache blocking
  and prefetching (`asm_test 10`: 7,424 plans run);
* `asm_test small`: the direct and two-pass kernels (596 plans);
* `asm_test stk MAXN`: the Stockham and blocked schedules over mixed radices (3,408 runs
  to 120);
* `asm_test plan LO HI` and `asm_test mixed LO HI [N…]`: the plan the planner actually
  picks, for powers of two and for every size with prime factors at most 13.

Each butterfly performs the same operations on the same values as `refTransform`; the
engine only reorders memory traffic. That is why the output is expected to be, and is
tested to be, identical bit for bit. libbench2 `--verify` additionally checks the planner's
choice against FFTW's own linearity, impulse and shift tests. A test is evidence for the
inputs it runs, not a proof for all inputs, and that is the remaining gap between the
proofs and the running code.

Also trusted as is: the twiddle tables. They are computed by Lean (`Trig.cosSin2PiTable`),
so the engine and `refTransform` use the same values. Their accuracy (τ) is a hypothesis of
the error theorems, not proved. It is measured at 0.502 ulp (`asm_test twdump` with
`tools/twcheck.py`), and the kernel constants (κ) at 0.945 ulp (`tools/kappa.py`).

Planning (`Asm/Planner.lean`) enumerates candidates, orders and prunes them by the proved
operation counts, measures, and chooses. A planning mistake can make a transform slow, not
wrong.

### The Lean-compiled backend (`LeanFFTW/Native`)

A second executor for powers of two, written entirely in Lean and compiled by Lean's own
compiler (no hand-written C). `Native.exec` is a safe function defined as the proved
schedule, so `exec_eq_refTransform` is a theorem about it. The code the compiler runs is
its `@[implemented_by]` implementation `execU`, which is trusted and tested bit for bit:

* the kernels in `Native/Kernels.lean` are printed by `Gen/LeanEmit.lean` from the same
  `Kernel` values as the assembly engine's blocks, one `let` per operation, constants as
  their exact bits;
* `Native/Prim.lean` holds the whole unsafe surface: an unchecked read, a store without
  bounds or sharing checks, an uninitialized allocation (marked `never_extract` so the
  compiler cannot merge two of them, a bug the bit-exact test caught), and a constant
  helper. `execU` sizes every array it indexes, checks the input size (falling back to the
  reference), and makes its output unshared before the first store;
* `scripts/NativeBench.lean check` compares `exec` and `execInto` with `refTransform` bit for
  bit for every radix sequence over {2, 4, 8, 16} (all orders up to 2^10, sorted orders up
  to 2^14), both directions: 2,236 plans, 0 failures.

Deleting the `implemented_by` attributes leaves the same functions, only slower; that is
the sense in which the unsafe code "can be taken out".

## The generic engine (everything else)

1-D complex sizes with a prime factor above 13, r2c/c2r, all r2r kinds, multi-dimensional, vector and strided
problems run in the generic engine, which is pure Lean (`Core/Alg.lean`,
`Core/Problem.lean`, `Core/FloatOps.lean`, `Core/FastExec.lean`).

* Its mixed-radix algorithm is **proved** equal to the DFT in exact arithmetic
  (`exec_mkPlan_exact`).
* The code that runs is `execFloatFast`, which the compiler substitutes for the
  specification `exec floatOps` through `@[csimp]`. The two are **proved** equal
  (`execFloat_eq_fast`), so the substitution changes speed and nothing else. The
  substitution itself is done by Lean's compiler, which is trusted as in link 6.
* Its binary64 execution (`floatOps`) has **no proved error bound**.
* The r2c/c2r and r2r reductions to a complex DFT (`embed`, `extract`, `hermExt`) are
  **not proved**. The r2r formulas are those of the FFTW manual §4.8; they are checked
  numerically by FFTW's own test harness, not stated as Lean theorems.

All of it is **tested** with FFTW's `tests/check.pl` driving libbench2's `--verify`
(linearity, impulse response and time-shift checks), the same tests FFTW's `make check`
applies to FFTW.

## The benchmark and test harness

libbench2 and `check.pl` come unmodified from the FFTW 3.3.10 source distribution
(sha256 in [FFTW_INVENTORY.md](FFTW_INVENTORY.md)). The Lean FFTW backend
(`bench/backends/bench-leanfftw.c`) is the only new C code in the harness, and the only C
in the repository. FFTW itself is built only as a competitor and is never linked into Lean
FFTW.

## Axioms

`scripts/Axioms.lean` prints the axioms of every theorem in [THEOREMS.md](THEOREMS.md).
All of them use only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`,
`admit`, `native_decide` or `implemented_by` in the proofs.
