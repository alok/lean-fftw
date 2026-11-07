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
| 7 | the C fast engine (`csrc/`, generated `lf_kernels_gen.c`) | `refTransform` with the same radices | **tested bit for bit** (below) |

Link 7 is the trust boundary. The C kernels are printed by the Lean generator from the
same `Kernel` values that links 2–4 are about, with every rounding operation written out
explicitly. The code is compiled with `-ffp-contract=off`, so the compiler adds no fused
operations, and the only FMAs are the ones in the kernel. The C engine reorders memory
traffic (in-place, blocked, fused and two-pass schedules), but each butterfly performs
the same operations on the same values as `refTransform`. That is why its output is
expected to be, and is tested to be, **identical bit for bit**.

`csrc/test_fast.c` checks link 7. It runs every plan the planner can enumerate for every
N = 2^k from 1 to 2^14, both directions, in place and out of place, and compares each
output with `refTransform` (called through the Lean FFI) using `memcmp`. For N = 2^15 to
2^18 it checks the cache-blocked plans: three plans spread over the enumeration, for each
block parameter, in both directions and both placements (`test_fast 14 18`: 3,726 plans,
0 failures, recorded per iteration in [ITERATIONS.md](ITERATIONS.md)). `test_fast mixed
MAXN [sizes…]` does the same for every 13-smooth size that is not a power of two up to
MAXN and for the listed sizes: every plan the planner can enumerate, both directions,
`memcmp` against `refTransform` with the same radices.

What the printing adds on top of the proved kernels, and what these tests therefore have
to catch, is: the SIMD instructions for each kernel operation (one lane per butterfly,
or for the whole-transform kernels of sizes up to 64 one complex number per 128-bit
vector with `fmaddsub`-style pairs); the deinterleaving and transposition shuffles; and,
for sizes whose butterfly count is not a multiple of the vector length, one extra loop
iteration with masked loads and stores (inactive lanes are loaded as zero and never
stored). Every lane computes the same operations as the scalar kernel, so the masked
iteration is bit-identical too, and the tests include sizes where it runs in every pass. libbench2
`--verify` additionally checks the plan the planner actually picks, for N = 1 to 2^18.
`tools/c/xcheck.c` checks that plan **bit for bit** against `refTransform` with the
radices the planner chose, in and out of place, on random inputs. It ran at all 36
benchmark sizes, three times, with 0 mismatches ([REPRODUCTION.md](REPRODUCTION.md)).
A test is evidence for the inputs it runs,
not a proof for all inputs, and that is the remaining gap between the proofs and the
running code.

Also trusted as is: the twiddle tables. They are computed by Lean (`Trig.cosSin2PiTable`)
and passed to C, so C and `refTransform` use the same values. Their accuracy (τ) is a
hypothesis of the error theorems, not proved. It is measured at 0.502 ulp
(`tools/c/twcheck.c`), and the kernel constants (κ) at 0.945 ulp (`tools/kappa.py`).

### What is Lean and what is C in the fast engine

* **Planning** is Lean (`LeanFFTW/Plan/Planner.lean`): candidate enumeration, the order and
  pruning of the search by the proved operation counts, measurement, and the choice. The C
  side only builds and runs the plan it is handed. A planning mistake can make a transform
  slow, not wrong: up to 2^14 every plan the planner can enumerate is in the bit-exact test
  set, and above that the blocked plans are sampled and the chosen plan is checked by `xcheck`.
* **The in-place executor's address table** (`leafOffsets`, the digit reversal) is computed
  by Lean and read by C (`lf_leaf_offsets`); `ipLeaf_scatter` is about that function.
* `test_fast` needs `ulimit -s unlimited` for the blocked checks at N ≥ 2^15 (the test
  allocates its reference buffers on the stack; this predates these changes).

### The Lean-compiled backend (`LeanFFTW/Native`)

A second executor for powers of two, written entirely in Lean and compiled by Lean's own
compiler (no hand-written C). `Native.exec` is a safe function defined as the proved
schedule, so `exec_eq_refTransform` is a theorem about it. The code the compiler runs is
its `@[implemented_by]` implementation `execU`, which is trusted the same way as the C
engine (link 7) and tested the same way:

* the kernels in `Native/Kernels.lean` are printed by `Gen/LeanEmit.lean` from the same
  `Kernel` values as the C kernels, one `let` per operation, constants as their exact bits;
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
(`bench/backends/bench-leanfftw.c`) is the only new C code in the harness. FFTW itself
is built only as a competitor and is never linked into Lean FFTW.

## Axioms

`scripts/Axioms.lean` prints the axioms of every theorem in [THEOREMS.md](THEOREMS.md).
All of them use only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`,
`admit`, `native_decide` or `implemented_by` in the proofs.
