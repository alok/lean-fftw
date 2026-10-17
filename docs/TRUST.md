# Trust boundary

What a user of Lean FFTW relies on, split into what is proved in Lean, what is
established by testing, and what is trusted as is.

## The chain for the fast engine (1-D complex, N = 2^k)

This is the path every benchmark size takes.

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
0 failures, recorded per iteration in [ITERATIONS.md](ITERATIONS.md)). libbench2
`--verify` additionally checks the plan the planner actually picks, for N = 1 to 2^18.
A test is evidence for the inputs it runs,
not a proof for all inputs, and that is the remaining gap between the proofs and the
running code.

Also trusted as is: the twiddle tables. They are computed by Lean (`Trig.cosSin2PiTable`)
and passed to C, so C and `refTransform` use the same values. Their accuracy (τ) is a
hypothesis of the error theorems, not proved.

## The generic engine (everything else)

Non-power-of-two sizes, r2c/c2r, all r2r kinds, multi-dimensional, vector and strided
problems run in the generic engine, which is pure Lean (`Core/Alg.lean`,
`Core/Problem.lean`, `Core/FloatOps.lean`).

* Its mixed-radix algorithm is **proved** equal to the DFT in exact arithmetic
  (`exec_mkPlan_exact`).
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
