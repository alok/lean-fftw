# The cost model of the emitted code

The engine is assembly written by Lean. This note says what is proved about the cost of
that assembly, what is only measured, and how the generator uses both.

In short: every block of emitted vector code has a lower bound on its running time that is
a theorem about the instructions actually emitted. Measured passes run 1.05 to 1.2 times
above it. Choosing the order of instructions by the quantity the model counts made the
radix-16 and radix-32 passes about 20% faster and whole power-of-two transforms 7% faster
on geometric mean.

## One program, three handlers

A block is a list of instructions. `LeanFFTW/Proof/Ports.lean` writes it as a program in
CSLib's free monad (`Cslib.Algorithms.Lean.Query`) whose only query is "run this
instruction on this state":

```lean
inductive InstrQ (σ : Type) : Type → Type where
  | exec (s : σ) (i : Instr) : InstrQ σ σ

def blockQ : List Instr → σ → FreeM (InstrQ σ) σ
```

CSLib's two interpreters, `FreeM.eval` and `FreeM.cost`, then give that one program three
meanings. Each was already in the library as a separate definition; now each is a handler
of the same object.

| Handler | Answers a query with | The program then is | Theorem |
|---|---|---|---|
| `machine M ad` | the step of the processor model (`Asm/Sem.lean`) | `run M ad is s`, the semantics | `eval_blockQ_machine` |
| `checker cx` | the symbolic step of the checker (`Asm/Check.lean`) | `crun cx is`, the run `check_sound` is about | `eval_blockQ_checker` |
| `uopWeight` | the micro-operations of the instruction, by class | `portsOf is`, under **every** oracle | `cost_blockQ` |

The third line is the cost model. The cost does not depend on the oracle, so it is a
property of the code, not of the data it runs on. The block has no branches, so this is
exact.

## The cost is a vector, and the price is its scarcest port

The cost is not a number. `Ports` (`Asm/Ports.lean`) counts micro-operations by class, and
is an additive monoid, which is all `FreeM.cost` needs:

```lean
structure Ports where
  fp : Nat      -- arithmetic: add, subtract, multiply, fused multiply-add, xor
  shuf : Nat    -- unpck, shufpd, shuff64x2, permt2pd
  load : Nat    -- a load, or the memory operand of another instruction
  store : Nat
```

The model of the processor is the port layout of the Intel cores the engine targets
(Sunny Cove to Raptor Cove) for 512-bit code: arithmetic runs on either of two ports;
shuffles run on one port only, and it is one of those two; two loads start per cycle; one
store completes per cycle. A schedule assigns each micro-operation a cycle and a port it
may use, and no port does two things in one cycle. Dependencies between micro-operations
are ignored, which only makes schedules easier to find.

```lean
structure Schedule (us : List UClass) (T : Nat) where
  slot : Fin us.length → Fin T × Port
  inj : Function.Injective slot
  ok : ∀ i, (us.get i).allowed (slot i).2 = true

def Ports.bound (p : Ports) : Nat :=
  max (max p.shuf ((p.fp + p.shuf + 1) / 2)) (max ((p.load + 1) / 2) p.store)

theorem block_cycles_ge (is : List Instr) (T : Nat) (σ : Schedule (uopsOf is) T) :
    (portsOf is).bound ≤ T
```

So in this model no out-of-order scheduler, however clever, runs the block in fewer cycles
than `(portsOf is).bound`. The proof is a counting argument on each group of ports
(`Schedule.countP_le`). It uses no `sorry` and the standard axioms only
(`scripts/Axioms.lean`).

Two things keep the statement honest:

* The theorem is about the model. That the model matches the processor is measured, below,
  not proved.
* Instructions the model does not know (register copies, which the renamer removes, and
  integer and control instructions) count as nothing, so the bound stays a lower bound.

## Measuring against the bound

`asm_test ports PREFIX` prints the counts and the bound of every checked 512-bit block of
the functions whose name starts with `PREFIX`. `asm_test calib` times a loop of eight
chained fused multiply-adds, which takes 32 cycles per iteration whatever the clock, and so
gives the length of a cycle of 512-bit code on the machine at hand. `asm_test prof N R…`
times each pass of a plan.

The table is for the forward passes of the in-place schedule on the test machine (an Emerald
Rapids virtual machine, 0.334 ns per cycle of 512-bit code, one core, best of 9 to 11 runs;
other tenants make single runs vary by 10%). A pass body handles 64, 128 or 256 complex
numbers for radix 8, 16 or 32. "Before" is the code at commit `79069f3`, which ordered
instructions to minimize their number; "after" orders them by micro-operations (next
section). Counts are arithmetic / shuffle / load / store. Times are in cycles per body, with
the data in the first-level cache except for the middle radix-16 pass (`N = 4096`, second
level).

| Pass | Counts before | Counts after | Bound (cycles) | Measured before | Measured after | After / bound |
|---|---|---|---:|---:|---:|---:|
| first, radix 8 | 52 / 64 / 32 / 16 | 52 / 64 / 24 / 16 | 64 | 71 | 70 | 1.09 |
| middle, radix 8 | 80 / 0 / 52 / 16 | 80 / 0 / 38 / 16 | 40 | 46 | 43 | 1.08 |
| last, radix 8 | 80 / 16 / 52 / 16 | 80 / 16 / 38 / 16 | 48 | 50 | 51 | 1.05 |
| first, radix 16 | 148 / 128 / 134 / 72 | 148 / 128 / 83 / 34 | 138 | 166 | 159 | 1.15 |
| middle, radix 16 | 208 / 0 / 187 / 89 | 208 / 0 / 112 / 33 | 104 | 148 | 115 | 1.11 |
| last, radix 16 | 208 / 32 / 176 / 79 | 208 / 32 / 113 / 34 | 120 | 172 | 131 | 1.09 |
| first, radix 32 | 388 / 256 / 450 / 285 | 388 / 256 / 307 / 132 | 322 | 416 | 338 | 1.05 |
| last, radix 32 | 512 / 64 / 555 / 275 | 512 / 64 / 379 / 135 | 288 | 409 | 341 | 1.18 |

The bound is the same before and after: the reordering changes loads and stores, and for
these passes the arithmetic and shuffle ports set the bound. What changed is the distance to
it, from 1.04–1.43 to 1.05–1.18. So on this machine the proved bound is within a fifth of
the measured time of every pass listed.

## What the model predicted

**Lane stores.** The first pass of the in-place schedule spends 48 of its 64 shuffles on a
transposition, and the shuffle port is its scarcest port. Replacing the transposition by 64
narrow stores removes those shuffles. The model says the bound does not move: it stays at
64 cycles, set by the store port (64 stores) instead of the shuffle port (64 shuffles).
Measured, the variant is 10% faster while the output fits the first-level cache, because
the pass was running above its bound, and 4 to 27% slower from `N = 2048` up, where each of
the 64 stores also waits for its cache line. The experiment was run before the model
existed; the model would have said beforehand that the best case is a small gain.

**Spills and memory operands.** An instruction count hides work. A memory operand is a load,
and a spill is a store and a load, yet neither adds an instruction that computes anything.
The counts showed where the work was: in the radix-16 pass 187 loads for 32 numbers read
and 89 stores for 32 written, and in the radix-32 pass 594 and 314.

## How the generator uses it

The register allocator (`Asm/Alloc.lean`) already tried several orders of the operations of
a block and kept the result with the fewest instructions. It now keeps the result with the
fewest micro-operations, `(uopsOf is).length`, the same list the theorem counts, and it
has more to choose from:

* *Eager order* (`VBlock.schedule … (eager := true)`): an operation is computed as soon as
  all its operands are there, when one of them was just computed or used. The two halves of
  a butterfly come out together, so both operands die at once; the two parts of a complex
  product come out together, so a twiddle factor read twice is still in its register the
  second time.
* *Loads* used twice may be read once into a register (`foldLimit = 1`) or twice as a
  memory operand.

Every candidate goes through the same checker (`check`, proved sound), so the search cannot
change what a block computes. It can only change how long the block takes.

Results, same machine and method as the table:

| | Before | After |
|---|---:|---:|
| spill stores per body, radix 16 middle pass | 57 | 1 |
| spill stores per body, radix 32 last pass | 211 | 71 |
| time of the radix-16 middle and last passes | 1 | 0.73–0.82 |
| time of the radix-32 first and last passes | 1 | 0.76–0.83 |
| time of the radix-8 passes | 1 | 0.92–1.04 |
| whole transform, `N = 4096 … 16384` | 1 | 0.80–0.86 |
| whole transform, geometric mean over `N = 16 … 2^18` (powers of two) | 1 | 0.93 |

The eager order is what removed the spills. Choosing by micro-operations is what made it
safe to add: with the old instruction count as the criterion, the same candidates made
`N = 64` 21% slower and left the mean unchanged (0.999), because the shortest listing is
often the one with the most memory operands.

Two things were tried and are not used:

* *Constants in registers.* A constant used many times can sit in a register while one is
  free (`ACfg.constReg`). This removes a tenth of the micro-operations of the radix-16 and
  radix-32 passes (loads 112 → 76 and 369 → 279) and changes their time by less than the
  noise. The option exists and is off.
* *A total-throughput term.* The measured times of the passes that are not limited by the
  shuffle port are all close to (all micro-operations) / 3.2 cycles, before and after. That
  fit predicted a 9% gain from the constants in registers, which did not appear. So the fit
  is not in the model, and the criterion "fewest micro-operations" is a heuristic that the
  measurements support for spills and not for memory operands.

## What the model does not see

* **Dependencies.** A schedule in the model may run an operation before its operands. The
  real processor cannot, and its window is finite (a pass body of several hundred
  micro-operations does not fit in the scheduler at once), so the order of instructions
  matters beyond the counts.
* **Limits that are not ports.** Renaming and retirement handle a few micro-operations per
  cycle whatever their ports, and a virtual processor may share its core. In
  microbenchmarks on the test machine eight loads take 4 cycles and eight additions take 4,
  but the sixteen together take 5.5 to 6, not 4. The machine has no performance counters,
  so the cause is not known, and nothing of this is in the proved model.
* **Memory.** Cache misses, translation misses and store-to-load forwarding. The lane-store
  experiment is the example: the port count was right about the limit and silent about
  when the cache makes it worse.
* **The clock.** 512-bit code runs at a lower frequency on these cores; `calib` measures the
  cycle instead of assuming it.

## Where this could go

The bound is a relaxation: it drops the dependency constraints. Keeping them gives the
classical bound `max(critical path, work / ports)` and, with a finite window, a model in
which the order of instructions matters. A proved cost of that kind would let the allocator
search orders against a quantity that is both a theorem and closer to the clock. That is
not done.
