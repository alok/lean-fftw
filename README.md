# Lean FFTW

An FFTW-class FFT library implemented in Lean 4, with kernel-checked correctness proofs.
FFTW is used only as a benchmark competitor and test oracle; the library never calls it.

**Status: work in progress.** The full write-up (theorems, trust boundary, benchmark
results and the optimization GIF) will replace this file when the work is complete. Until
then see:

* `docs/CONTRACT.md` — supported problem space and exclusions
* `docs/FFTW_INVENTORY.md` — FFTW's feature and test surface, and what is covered
* `docs/BENCHMARK_PROTOCOL.md` — the predeclared benchmark protocol
* `docs/ITERATIONS.md` — every optimization iteration, including failed attempts
* `scripts/Axioms.lean` — axiom audit of the main theorems
