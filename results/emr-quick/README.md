# Quick measurements, Emerald Rapids VM, 2026-11-10

Not protocol runs: interleaved rounds, minimum per program, a shared virtual machine with
4 virtual CPUs (noise of 10% between rounds). Times in ns unless a unit is given.

* `pow2-allocator.txt`: powers of two, one core (cpu 2), best of 5. `bench-lean.old` is commit
  `79069f3`; `bench-lean.e0` has the eager orders with the old criterion (fewest
  instructions); `bench-lean` is commit `448cc39` (fewest micro-operations). Ratios are to
  `bench-lean.old`.
* `nonpow2-inplace.txt`: sizes that are not powers of two, one core, best of 3. `fftw` is
  FFTW 3.3.10 in patient mode, planned on the spot; `bench-lean.old` is commit `79069f3`;
  `bench-lean` is commit `07722b7`. Ratios are to `fftw`.
* `threads.txt`: 1, 2 and 4 threads (pinned to cpu 2, cpus 2–3, all four), best of 4.
  FFTW 3.3.10 built with `--enable-threads`, patient mode with wisdom kept per thread count;
  `asm` is commit `07722b7`, planned on every run. `r` is asm / fftw.
