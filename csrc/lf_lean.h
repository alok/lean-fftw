/* Glue between the fast engine and the Lean library (twiddles, planner, reference). */
#ifndef LF_LEAN_H
#define LF_LEAN_H
#include "lf_fast.h"

/* Initialize the Lean runtime and the LeanFFTW modules (once). */
void lf_lean_init(void);

/* Base twiddle table omega_N^m, m < N, interleaved; caller frees. */
double *lf_lean_base_table(size_t N, int fwd);

/* Lean Float reference of the plan R[0..s-1] (LeanFFTW.Gen.refTransform). */
void lf_lean_reference(size_t N, int fwd, int s, const int *R, const double *in, double *out);

/* Enumerate radix sequences covered by generated kernels; calls f for each. */
void lf_enumerate(size_t N, int fwd, void (*f)(int s, const int *R, void *ctx), void *ctx);

/* Planner: time every candidate (min over repetitions) and keep the fastest.
   If R_out is non-null, the chosen sequence is stored there and its length in *s_out. */
lf_plan *lf_plan_measure(size_t N, int fwd, int *s_out, int *R_out);

#endif
