/* Interface of the generated kernels (lf_kernels_gen.c, emitted by LeanFFTW.Gen.Stockham). */
#ifndef LF_KERNELS_H
#define LF_KERNELS_H
#include <stddef.h>

/* first pass (ns = 1): interleaved in -> split (ore, oim) */
typedef void (*lf_first_fn)(const double *restrict in, double *restrict ore, double *restrict oim, size_t N);
/* middle pass: split -> split, twiddled */
typedef void (*lf_mid_fn)(const double *restrict ire, const double *restrict iim, double *restrict ore,
                          double *restrict oim, const double *restrict tw, size_t N, size_t ns);
/* last pass: split -> interleaved out, twiddled */
typedef void (*lf_last_fn)(const double *restrict ire, const double *restrict iim, double *restrict out,
                           const double *restrict tw, size_t N, size_t ns);
/* whole small transform, interleaved -> interleaved, in == out allowed */
typedef void (*lf_small_fn)(const double *in, double *out);

/* whole transform N = R1*R2 in registers, interleaved -> interleaved, in == out allowed;
   tw is the twiddle table of pass 1 of the plan [R1, R2] */
typedef void (*lf_fused_fn)(const double *in, double *out, const double *restrict tw);

lf_fused_fn lf_get_fused(int R1, int R2, int vl, int fwd);
lf_first_fn lf_get_first(int R, int vl, int fwd);
lf_mid_fn lf_get_mid(int R, int vl, int fwd);
lf_last_fn lf_get_last(int R, int vl, int fwd);
lf_small_fn lf_get_small(int N, int fwd);

#endif
