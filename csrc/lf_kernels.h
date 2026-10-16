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

/* in-place schedule (blocked layout: VL re, VL im per block of VL complex numbers) */
typedef void (*lf_leaf_fn)(const double *restrict in, double *restrict out, size_t N,
                           const unsigned *restrict gofs, const unsigned *restrict ldel, size_t g0, size_t gn, size_t gs);
/* blocks b in [b0,b1) of size ns*R, butterflies q in [q0,q1) of each; twiddle (r, q) is at
   tw[2(r-1) tns + q + tq] (re) and tw[(2(r-1)+1) tns + q + tq] (im) */
typedef void (*lf_dit_fn)(double *x, const double *restrict tw, size_t ns, size_t tns, size_t b0, size_t b1,
                          size_t q0, size_t q1, size_t tq);
typedef void (*lf_ditlast_fn)(double *x, const double *restrict tw, size_t ns, size_t tns, size_t q0, size_t q1, size_t tq);
lf_leaf_fn lf_get_leaf(int R, int vl, int fwd);
lf_dit_fn lf_get_dit(int R, int vl, int fwd);
lf_ditlast_fn lf_get_ditlast(int R, int vl, int fwd);

/* whole transform N = R1*R2 on interleaved vectors of vlc complex numbers (twiddles are
   constants), in == out allowed */
typedef void (*lf_cfused_fn)(const double *in, double *out);
lf_cfused_fn lf_get_cfused(int R1, int R2, int vlc, int fwd);

lf_fused_fn lf_get_fused(int R1, int R2, int vl, int fwd);
lf_first_fn lf_get_first(int R, int vl, int fwd);
lf_mid_fn lf_get_mid(int R, int vl, int fwd);
lf_last_fn lf_get_last(int R, int vl, int fwd);
lf_small_fn lf_get_small(int N, int fwd);

#endif
