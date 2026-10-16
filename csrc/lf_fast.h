/* The fast engine: plans of vectorized Stockham passes over the generated kernels.
   1-D complex DFT of size N, unit stride, interleaved, in-place or out-of-place. */
#ifndef LF_FAST_H
#define LF_FAST_H
#include <stddef.h>

#define LF_MAXPASS 24

typedef struct lf_plan lf_plan;

/* Vector length usable for the radix sequence R[0..s-1] (product N), or 0 if no
   generated kernels cover it. s = 1 means a single scalar small transform. */
int lf_radices_vl(size_t N, int fwd, int s, const int *R);

/* Build a plan for the radix sequence. base[2m], base[2m+1] = re, im of omega_N^m (m < N),
   as computed by Lean (lfftw_fast_base_table); the pass tables are gathered from it.
   Returns NULL if unsupported. */
lf_plan *lf_plan_radices(size_t N, int fwd, int s, const int *R, const double *base);

/* Execute: in and out are interleaved arrays of N complex values; in == out allowed. */
void lf_execute(const lf_plan *p, const double *in, double *out);

void lf_destroy(lf_plan *p);

/* Number of doubles of the twiddle tables of a radix sequence. */
size_t lf_twiddle_size(size_t N, int s, const int *R);

#endif
