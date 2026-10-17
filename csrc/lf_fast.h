/* The fast engine: plans of vectorized passes over the generated kernels.
   1-D complex DFT of size N, unit stride, interleaved, in-place or out-of-place. */
#ifndef LF_FAST_H
#define LF_FAST_H
#include <stddef.h>

#define LF_MAXPASS 24

typedef struct lf_plan lf_plan;

/* Schedules of a radix sequence (all compute the same operations, bit for bit):
   LF_STOCKHAM: out-of-place passes between two split work arrays;
   LF_FUSED: whole transform N = R[0]*R[1] in registers;
   LF_INPLACE: digit-reversed first pass into `out`, then in-place passes;
   LF_CFUSED: whole transform N = R[0]*R[1] on interleaved complex vectors.
   LF_CTWO: as LF_CFUSED, with the intermediate array in memory (larger N). */
enum { LF_STOCKHAM = 0, LF_FUSED = 1, LF_INPLACE = 2, LF_CFUSED = 3, LF_CTWO = 4 };
#define LF_NMODES 5

/* Vector length usable for the radix sequence R[0..s-1] (product N) in the given
   schedule, or 0 if no generated kernels cover it. s = 1 (LF_STOCKHAM only) means a
   single scalar small transform. */
int lf_mode_vl(size_t N, int fwd, int s, const int *R, int mode);

/* Build a plan for the radix sequence. base[2m], base[2m+1] = re, im of omega_N^m (m < N),
   as computed by Lean (lfftw_fast_base_table); the pass tables are gathered from it.
   Returns NULL if unsupported. */
lf_plan *lf_plan_radices(size_t N, int fwd, int s, const int *R, const double *base, int mode);

/* Execute: in and out are interleaved arrays of N complex values; in == out allowed. */
void lf_execute(const lf_plan *p, const double *in, double *out);

/* Cache blocking of an LF_INPLACE plan (a reordering of independent butterflies; the
   operations are unchanged). T = 0: pass by pass. T >= 1: the first T passes run per group
   of VL blocks of size R[0]...R[T-1], and the remaining passes run on chunks of Q
   butterflies (Q = 0: whole passes). Returns 0 (plan unchanged) if invalid. */
int lf_set_blocking(lf_plan *p, int T, size_t Q);

/* Size and schedule of a plan. */
int lf_plan_info(const lf_plan *p, int *mode, int *T, size_t *Q);

void lf_destroy(lf_plan *p);

/* Number of doubles of the twiddle tables of a radix sequence. */
size_t lf_twiddle_size(size_t N, int s, const int *R);

#endif
