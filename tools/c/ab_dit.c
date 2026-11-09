/* Development A/B test: the assembly in-place pass against the C kernel (bit-exact, timing).
   ab_dit R log2ns log2N [reps] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "lf_kernels.h"

typedef void (*lfa_fn)(const void *ctx, const double *in, double *out);
extern void lfa_dit_r2_f(const void *, const double *, double *);
extern void lfa_dit_r4_f(const void *, const double *, double *);
extern void lfa_dit_r8_f(const void *, const double *, double *);
extern void lfa_dit_r16_f(const void *, const double *, double *);
extern void lfa_dit_r32_f(const void *, const double *, double *);

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv)
{
     int R = atoi(argv[1]);
     size_t ns = (size_t)1 << atoi(argv[2]), N = (size_t)1 << atoi(argv[3]);
     int reps = argc > 4 ? atoi(argv[4]) : 5;
     size_t nb = N / (ns * R);
     double *x = aligned_alloc(64, 16 * N), *y = aligned_alloc(64, 16 * N), *x0 = aligned_alloc(64, 16 * N);
     double *twc = aligned_alloc(64, 16 * (R - 1) * ns + 64), *twa = aligned_alloc(64, 16 * (R - 1) * ns + 64);
     lf_dit_fn cfn = lf_get_dit(R, 8, 1);
     lfa_fn afn = R == 2 ? lfa_dit_r2_f : R == 4 ? lfa_dit_r4_f : R == 8 ? lfa_dit_r8_f : R == 16 ? lfa_dit_r16_f : lfa_dit_r32_f;
     size_t ctx[8];
     srand(1);
     for (size_t i = 0; i < 2 * N; ++i) x0[i] = (double)rand() / RAND_MAX - 0.5;
     for (size_t i = 0; i < 2 * (size_t)(R - 1) * ns; ++i) twc[i] = (double)rand() / RAND_MAX - 0.5;
     /* asm layout: per vector of 8 q: for r: re(8), im(8) */
     for (size_t q = 0; q < ns; q += 8)
          for (int r = 1; r < R; ++r)
               for (int l = 0; l < 8; ++l) {
                    twa[(q / 8) * (R - 1) * 16 + (r - 1) * 16 + l] = twc[2 * (r - 1) * ns + q + l];
                    twa[(q / 8) * (R - 1) * 16 + (r - 1) * 16 + 8 + l] = twc[(2 * (r - 1) + 1) * ns + q + l];
               }
     ctx[0] = (size_t)afn; ctx[1] = 0; ctx[2] = (size_t)twa; ctx[3] = 16 * ns; ctx[4] = nb; ctx[5] = ns / 8;
     ctx[6] = 16 * ns * R - 16 * ns;
     memcpy(x, x0, 16 * N); memcpy(y, x0, 16 * N);
     cfn(x, twc, ns, ns, 0, nb, 0, ns, 0);
     afn(ctx, 0, y);
     if (memcmp(x, y, 16 * N)) { printf("MISMATCH R=%d ns=%zu N=%zu\n", R, ns, N); return 1; }
     {
          double bc = 1e30, ba = 1e30;
          size_t it = (size_t)(2e8 / (double)N) + 1;
          for (int rep = 0; rep < reps; ++rep) {
               double t0 = now();
               for (size_t i = 0; i < it; ++i) cfn(x, twc, ns, ns, 0, nb, 0, ns, 0);
               double t1 = now();
               for (size_t i = 0; i < it; ++i) afn(ctx, 0, y);
               double t2 = now();
               if ((t1 - t0) / it < bc) bc = (t1 - t0) / it;
               if ((t2 - t1) / it < ba) ba = (t2 - t1) / it;
               memcpy(x, x0, 16 * N); memcpy(y, x0, 16 * N);
          }
          printf("R=%2d ns=%7zu N=%7zu  C %9.1f ns  asm %9.1f ns  asm/C %.3f  (%.3f ns/pt asm)\n", R, ns, N, bc * 1e9, ba * 1e9, ba / bc, ba * 1e9 / N);
     }
     return 0;
}
