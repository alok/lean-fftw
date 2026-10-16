/* Profiling aid: time the individual passes of a radix sequence (vl 8, forward). */
#include "lf_kernels.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
#define TIME(stmt) ({ size_t reps = 1; double best = 1e30; \
     for (;;) { double t0 = now(); for (size_t i = 0; i < reps; ++i) { stmt; } if (now() - t0 > 2e-3) break; reps *= 2; } \
     for (int k = 0; k < 9; ++k) { double t0 = now(); for (size_t i = 0; i < reps; ++i) { stmt; } double d = (now() - t0) / reps; if (d < best) best = d; } best; })

int main(int argc, char **argv)
{
     size_t N = strtoul(argv[1], 0, 10), ns;
     int s = argc - 2, R[16], vl = 8;
     double *in = aligned_alloc(64, 16 * N), *out = aligned_alloc(64, 16 * N), *a = aligned_alloc(64, 16 * N), *b = aligned_alloc(64, 16 * N), *tw = aligned_alloc(64, 32 * N);
     for (size_t i = 0; i < 2 * N; ++i) in[i] = a[i] = b[i] = 0.5;
     for (size_t i = 0; i < 4 * N; ++i) tw[i] = 0.5;
     for (int t = 0; t < s; ++t) R[t] = atoi(argv[2 + t]);
     double tot = 0, t1;
     lf_first_fn f = lf_get_first(R[0], vl, 1);
     t1 = TIME(f(in, a, a + N, N)); tot += t1;
     printf("first R=%-3d %8.1f ns  %.2f ns/elt\n", R[0], t1 * 1e9, t1 * 1e9 / N);
     ns = R[0];
     for (int t = 1; t < s - 1; ++t) {
          lf_mid_fn m = lf_get_mid(R[t], vl, 1);
          t1 = TIME(m(a, a + N, b, b + N, tw, N, ns)); tot += t1;
          printf("mid   R=%-3d ns=%-6zu %8.1f ns  %.2f ns/elt\n", R[t], ns, t1 * 1e9, t1 * 1e9 / N);
          ns *= R[t];
     }
     lf_last_fn l = lf_get_last(R[s - 1], vl, 1);
     t1 = TIME(l(a, a + N, out, tw, N, ns)); tot += t1;
     printf("last  R=%-3d ns=%-6zu %8.1f ns  %.2f ns/elt\n", R[s - 1], ns, t1 * 1e9, t1 * 1e9 / N);
     printf("total %8.1f ns\n", tot * 1e9);
     return 0;
}
