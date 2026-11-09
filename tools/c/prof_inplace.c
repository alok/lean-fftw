/* Profiling aid: time the passes of the C in-place schedule one by one (vl 8, forward, T = 0). */
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
     double *in = aligned_alloc(64, 16 * N), *out = aligned_alloc(64, 16 * N), *tw = aligned_alloc(64, 32 * N);
     for (size_t i = 0; i < 2 * N; ++i) in[i] = out[i] = 0.0;
     for (size_t i = 0; i < 4 * N; ++i) tw[i] = 0.0;
     for (int t = 0; t < s; ++t) R[t] = atoi(argv[2 + t]);
     size_t ng = N / R[0] / vl;
     unsigned *gofs = malloc(ng * sizeof(unsigned)), ldel[8];
     /* leaf d is written at digitRev(R[1..], d) * R[0] */
     #define OFS(d) ({ size_t dd = (d), m = N / R[0], P = 0, w = 1; \
          for (int t = s - 1; t >= 1; --t) { m /= R[t]; } \
          m = N / R[0]; \
          for (int t = 1; t < s; ++t) { m /= R[t]; P += (dd / m) * w; dd %= m; w *= R[t]; } \
          (unsigned)(P * R[0]); })
     for (size_t g = 0; g < ng; ++g) gofs[g] = OFS(g * vl);
     for (int l = 0; l < 8; ++l) ldel[l] = OFS(l);
     double tot = 0, t1;
     lf_leaf_fn f = lf_get_leaf(R[0], vl, 1);
     t1 = TIME(f(in, out, N, gofs, ldel, 0, ng, 1)); tot += t1;
     printf("leaf  R=%-3d %8.1f ns  %.2f ns/elt\n", R[0], t1 * 1e9, t1 * 1e9 / N);
     ns = R[0];
     for (int t = 1; t < s - 1; ++t) {
          lf_dit_fn m = lf_get_dit(R[t], vl, 1);
          t1 = TIME(m(out, tw, ns, ns, 0, N / (ns * R[t]), 0, ns, 0)); tot += t1;
          printf("dit   R=%-3d ns=%-6zu %8.1f ns  %.2f ns/elt\n", R[t], ns, t1 * 1e9, t1 * 1e9 / N);
          ns *= R[t];
     }
     lf_ditlast_fn l = lf_get_ditlast(R[s - 1], vl, 1);
     t1 = TIME(l(out, tw, ns, ns, 0, ns, 0)); tot += t1;
     printf("last  R=%-3d ns=%-6zu %8.1f ns  %.2f ns/elt\n", R[s - 1], ns, t1 * 1e9, t1 * 1e9 / N);
     printf("total %8.1f ns\n", tot * 1e9);
     return 0;
}
