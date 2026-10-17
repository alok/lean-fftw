/* Show the plan the measuring planner picks for size N, and time it. */
#include "lf_fast.h"
#include "lf_lean.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

int main(int argc, char **argv)
{
     size_t N = strtoul(argv[1], 0, 10);
     int s, R[LF_MAXPASS], mode, T; size_t Q;
     lf_lean_init();
     double *in = aligned_alloc(64, 16 * N + 64), *out = aligned_alloc(64, 16 * N + 64);
     double t0 = now();
     lf_plan *p = lf_plan_measure_arrays(N, 1, in, out, &s, R);
     double tp = now() - t0;
     lf_plan_info(p, &mode, &T, &Q);
     for (size_t i = 0; i < 2 * N; ++i) in[i] = 0;
     if (getenv("HP")) { FILE *f = fopen("/proc/self/smaps_rollup", "r"); char l[256]; while (fgets(l, sizeof l, f)) if (strstr(l, "AnonHuge")) fputs(l, stdout); fclose(f); }
     size_t reps = 1; double best = 1e30;
     for (;;) { double a = now(); for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out); if (now() - a > 1e-2) break; reps *= 2; }
     for (int k = 0; k < 8; ++k) { double a = now(); for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out); double d = (now() - a) / reps; if (d < best) best = d; }
     printf("N=%zu mode=%d T=%d Q=%zu R=", N, mode, T, Q);
     for (int t = 0; t < s; ++t) printf("%d%s", R[t], t + 1 < s ? "x" : "");
     printf("  plan %.2fs  time %.1f ns\n", tp, best * 1e9);
     return 0;
}
