/* Profiling aid: time the cache-blocking options of an in-place plan. */
#include "lf_fast.h"
#include "lf_lean.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static double timeit(lf_plan *p, double *in, double *out)
{
     size_t reps = 1; double best = 1e30;
     for (;;) { double t0 = now(); for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out); if (now() - t0 > 5e-3) break; reps *= 2; }
     for (int k = 0; k < 7; ++k) { double t0 = now(); for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out); double d = (now() - t0) / reps; if (d < best) best = d; }
     return best;
}

extern int lf_dbg_phase;
int main(int argc, char **argv)
{
     size_t N = strtoul(argv[1], 0, 10);
     int s = argc - 2, R[32];
     static const size_t Qs[] = { 0, 8, 16, 32, 64, 128, 256, 1024 };
     for (int t = 0; t < s; ++t) R[t] = atoi(argv[2 + t]);
     lf_lean_init();
     double *base = lf_lean_base_table(N, 1), *in = aligned_alloc(64, 16 * N), *out = aligned_alloc(64, 16 * N);
     for (size_t i = 0; i < 2 * N; ++i) in[i] = (double)(i % 7) - 3.0;
     lf_plan *p = lf_plan_radices(N, 1, s, R, base, LF_INPLACE);
     if (!p) { puts("no plan"); return 1; }
     for (int T = 0; T < s; ++T)
          for (size_t qi = 0; qi < sizeof Qs / sizeof Qs[0]; ++qi)
               if (lf_set_blocking(p, T, Qs[qi])) {
                    double a, b, c;
                    lf_dbg_phase = 0; a = timeit(p, in, out);
                    lf_dbg_phase = 1; b = timeit(p, in, out);
                    lf_dbg_phase = 2; c = timeit(p, in, out);
                    printf("T=%d Q=%-5zu %10.1f ns  (inner %10.1f, outer %10.1f)\n", T, Qs[qi], a * 1e9, b * 1e9, c * 1e9);
               }
     return 0;
}
