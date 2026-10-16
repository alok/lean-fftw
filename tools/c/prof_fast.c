/* Profiling aid: time every enumerated plan of size N and the passes of the best one. */
#include "lf_fast.h"
#include "lf_lean.h"
#include "lf_kernels.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

struct ctx { size_t N; double *base, *in, *out; int n; struct { double t; int s, fuse, R[LF_MAXPASS]; } r[512]; };

static double timeit(lf_plan *p, double *in, double *out)
{
     size_t reps = 1; double best = 1e30;
     for (;;) { double t0 = now(); for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out); if (now() - t0 > 2e-3) break; reps *= 2; }
     for (int k = 0; k < 9; ++k) { double t0 = now(); for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out); double d = (now() - t0) / reps; if (d < best) best = d; }
     return best;
}

static void f(int s, const int *R, int fuse, void *v)
{
     struct ctx *c = v;
     lf_plan *p = lf_plan_radices(c->N, 1, s, R, c->base, fuse);
     if (!p) return;
     c->r[c->n].t = timeit(p, c->in, c->out); c->r[c->n].s = s; c->r[c->n].fuse = fuse;
     memcpy(c->r[c->n].R, R, s * sizeof(int)); c->n++;
     lf_destroy(p);
}

static int cmp(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return x < y ? -1 : x > y; }

int main(int argc, char **argv)
{
     size_t N = strtoul(argv[1], 0, 10);
     int top = argc > 2 ? atoi(argv[2]) : 8;
     static struct ctx c;
     lf_lean_init();
     c.N = N; c.base = lf_lean_base_table(N, 1);
     c.in = aligned_alloc(64, 16 * N + 64); c.out = aligned_alloc(64, 16 * N + 64);
     for (size_t i = 0; i < 2 * N; ++i) c.in[i] = (double)(i % 7) - 3.0;
     lf_enumerate(N, 1, f, &c);
     qsort(c.r, c.n, sizeof c.r[0], cmp);
     for (int i = 0; i < c.n && i < top; ++i) {
          printf("%9.3f ns  %s", c.r[i].t * 1e9, (const char *[]){"", "fused ", "inplace "}[c.r[i].fuse]);
          for (int t = 0; t < c.r[i].s; ++t) printf("%d%s", c.r[i].R[t], t + 1 < c.r[i].s ? "x" : "");
          printf("   %.2f Gflop/s\n", 5.0 * N * __builtin_ctzl(N) / c.r[i].t * 1e-9);
     }
     return 0;
}
