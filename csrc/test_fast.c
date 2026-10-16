/* Differential test: every radix sequence of the fast engine against the Lean Float
   reference (LeanFFTW.Gen.refTransform), bit for bit, out-of-place and in-place. */
#include "lf_lean.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

/* relative L2 error of out against a long-double naive DFT of in (N <= 4096) */
static double l2err(size_t N, int fwd, const double *in, const double *out)
{
     long double num = 0, den = 0;
     const long double tp = 6.283185307179586476925286766559L;
     for (size_t k = 0; k < N; ++k) {
          long double re = 0, im = 0;
          for (size_t j = 0; j < N; ++j) {
               long double a = tp * (long double)((j * k) % N) / (long double)N;
               long double c = cosl(a), s = fwd ? -sinl(a) : sinl(a);
               re += c * in[2 * j] - s * in[2 * j + 1];
               im += c * in[2 * j + 1] + s * in[2 * j];
          }
          num += (re - out[2 * k]) * (re - out[2 * k]) + (im - out[2 * k + 1]) * (im - out[2 * k + 1]);
          den += re * re + im * im;
     }
     return (double)sqrtl(num / den);
}

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static double rnd(void)
{
     rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
     return ((double)(rng >> 11) / 9007199254740992.0) * 2.0 - 1.0;
}

struct tc { size_t N; int fwd; double *in, *ref, *out, *base; long nplans, nfail; int full; double maxerr; };

static void check(int s, const int *R, void *ctx)
{
     struct tc *c = ctx;
     size_t n2 = 2 * c->N;
     lf_plan *p = lf_plan_radices(c->N, c->fwd, s, R, c->base);
     int bad = 0;
     lf_lean_reference(c->N, c->fwd, s, R, c->in, c->ref);
     lf_execute(p, c->in, c->out);
     if (memcmp(c->out, c->ref, n2 * sizeof(double))) bad |= 1;
     memcpy(c->out, c->in, n2 * sizeof(double));
     lf_execute(p, c->out, c->out);
     if (memcmp(c->out, c->ref, n2 * sizeof(double))) bad |= 2;
     c->nplans++;
     if (c->N <= 4096 && c->N > 1) { double e = l2err(c->N, c->fwd, c->in, c->ref); if (e > c->maxerr) c->maxerr = e; }
     if (bad) {
          c->nfail++;
          printf("FAIL N=%zu fwd=%d bad=%d R=", c->N, c->fwd, bad);
          for (int t = 0; t < s; ++t) printf("%d ", R[t]);
          printf("\n");
     }
     lf_destroy(p);
}

int main(int argc, char **argv)
{
     int maxlg = argc > 1 ? atoi(argv[1]) : 12;
     long tot = 0, fail = 0;
     lf_lean_init();
     for (int lg = 0; lg <= maxlg; ++lg)
          for (int fwd = 0; fwd <= 1; ++fwd) {
               struct tc c;
               size_t N = (size_t)1 << lg;
               memset(&c, 0, sizeof c);
               c.N = N; c.fwd = fwd;
               c.in = malloc(2 * N * sizeof(double));
               c.ref = malloc(2 * N * sizeof(double));
               c.out = malloc(2 * N * sizeof(double));
               for (size_t i = 0; i < 2 * N; ++i) c.in[i] = rnd();
               c.base = lf_lean_base_table(N, fwd);
               lf_enumerate(N, fwd, check, &c);
               printf("N=%zu fwd=%d plans=%ld fail=%ld maxL2err=%.3g\n", N, fwd, c.nplans, c.nfail, c.maxerr);
               fflush(stdout);
               tot += c.nplans; fail += c.nfail;
               free(c.in); free(c.ref); free(c.out); free(c.base);
          }
     printf("total plans=%ld failures=%ld\n", tot, fail);
     return fail != 0;
}
