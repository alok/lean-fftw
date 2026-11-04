/* Independent cross-check of Lean FFTW against FFTW, outside libbench2.
 *
 *   xcheck [-m measure|patient|exhaustive] [-w wisdomfile] [-r rounds] [-b] N...
 *
 * For each size N (forward, out of place, interleaved complex double):
 *   1. both libraries plan on their own arrays (Lean FFTW: lf_plan_measure_arrays;
 *      FFTW: fftw_plan_dft_1d with the chosen planner flag, wisdom optional);
 *   2. correctness on random inputs (uniform [-1, 1), fixed seed): both outputs are compared
 *      with a long-double FFTW (fftwl, no SIMD, ~19 significant digits) and the relative L2
 *      and max errors are printed; the Lean FFTW plan the planner picked is also compared bit
 *      for bit with the proved Lean reference (refTransform with the same radices), out of
 *      place and in place;
 *   3. timing on the same random (non-zero) inputs: rounds of interleaved blocks (Lean, FFTW,
 *      Lean, ...), each block repeating the transform for >= 10 ms; per-call time is the
 *      median over rounds; the ratio Lean/FFTW is printed per size.
 * Output is one JSON object per line.
 * -b: bit-exactness and accuracy only (no timing).
 */
#include "lf_fast.h"
#include "lf_lean.h"
#include <fftw3.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void)
{
     struct timespec ts;
     clock_gettime(CLOCK_MONOTONIC, &ts);
     return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rng = 0x2545F4914F6CDD1Dull;
static double rnd(void)
{
     rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
     return ((double)(rng >> 11) / 9007199254740992.0) * 2.0 - 1.0;
}

static int cmpd(const void *a, const void *b)
{
     double x = *(const double *)a, y = *(const double *)b;
     return x < y ? -1 : x > y;
}

/* relative L2 and max-abs (relative to max |ref|) errors against a long-double reference */
static double maxabs;
static void errs(size_t N, const double *y, const long double *ref, double *l2, double *linf)
{
     long double num = 0, den = 0, mx = 0, mref = 0;
     for (size_t i = 0; i < 2 * N; ++i) {
          long double d = (long double)y[i] - ref[i];
          num += d * d; den += ref[i] * ref[i];
          if (fabsl(d) > mx) mx = fabsl(d);
          if (fabsl(ref[i]) > mref) mref = fabsl(ref[i]);
     }
     *l2 = (double)sqrtl(num / den);
     *linf = (double)(mx / mref);
     maxabs = (double)mx;
}

typedef void (*runf)(void *ctx);
struct lctx { lf_plan *p; const double *in; double *out; };
struct fctx { fftw_plan p; };
static void runl(void *c) { struct lctx *x = c; lf_execute(x->p, x->in, x->out); }
static void runf_(void *c) { struct fctx *x = c; fftw_execute(x->p); }

static size_t calib(runf f, void *c)
{
     size_t reps = 1;
     for (;;) {
          double t0 = now();
          for (size_t i = 0; i < reps; ++i) f(c);
          if (now() - t0 >= 1e-2) return reps;
          reps *= 2;
     }
}

static double block(runf f, void *c, size_t reps)
{
     double t0 = now();
     for (size_t i = 0; i < reps; ++i) f(c);
     return (now() - t0) / (double)reps;
}

int main(int argc, char **argv)
{
     unsigned flag = FFTW_PATIENT;
     const char *mode = "patient", *wis = 0;
     int rounds = 15, bitonly = 0, i = 1;
     for (; i < argc && argv[i][0] == '-'; ++i) {
          if (!strcmp(argv[i], "-m")) {
               mode = argv[++i];
               flag = !strcmp(mode, "measure") ? FFTW_MEASURE : !strcmp(mode, "exhaustive") ? FFTW_EXHAUSTIVE : FFTW_PATIENT;
          } else if (!strcmp(argv[i], "-w")) wis = argv[++i];
          else if (!strcmp(argv[i], "-r")) rounds = atoi(argv[++i]);
          else if (!strcmp(argv[i], "-b")) bitonly = 1;
     }
     lf_lean_init();
     if (wis) fftw_import_wisdom_from_filename(wis);
     for (; i < argc; ++i) {
          size_t N = strtoul(argv[i], 0, 10), n2 = 2 * N;
          int s, R[LF_MAXPASS];
          double *li = fftw_malloc(n2 * sizeof(double)), *lo = fftw_malloc(n2 * sizeof(double));
          double *fi = fftw_malloc(n2 * sizeof(double)), *fo = fftw_malloc(n2 * sizeof(double));
          double *x = malloc(n2 * sizeof(double)), *ref = malloc(n2 * sizeof(double));
          double *ip = fftw_malloc(n2 * sizeof(double));
          long double *xl = fftwl_malloc(n2 * sizeof(long double)), *yl = fftwl_malloc(n2 * sizeof(long double));
          double tpl, tpf, l2l, lil, l2f, lif;
          int bit_oop, bit_ip;

          tpl = now();
          lf_plan *lp = lf_plan_measure_arrays(N, 1, li, lo, &s, R);
          tpl = now() - tpl;
          tpf = now();
          fftw_plan fp = fftw_plan_dft_1d((int)N, (fftw_complex *)fi, (fftw_complex *)fo, FFTW_FORWARD, flag);
          tpf = now() - tpf;
          fftwl_plan rp = fftwl_plan_dft_1d((int)N, (fftwl_complex *)xl, (fftwl_complex *)yl, FFTW_FORWARD, FFTW_ESTIMATE);

          for (size_t k = 0; k < n2; ++k) x[k] = rnd();
          for (size_t k = 0; k < n2; ++k) xl[k] = x[k];
          fftwl_execute(rp);
          memcpy(li, x, n2 * sizeof(double));
          memcpy(fi, x, n2 * sizeof(double));
          lf_execute(lp, li, lo);
          fftw_execute(fp);
          errs(N, lo, yl, &l2l, &lil);
          double lean_abs = maxabs;
          errs(N, fo, yl, &l2f, &lif);
          /* the chosen plan, bit for bit against the proved reference */
          lf_lean_reference(N, 1, s, R, x, ref);
          bit_oop = !memcmp(lo, ref, n2 * sizeof(double));
          memcpy(ip, x, n2 * sizeof(double));
          lf_execute(lp, ip, ip);
          bit_ip = !memcmp(ip, ref, n2 * sizeof(double));

          printf("{\"N\":%zu,\"fftw_mode\":\"%s\",\"lean_R\":\"", N, mode);
          for (int t = 0; t < s; ++t) printf("%d%s", R[t], t + 1 < s ? "x" : "");
          printf("\",\"lean_bitexact_oop\":%d,\"lean_bitexact_inplace\":%d,"
                 "\"lean_maxabs\":%.4g,\"lean_l2\":%.4g,\"fftw_l2\":%.4g,\"lean_linf\":%.4g,\"fftw_linf\":%.4g,"
                 "\"lean_plan_s\":%.3f,\"fftw_plan_s\":%.3f",
                 bit_oop, bit_ip, lean_abs, l2l, l2f, lil, lif, tpl, tpf);
          if (!bitonly) {
               struct lctx lc = { lp, li, lo };
               struct fctx fc = { fp };
               size_t rl = calib(runl, &lc), rf = calib(runf_, &fc);
               double *tl = malloc((size_t)rounds * sizeof(double)), *tf = malloc((size_t)rounds * sizeof(double));
               double *rat = malloc((size_t)rounds * sizeof(double));
               for (int r = 0; r < rounds; ++r) {
                    if (r & 1) { tf[r] = block(runf_, &fc, rf); tl[r] = block(runl, &lc, rl); }
                    else { tl[r] = block(runl, &lc, rl); tf[r] = block(runf_, &fc, rf); }
                    rat[r] = tl[r] / tf[r];
               }
               qsort(tl, (size_t)rounds, sizeof(double), cmpd);
               qsort(tf, (size_t)rounds, sizeof(double), cmpd);
               qsort(rat, (size_t)rounds, sizeof(double), cmpd);
               printf(",\"lean_ns\":%.4g,\"fftw_ns\":%.4g,\"ratio_median\":%.4f,\"ratio_q1\":%.4f,\"ratio_q3\":%.4f",
                      tl[rounds / 2] * 1e9, tf[rounds / 2] * 1e9, rat[rounds / 2], rat[rounds / 4], rat[(3 * rounds) / 4]);
               free(tl); free(tf); free(rat);
          }
          printf("}\n");
          fflush(stdout);
          lf_destroy(lp); fftw_destroy_plan(fp); fftwl_destroy_plan(rp);
          fftw_free(li); fftw_free(lo); fftw_free(fi); fftw_free(fo); fftw_free(ip);
          fftwl_free(xl); fftwl_free(yl); free(x); free(ref);
     }
     if (wis) fftw_export_wisdom_to_filename(wis);
     return 0;
}
