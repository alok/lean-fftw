#include "lf_lean.h"
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern lean_object *lfftw_fast_base_table(lean_object *spec);
extern lean_object *lfftw_fast_reference(lean_object *spec, lean_object *inp);
extern lean_object *initialize_lean_x2dfftw_LeanFFTW_FFI(uint8_t builtin);
extern void lean_initialize_runtime_module(void);

static int inited = 0;

void lf_lean_init(void)
{
     lean_object *res;
     if (inited) return;
     inited = 1;
     lean_initialize_runtime_module();
     res = initialize_lean_x2dfftw_LeanFFTW_FFI(1);
     if (lean_io_result_is_ok(res)) lean_dec_ref(res);
     else { lean_io_result_show_error(res); lean_dec(res); abort(); }
     lean_io_mark_end_initialization();
}

static lean_object *farray(const double *x, size_t n)
{
     lean_object *a = lean_alloc_sarray(sizeof(double), n, n);
     if (n) memcpy(lean_float_array_cptr(a), x, n * sizeof(double));
     return a;
}

double *lf_lean_base_table(size_t N, int fwd)
{
     double spec[2] = { (double)N, fwd ? 1.0 : 0.0 };
     lean_object *res = lfftw_fast_base_table(farray(spec, 2));
     double *out = malloc(2 * N * sizeof(double));
     memcpy(out, lean_float_array_cptr(res), 2 * N * sizeof(double));
     lean_dec(res);
     return out;
}

void lf_lean_reference(size_t N, int fwd, int s, const int *R, const double *in, double *out)
{
     double spec[3 + LF_MAXPASS];
     lean_object *res;
     spec[0] = (double)N; spec[1] = fwd ? 1.0 : 0.0; spec[2] = (double)s;
     for (int t = 0; t < s; ++t) spec[3 + t] = (double)R[t];
     res = lfftw_fast_reference(farray(spec, 3 + (size_t)s), farray(in, 2 * N));
     memcpy(out, lean_float_array_cptr(res), 2 * N * sizeof(double));
     lean_dec(res);
}

/* ---- enumeration of radix sequences: first radix, then a monotone tail ---- */

static const int firsts[] = { 2, 4, 8, 16, 32 };
static const int mids[] = { 32, 16, 8, 4, 2 };

struct en { size_t N; int fwd; void (*f)(int, const int *, int, void *); void *ctx; int R[LF_MAXPASS]; };

static void emit_all(struct en *e, int s)
{
     for (int mode = 0; mode < LF_NMODES; ++mode)
          if (lf_mode_vl(e->N, e->fwd, s, e->R, mode)) e->f(s, e->R, mode, e->ctx);
}

/* dir = 0: non-increasing tail (mids[i] for i >= lo); dir = 1: non-decreasing and not
   constant (constant tails are enumerated by dir = 0) */
static void tail(struct en *e, int s, size_t M, int lo, int dir, int first, int strict)
{
     if (M == 1) {
          if (dir == 0 || strict) emit_all(e, s);
          return;
     }
     if (s >= LF_MAXPASS) return;
     for (int i = 0; i < (int)(sizeof mids / sizeof mids[0]); ++i) {
          if (dir == 0 ? i < lo : i > lo) continue;
          if (M % (size_t)mids[i] == 0) {
               e->R[s] = mids[i];
               tail(e, s + 1, M / (size_t)mids[i], i, dir, 0, strict || (!first && i != lo));
          }
     }
}

void lf_enumerate(size_t N, int fwd, void (*f)(int, const int *, int, void *), void *ctx)
{
     struct en e = { N, fwd, f, ctx, { 0 } };
     e.R[0] = (int)N;
     if (lf_mode_vl(N, fwd, 1, e.R, LF_STOCKHAM)) f(1, e.R, 0, ctx);
     for (size_t i = 0; i < sizeof firsts / sizeof firsts[0]; ++i)
          if (N % (size_t)firsts[i] == 0 && N > (size_t)firsts[i]) {
               e.R[0] = firsts[i];
               tail(&e, 1, N / (size_t)firsts[i], 0, 0, 1, 0);
               tail(&e, 1, N / (size_t)firsts[i], 4, 1, 1, 0);
          }
}

/* ---- measuring planner ---- */

static double now(void)
{
     struct timespec ts;
     clock_gettime(CLOCK_MONOTONIC, &ts);
     return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* min over k measurements of >= tmin seconds each */
static double time_plan(const lf_plan *p, const double *in, double *out, int k, double tmin)
{
     double t = 1e30;
     size_t reps = 1;
     lf_execute(p, in, out);
     for (;;) {
          double t0 = now();
          for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out);
          if (now() - t0 >= tmin || reps >= (1u << 24)) break;
          reps *= 2;
     }
     for (int j = 0; j < k; ++j) {
          double t0 = now(), d;
          for (size_t i = 0; i < reps; ++i) lf_execute(p, in, out);
          d = (now() - t0) / (double)reps;
          if (d < t) t = d;
     }
     return t;
}

struct cand { int s, mode, T; size_t Q; int R[LF_MAXPASS]; double t; };
struct pm { size_t N; int fwd; double *base, *in, *out; struct cand *c; size_t n, cap; };

static void collect(int s, const int *R, int mode, void *ctx)
{
     struct pm *m = ctx;
     struct cand c;
     memset(&c, 0, sizeof c);
     c.s = s; c.mode = mode;
     memcpy(c.R, R, (size_t)s * sizeof(int));
     if (m->n == m->cap) { m->cap = m->cap ? 2 * m->cap : 256; m->c = realloc(m->c, m->cap * sizeof c); }
     m->c[m->n++] = c;
}

static lf_plan *build(struct pm *m, const struct cand *c)
{
     lf_plan *p = lf_plan_radices(m->N, m->fwd, c->s, c->R, m->base, c->mode);
     if (p && (c->T || c->Q) && !lf_set_blocking(p, c->T, c->Q)) { lf_destroy(p); p = 0; }
     return p;
}

static int bytime(const void *a, const void *b)
{
     double x = ((const struct cand *)a)->t, y = ((const struct cand *)b)->t;
     return x < y ? -1 : x > y;
}

lf_plan *lf_plan_measure(size_t N, int fwd, int *s_out, int *R_out)
{
     return lf_plan_measure_arrays(N, fwd, 0, 0, s_out, R_out);
}

lf_plan *lf_plan_measure_arrays(size_t N, int fwd, double *in, double *out, int *s_out, int *R_out)
{
     struct pm m;
     size_t top, n0;
     static const size_t Qs[] = { 0, 32, 128 };
     lf_plan *best = 0, *lead[4] = { 0 };
     memset(&m, 0, sizeof m);
     m.N = N; m.fwd = fwd;
     m.base = lf_lean_base_table(N, fwd);
     m.in = in ? in : aligned_alloc(64, (2 * N * sizeof(double) + 63) / 64 * 64);
     m.out = out ? out : aligned_alloc(64, (2 * N * sizeof(double) + 63) / 64 * 64);
     memset(m.in, 0, 2 * N * sizeof(double));
     lf_enumerate(N, fwd, collect, &m);
     /* 1: every radix sequence and schedule */
     for (size_t i = 0; i < m.n; ++i) {
          lf_plan *p = build(&m, &m.c[i]);
          m.c[i].t = p ? time_plan(p, m.in, m.out, 5, 2e-4) : 1e30;
          lf_destroy(p);
     }
     qsort(m.c, m.n, sizeof m.c[0], bytime);
     /* 2: cache blocking of the best in-place plans of large sizes */
     n0 = m.n;
     if (N >= (1u << 15))
          for (size_t i = 0; i < n0 && i < 8; ++i) {
               if (m.c[i].mode != LF_INPLACE) continue;
               for (int T = m.c[i].s - 3 > 1 ? m.c[i].s - 3 : 1; T < m.c[i].s; ++T)
                    for (size_t q = 0; q < sizeof Qs / sizeof Qs[0]; ++q) {
                         struct cand c = m.c[i];
                         lf_plan *p;
                         c.T = T; c.Q = Qs[q];
                         p = build(&m, &c);
                         if (!p) continue;
                         c.t = time_plan(p, m.in, m.out, 5, 2e-4);
                         lf_destroy(p);
                         if (m.n == m.cap) { m.cap *= 2; m.c = realloc(m.c, m.cap * sizeof c); }
                         m.c[m.n++] = c;
                    }
          }
     qsort(m.c, m.n, sizeof m.c[0], bytime);
     /* 3: re-time the leaders, interleaved, to reduce the effect of noise. The plans are
        built once and the winner is returned as built, with the work arrays it was timed with. */
     top = m.n < 4 ? m.n : 4;
     for (size_t i = 0; i < top; ++i) { m.c[i].t = 1e30; lead[i] = build(&m, &m.c[i]); }
     for (int round = 0; round < 3; ++round)
          for (size_t i = 0; i < top; ++i) {
               double t = lead[i] ? time_plan(lead[i], m.in, m.out, 3, 5e-4) : 1e30;
               if (t < m.c[i].t) m.c[i].t = t;
          }
     {
          size_t b = 0;
          for (size_t i = 1; i < top; ++i) if (m.c[i].t < m.c[b].t) b = i;
          for (size_t i = 0; i < top; ++i) if (i != b) lf_destroy(lead[i]);
          if (top) { best = lead[b]; m.c[0] = m.c[b]; }
     }
     if (best && s_out) { *s_out = m.c[0].s; memcpy(R_out, m.c[0].R, (size_t)m.c[0].s * sizeof(int)); }
     free(m.c); free(m.base);
     if (!in) free(m.in);
     if (!out) free(m.out);
     return best;
}
