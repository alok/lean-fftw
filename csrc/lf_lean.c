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

/* ---- enumeration of radix sequences: first radix, then a non-increasing tail ---- */

static const int firsts[] = { 4, 8, 16, 32 };
static const int mids[] = { 32, 16, 8, 4, 2 };

struct en { size_t N; int fwd; void (*f)(int, const int *, int, void *); void *ctx; int R[LF_MAXPASS]; };

static void tail(struct en *e, int s, size_t M, int maxi)
{
     if (M == 1) {
          if (lf_radices_vl(e->N, e->fwd, s, e->R)) e->f(s, e->R, 0, e->ctx);
          if (lf_fused_vl(e->N, e->fwd, s, e->R)) e->f(s, e->R, 1, e->ctx);
          return;
     }
     if (s >= LF_MAXPASS) return;
     for (int i = maxi; i < (int)(sizeof mids / sizeof mids[0]); ++i)
          if (M % (size_t)mids[i] == 0) {
               e->R[s] = mids[i];
               tail(e, s + 1, M / (size_t)mids[i], i);
          }
}

void lf_enumerate(size_t N, int fwd, void (*f)(int, const int *, int, void *), void *ctx)
{
     struct en e = { N, fwd, f, ctx, { 0 } };
     e.R[0] = (int)N;
     if (lf_radices_vl(N, fwd, 1, e.R)) { f(1, e.R, 0, ctx); return; }
     for (size_t i = 0; i < sizeof firsts / sizeof firsts[0]; ++i)
          if (N % (size_t)firsts[i] == 0 && N > (size_t)firsts[i]) {
               e.R[0] = firsts[i];
               tail(&e, 1, N / (size_t)firsts[i], 0);
          }
}

/* ---- measuring planner ---- */

static double now(void)
{
     struct timespec ts;
     clock_gettime(CLOCK_MONOTONIC, &ts);
     return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

struct pm { size_t N; int fwd; double *base, *in, *out; double best; lf_plan *bp; int s, fuse; int R[LF_MAXPASS]; };

static void try_plan(int s, const int *R, int fuse, void *ctx)
{
     struct pm *m = ctx;
     lf_plan *p = lf_plan_radices(m->N, m->fwd, s, R, m->base, fuse);
     double t = 1e30;
     size_t reps = 1;
     if (!p) return;
     lf_execute(p, m->in, m->out);
     for (;;) {   /* calibrate to >= 0.2 ms per measurement */
          double t0 = now();
          for (size_t i = 0; i < reps; ++i) lf_execute(p, m->in, m->out);
          if (now() - t0 >= 2e-4 || reps >= (1u << 24)) break;
          reps *= 2;
     }
     for (int k = 0; k < 5; ++k) {
          double t0 = now(), d;
          for (size_t i = 0; i < reps; ++i) lf_execute(p, m->in, m->out);
          d = (now() - t0) / (double)reps;
          if (d < t) t = d;
     }
     if (t < m->best) {
          lf_destroy(m->bp);
          m->bp = p; m->best = t; m->s = s; m->fuse = fuse;
          memcpy(m->R, R, (size_t)s * sizeof(int));
     } else lf_destroy(p);
}

lf_plan *lf_plan_measure(size_t N, int fwd, int *s_out, int *R_out)
{
     struct pm m;
     memset(&m, 0, sizeof m);
     m.N = N; m.fwd = fwd; m.best = 1e30;
     m.base = lf_lean_base_table(N, fwd);
     m.in = aligned_alloc(64, (2 * N * sizeof(double) + 63) / 64 * 64);
     m.out = aligned_alloc(64, (2 * N * sizeof(double) + 63) / 64 * 64);
     memset(m.in, 0, 2 * N * sizeof(double));
     lf_enumerate(N, fwd, try_plan, &m);
     free(m.base); free(m.in); free(m.out);
     if (m.bp && s_out) { *s_out = m.s; memcpy(R_out, m.R, (size_t)m.s * sizeof(int)); }
     return m.bp;
}
