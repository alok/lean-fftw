/* libbench2 backend for the Lean FFTW library: the fast engine (Lean-generated SIMD
 * Stockham kernels, see csrc/) for 1-D complex power-of-two transforms with unit stride,
 * interleaved, in-place or out-of-place, and the generic engine for everything else.
 *
 * Generic engine (pure Lean, compiled by Lean):
 *
 * Covers FFTW's whole problem space for double precision: complex DFT, rdft2 (r2c/c2r)
 * and all r2r kinds, any rank and vector rank, any strides, interleaved or split,
 * in-place or out-of-place. The transform is computed entirely by Lean code
 * (the LeanFFTW.Core modules); this file only marshals buffers.
 *
 * Buffer convention (shared with LeanFFTW/FFI.lean): every element address is
 *   base + sum(index_d * stride_d)   (in units of double),
 * with separate bases for real and imaginary parts. The spanned range of doubles is
 * copied into a Lean FloatArray before the call and the output range copied back after.
 */
#include "libbench2/bench-user.h"
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>
#include "lf_lean.h"

extern lean_object *lfftw_generic_plan(lean_object *spec);
extern lean_object *lfftw_generic_exec(lean_object *pp, lean_object *inp, lean_object *out);
extern lean_object *initialize_lean_x2dfftw_LeanFFTW_FFI(uint8_t builtin);
extern void lean_initialize_runtime_module(void);

BEGIN_BENCH_DOC
BENCH_DOC("name", "lean-fftw")
BENCH_DOC("version", "0.1.0")
BENCH_DOC("notes", "fast engine: Lean-generated AVX-512/AVX2 Stockham kernels; generic Lean engine elsewhere")
END_BENCH_DOC

typedef struct {
     double *re, *im;   /* bases (im unused for real data) */
     int real;          /* real data */
     int scale;         /* stride multiplier to doubles */
} side;

static lean_object *plan = 0;
static side sin_, sout;
static double *in_lo, *out_lo;     /* start of copied ranges */
static size_t in_len, out_len;     /* lengths in doubles */
static double in_offre, in_offim, out_offre, out_offim;

static int kind_code(const bench_problem *p)
{
     switch (p->kind) {
     case PROBLEM_COMPLEX: return 0;
     case PROBLEM_REAL: return 1;
     default: return 2;
     }
}

int can_do(bench_problem *p)
{
     int i;
     if (!BENCH_FINITE_RNK(p->sz->rnk) || !BENCH_FINITE_RNK(p->vecsz->rnk)) return 0;
     for (i = 0; i < p->sz->rnk; ++i) if (p->sz->dims[i].n <= 0) return 0;
     for (i = 0; i < p->vecsz->rnk; ++i) if (p->vecsz->dims[i].n <= 0) return 0;
     if (p->kind == PROBLEM_REAL && p->sz->rnk < 1) return 0;
     if (p->kind == PROBLEM_R2R)
          for (i = 0; i < p->sz->rnk; ++i)
               if (p->k[i] == R2R_REDFT00 && p->sz->dims[i].n < 2) return 0;
     return 1;
}

/* split-format imaginary base offsets, mirroring libbench2's verify code */
static void mksides(bench_problem *p)
{
     double *ri = (double *) p->in, *ro = (double *) p->out;
     if (p->kind == PROBLEM_COMPLEX) {
          sin_.real = sout.real = 0;
          if (p->split) {
               sin_.re = ri; sin_.im = p->ini ? (double *) p->ini : ri + p->iphyssz;
               sout.re = ro; sout.im = p->outi ? (double *) p->outi : ro + p->ophyssz;
               sin_.scale = sout.scale = 1;
          } else {
               sin_.re = ri; sin_.im = ri + 1;
               sout.re = ro; sout.im = ro + 1;
               sin_.scale = sout.scale = 2;
          }
     } else if (p->kind == PROBLEM_R2R) {
          sin_.real = sout.real = 1;
          sin_.re = sin_.im = ri; sout.re = sout.im = ro;
          sin_.scale = sout.scale = 1;
     } else {
          int n2 = (int) (tensor_sz(p->sz) * tensor_sz(p->vecsz));
          int nl = p->sz->dims[p->sz->rnk - 1].n;
          side *cs, *rs;
          double *cb;
          n2 = (n2 / nl) * (nl / 2 + 1);
          if (p->sign < 0) { rs = &sin_; cs = &sout; cb = ro; rs->re = rs->im = ri; }
          else { rs = &sout; cs = &sin_; cb = ri; rs->re = rs->im = ro; }
          rs->real = 1; rs->scale = 1;
          cs->real = 0;
          cs->re = cb;
          if (p->split) { cs->im = cb + n2; cs->scale = 1; }
          else { cs->im = cb + 1; cs->scale = 2; }
     }
}

/* range [lo, hi] of offsets (in strides) spanned by the tensor, for input or output */
static void span(const bench_problem *p, int out, int lastHalf, long *lo, long *hi)
{
     int i;
     *lo = *hi = 0;
     for (i = 0; i < p->sz->rnk + p->vecsz->rnk; ++i) {
          const bench_iodim *d = i < p->sz->rnk ? &p->sz->dims[i] : &p->vecsz->dims[i - p->sz->rnk];
          long n = d->n;
          long s = out ? d->os : d->is;
          if (lastHalf && i == p->sz->rnk - 1) n = n / 2 + 1;
          if (n > 1) {
               if (s > 0) *hi += (n - 1) * s; else *lo += (n - 1) * s;
          }
     }
}

static void add_dim(double *spec, int *k, const bench_iodim *d, int is_mul, int os_mul)
{
     spec[(*k)++] = d->n;
     spec[(*k)++] = (double) d->is * is_mul;
     spec[(*k)++] = (double) d->os * os_mul;
}

static void generic_setup(bench_problem *p)
{
     int r = p->sz->rnk, v = p->vecsz->rnk, k = 0, i;
     long ilo, ihi, olo, ohi;
     double *a, *b;
     lean_object *spec, *res;
     double *buf;
     int nspec = 8 + 3 * (r + v) + r;

     mksides(p);
     span(p, 0, p->kind == PROBLEM_REAL && p->sign > 0, &ilo, &ihi);
     span(p, 1, p->kind == PROBLEM_REAL && p->sign < 0, &olo, &ohi);

     /* input range in doubles */
     a = sin_.re + ilo * sin_.scale; b = sin_.re + ihi * sin_.scale;
     if (!sin_.real) {
          if (sin_.im + ilo * sin_.scale < a) a = sin_.im + ilo * sin_.scale;
          if (sin_.im + ihi * sin_.scale > b) b = sin_.im + ihi * sin_.scale;
     }
     in_lo = a; in_len = (size_t) (b - a) + 1;
     in_offre = (double) (sin_.re - a); in_offim = (double) (sin_.im - a);

     a = sout.re + olo * sout.scale; b = sout.re + ohi * sout.scale;
     if (!sout.real) {
          if (sout.im + olo * sout.scale < a) a = sout.im + olo * sout.scale;
          if (sout.im + ohi * sout.scale > b) b = sout.im + ohi * sout.scale;
     }
     out_lo = a; out_len = (size_t) (b - a) + 1;
     out_offre = (double) (sout.re - a); out_offim = (double) (sout.im - a);

     spec = lean_alloc_sarray(sizeof(double), nspec, nspec);
     buf = lean_float_array_cptr(spec);
     buf[k++] = kind_code(p);
     buf[k++] = p->sign;
     buf[k++] = r;
     buf[k++] = v;
     buf[k++] = in_offre;
     buf[k++] = in_offim;
     buf[k++] = out_offre;
     buf[k++] = out_offim;
     for (i = 0; i < r; ++i) add_dim(buf, &k, &p->sz->dims[i], sin_.scale, sout.scale);
     for (i = 0; i < v; ++i) add_dim(buf, &k, &p->vecsz->dims[i], sin_.scale, sout.scale);
     for (i = 0; i < r; ++i) buf[k++] = p->kind == PROBLEM_R2R ? (double) p->k[i] : 0.0;

     res = lfftw_generic_plan(spec);
     if (lean_is_scalar(res)) {
          fprintf(stderr, "lean-fftw: problem not supported\n");
          bench_exit(1);
     }
     plan = lean_ctor_get(res, 0);
     lean_inc(plan);
     lean_dec(res);
}

static lean_object *copy_in(double *src, size_t len)
{
     lean_object *a = lean_alloc_sarray(sizeof(double), len, len);
     memcpy(lean_float_array_cptr(a), src, len * sizeof(double));
     return a;
}

static void generic_doit(int iter, bench_problem *p)
{
     int it;
     UNUSED(p);
     for (it = 0; it < iter; ++it) {
          lean_object *inp = copy_in(in_lo, in_len);
          lean_object *out = copy_in(out_lo, out_len);
          lean_object *res;
          lean_inc(plan);
          res = lfftw_generic_exec(plan, inp, out);
          memcpy(out_lo, lean_float_array_cptr(res), out_len * sizeof(double));
          lean_dec(res);
     }
}

static void generic_done(bench_problem *p)
{
     UNUSED(p);
     if (plan) lean_dec(plan);
     plan = 0;
}

void main_init(int *argc, char ***argv)
{
     UNUSED(argc); UNUSED(argv);
     lf_lean_init();
}

/* ---- fast engine ---- */

static lf_plan *fplan = 0;
static double *fin, *fout;

static int fast_ok(const bench_problem *p)
{
     size_t n;
     if (p->kind != PROBLEM_COMPLEX || p->split) return 0;
     if (p->sz->rnk != 1 || p->vecsz->rnk != 0) return 0;
     if (p->sz->dims[0].is != 1 || p->sz->dims[0].os != 1) return 0;
     n = (size_t) p->sz->dims[0].n;
     return n >= 1 && (n & (n - 1)) == 0 && n <= ((size_t) 1 << 24);
}

void setup(bench_problem *p)
{
     if (fast_ok(p)) {
          fplan = lf_plan_measure((size_t) p->sz->dims[0].n, p->sign < 0, 0, 0);
          if (fplan) {
               fin = (double *) p->in; fout = (double *) p->out;
               return;
          }
     }
     generic_setup(p);
}

void doit(int iter, bench_problem *p)
{
     if (fplan) {
          lf_plan *pl = fplan;
          const double *i = fin;
          double *o = fout;
          for (int it = 0; it < iter; ++it) lf_execute(pl, i, o);
          return;
     }
     generic_doit(iter, p);
}

void done(bench_problem *p)
{
     if (fplan) { lf_destroy(fplan); fplan = 0; return; }
     generic_done(p);
}

void initial_cleanup(void) {}
void final_cleanup(void) {}
void cleanup(void) {}
void useropt(const char *arg) { UNUSED(arg); }
