/* Glue between C and the Lean library: runtime start-up, and the C side of the planner,
   which is Lean code (LeanFFTW/Plan/Planner.lean). Lean holds plans and arrays as raw
   pointers (USize); the lfp_* functions are the only operations it performs on them. */
#include "lf_lean.h"
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern lean_object *lfftw_fast_base_table(lean_object *spec);
extern lean_object *lfftw_fast_reference(lean_object *spec, lean_object *inp);
extern lean_object *lfftw_enumerate(size_t N, uint8_t fwd);
extern lean_object *lfftw_plan_measure(size_t N, uint8_t fwd, size_t in, size_t out, lean_object *w);
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

/* ---- the engine, as seen by the Lean planner ---- */

static int radices(b_lean_obj_arg rs, int *R)
{
     size_t s = lean_sarray_size(rs);
     const double *d = lean_float_array_cptr(rs);
     if (s < 1 || s > LF_MAXPASS) return 0;
     for (size_t t = 0; t < s; ++t) R[t] = (int)d[t];
     return (int)s;
}

uint32_t lfp_mode_vl(size_t N, uint8_t fwd, b_lean_obj_arg rs, uint8_t mode)
{
     int R[LF_MAXPASS], s = radices(rs, R);
     return s ? (uint32_t)lf_mode_vl(N, fwd, s, R, mode) : 0;
}

lean_obj_res lfp_build(size_t N, uint8_t fwd, b_lean_obj_arg rs, uint8_t mode, uint32_t T, size_t Q,
                       b_lean_obj_arg base, lean_object *w)
{
     int R[LF_MAXPASS], s = radices(rs, R);
     lf_plan *p = s ? lf_plan_radices(N, fwd, s, R, lean_float_array_cptr(base), mode) : 0;
     (void)w;
     if (p && (T || Q) && !lf_set_blocking(p, (int)T, Q)) { lf_destroy(p); p = 0; }
     return lean_io_result_mk_ok(lean_box_usize((size_t)p));
}

lean_obj_res lfp_run(size_t p, size_t in, size_t out, size_t reps, lean_object *w)
{
     (void)w;
     for (size_t i = 0; i < reps; ++i) lf_execute((const lf_plan *)p, (const double *)in, (double *)out);
     return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lfp_destroy(size_t p, lean_object *w)
{
     (void)w;
     lf_destroy((lf_plan *)p);
     return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lfp_alloc(size_t n, lean_object *w)
{
     double *a = aligned_alloc(64, (n * sizeof(double) + 63) / 64 * 64);
     (void)w;
     memset(a, 0, n * sizeof(double));
     return lean_io_result_mk_ok(lean_box_usize((size_t)a));
}

lean_obj_res lfp_free(size_t p, lean_object *w)
{
     (void)w;
     free((void *)p);
     return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lfp_zero(size_t p, size_t n, lean_object *w)
{
     (void)w;
     memset((void *)p, 0, n * sizeof(double));
     return lean_io_result_mk_ok(lean_box(0));
}

/* ---- C interface of the Lean planner ---- */

void lf_enumerate(size_t N, int fwd, void (*f)(int, const int *, int, void *), void *ctx)
{
     lean_object *a = lfftw_enumerate(N, (uint8_t)(fwd != 0));
     const double *d = lean_float_array_cptr(a);
     size_t n = lean_sarray_size(a), i = 0;
     while (i < n) {
          int s = (int)d[i], mode = (int)d[i + 1], R[LF_MAXPASS];
          for (int t = 0; t < s; ++t) R[t] = (int)d[i + 2 + t];
          f(s, R, mode, ctx);
          i += 2 + (size_t)s;
     }
     lean_dec(a);
}

lf_plan *lf_plan_measure(size_t N, int fwd, int *s_out, int *R_out)
{
     return lf_plan_measure_arrays(N, fwd, 0, 0, s_out, R_out);
}

lf_plan *lf_plan_measure_arrays(size_t N, int fwd, double *in, double *out, int *s_out, int *R_out)
{
     double *a = in ? in : aligned_alloc(64, (2 * N * sizeof(double) + 63) / 64 * 64);
     double *b = out ? out : aligned_alloc(64, (2 * N * sizeof(double) + 63) / 64 * 64);
     lean_object *res = lfftw_plan_measure(N, (uint8_t)(fwd != 0), (size_t)a, (size_t)b, lean_io_mk_world());
     lf_plan *p = 0;
     if (lean_io_result_is_ok(res)) p = (lf_plan *)lean_unbox_usize(lean_io_result_get_value(res));
     else lean_io_result_show_error(res);
     lean_dec(res);
     if (p && s_out) *s_out = lf_plan_radix_seq(p, R_out);
     if (!in) free(a);
     if (!out) free(b);
     return p;
}
