/* libbench2 backend for Intel oneMKL DFTI (competitor baseline).
 *
 * Supports complex DFTs of any rank with arbitrary strides and at most one
 * vector (howmany) dimension, in-place and out-of-place, both signs.
 * Interleaved complex only (no split arrays), double precision only.
 * Timed work is DftiComputeForward/Backward only; descriptor creation and
 * commit are setup (planning) cost, reported separately by libbench2.
 */
#include "libbench2/bench-user.h"
#include <stdio.h>
#include <string.h>
#include <mkl_dfti.h>
#include <mkl_service.h>

static const char *mkl_version(void)
{
     static char buf[256];
     MKL_Get_Version_String(buf, sizeof(buf));
     return buf;
}

BEGIN_BENCH_DOC
BENCH_DOC("name", "mkl-dfti")
BENCH_DOCF("version", mkl_version)
END_BENCH_DOC

static DFTI_DESCRIPTOR_HANDLE h = 0;

static int split_p(const bench_problem *p) { return p->split; }

int can_do(bench_problem *p)
{
     if (p->kind != PROBLEM_COMPLEX) return 0;
     if (split_p(p)) return 0;
     if (!BENCH_FINITE_RNK(p->sz->rnk) || p->sz->rnk < 1) return 0;
     if (!BENCH_FINITE_RNK(p->vecsz->rnk) || p->vecsz->rnk > 1) return 0;
     if (p->sz->rnk > 7) return 0;
     return 1;
}

static void check(MKL_LONG st, const char *what)
{
     if (st && !DftiErrorClass(st, DFTI_NO_ERROR)) {
          fprintf(stderr, "MKL %s failed: %s\n", what, DftiErrorMessage(st));
          bench_exit(1);
     }
}

void setup(bench_problem *p)
{
     int r = p->sz->rnk, i;
     MKL_LONG n[8], is[8], os[8];
     for (i = 0; i < r; ++i) {
          n[i] = p->sz->dims[i].n;
          is[i + 1] = p->sz->dims[i].is;
          os[i + 1] = p->sz->dims[i].os;
     }
     is[0] = os[0] = 0;
     if (r == 1)
          check(DftiCreateDescriptor(&h, DFTI_DOUBLE, DFTI_COMPLEX, 1, n[0]), "create");
     else
          check(DftiCreateDescriptor(&h, DFTI_DOUBLE, DFTI_COMPLEX, r, n), "create");
     check(DftiSetValue(h, DFTI_PLACEMENT, p->in_place ? DFTI_INPLACE : DFTI_NOT_INPLACE), "placement");
     check(DftiSetValue(h, DFTI_INPUT_STRIDES, is), "istrides");
     check(DftiSetValue(h, DFTI_OUTPUT_STRIDES, os), "ostrides");
     if (p->vecsz->rnk == 1) {
          check(DftiSetValue(h, DFTI_NUMBER_OF_TRANSFORMS, (MKL_LONG) p->vecsz->dims[0].n), "howmany");
          check(DftiSetValue(h, DFTI_INPUT_DISTANCE, (MKL_LONG) p->vecsz->dims[0].is), "idist");
          check(DftiSetValue(h, DFTI_OUTPUT_DISTANCE, (MKL_LONG) p->vecsz->dims[0].os), "odist");
     }
     check(DftiCommitDescriptor(h), "commit");
}

void doit(int iter, bench_problem *p)
{
     int i;
     void *in = p->in, *out = p->out;
     if (p->sign < 0) {
          if (p->in_place)
               for (i = 0; i < iter; ++i) DftiComputeForward(h, in);
          else
               for (i = 0; i < iter; ++i) DftiComputeForward(h, in, out);
     } else {
          if (p->in_place)
               for (i = 0; i < iter; ++i) DftiComputeBackward(h, in);
          else
               for (i = 0; i < iter; ++i) DftiComputeBackward(h, in, out);
     }
}

void done(bench_problem *p)
{
     UNUSED(p);
     if (h) DftiFreeDescriptor(&h);
     h = 0;
}

void main_init(int *argc, char ***argv) { UNUSED(argc); UNUSED(argv); }
void initial_cleanup(void) {}
void final_cleanup(void) {}
void cleanup(void) {}
void useropt(const char *arg) { UNUSED(arg); }
