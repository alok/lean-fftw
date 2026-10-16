/* Executor of the fast engine (hand-written; trusted data movement only, no arithmetic). */
#include "lf_fast.h"
#include "lf_kernels.h"
#include <stdlib.h>
#include <string.h>

struct lf_plan {
     size_t N;
     int fwd, s, vl, mode;
     int R[LF_MAXPASS];
     lf_small_fn small;
     /* LF_FUSED */
     lf_fused_fn fused;
     /* LF_STOCKHAM */
     lf_first_fn first;
     lf_mid_fn mid[LF_MAXPASS];
     lf_last_fn last;
     /* LF_INPLACE */
     lf_leaf_fn leaf;
     lf_dit_fn dit[LF_MAXPASS];
     lf_ditlast_fn ditlast;
     unsigned *gofs, ldel[8];
     double *tw;            /* all twiddle tables */
     size_t twoff[LF_MAXPASS];
     double *buf;           /* LF_STOCKHAM: two split work arrays, 4N doubles;
                               LF_INPLACE: copy of the input when in == out, 2N doubles */
};

size_t lf_twiddle_size(size_t N, int s, const int *R)
{
     size_t ns = 1, tot = 0;
     for (int t = 0; t < s; ++t) {
          if (t >= 1) tot += 2 * (size_t)(R[t] - 1) * ns;
          ns *= (size_t)R[t];
     }
     (void)N;
     return tot;
}

/* Kernels exist and the divisibility conditions of the passes hold for vector length vl. */
static int try_vl(size_t N, int fwd, int s, const int *R, int vl, int mode)
{
     size_t ns = 1;
     if (mode == LF_STOCKHAM ? !lf_get_first(R[0], vl, fwd) : !lf_get_leaf(R[0], vl, fwd)) return 0;
     if (R[0] % vl) return 0;
     for (int t = 0; t < s; ++t) {
          if ((N / (size_t)R[t]) % (size_t)vl) return 0;
          if (t >= 1) {
               if (ns % (size_t)vl) return 0;
               if (mode == LF_STOCKHAM) {
                    if (t < s - 1 && !lf_get_mid(R[t], vl, fwd)) return 0;
                    if (t == s - 1 && !lf_get_last(R[t], vl, fwd)) return 0;
               } else {
                    if (t < s - 1 && !lf_get_dit(R[t], vl, fwd)) return 0;
                    if (t == s - 1 && !lf_get_ditlast(R[t], vl, fwd)) return 0;
               }
          }
          ns *= (size_t)R[t];
     }
     return ns == N;
}

int lf_mode_vl(size_t N, int fwd, int s, const int *R, int mode)
{
     static const int vls[] = { 8, 4 };
     if (s < 1 || s > LF_MAXPASS) return 0;
     if (s == 1) return (mode == LF_STOCKHAM && (size_t)R[0] == N && (N == 1 || lf_get_small((int)N, fwd))) ? 1 : 0;
     for (int i = 0; i < 2; ++i) {
          int vl = vls[i];
          if (mode == LF_FUSED) {
               if (s == 2 && (size_t)R[0] * (size_t)R[1] == N && R[0] % vl == 0 && R[1] % vl == 0
                   && lf_get_fused(R[0], R[1], vl, fwd))
                    return vl;
          } else if (try_vl(N, fwd, s, R, vl, mode))
               return vl;
     }
     return 0;
}

/* offset of leaf d in the in-place schedule: d = r_{s-1} + R_{s-1}(r_{s-2} + ...), offset
   = sum_{t>=1} r_t ns_t */
static size_t leaf_ofs(size_t d, int s, const int *R, const size_t *nst)
{
     size_t o = 0;
     for (int t = s - 1; t >= 1; --t) {
          o += (d % (size_t)R[t]) * nst[t];
          d /= (size_t)R[t];
     }
     return o;
}

lf_plan *lf_plan_radices(size_t N, int fwd, int s, const int *R, const double *base, int mode)
{
     int vl = lf_mode_vl(N, fwd, s, R, mode);
     lf_plan *p;
     size_t nst[LF_MAXPASS];
     if (!vl) return 0;
     p = calloc(1, sizeof *p);
     p->N = N; p->fwd = fwd; p->s = s; p->vl = vl; p->mode = mode;
     memcpy(p->R, R, (size_t)s * sizeof(int));
     if (s == 1) {
          p->small = N == 1 ? 0 : lf_get_small((int)N, fwd);
          return p;
     }
     nst[0] = 1;
     for (int t = 1; t < s; ++t) nst[t] = nst[t - 1] * (size_t)R[t - 1];
     if (mode == LF_FUSED) p->fused = lf_get_fused(R[0], R[1], vl, fwd);
     else if (mode == LF_STOCKHAM) {
          p->first = lf_get_first(R[0], vl, fwd);
          for (int t = 1; t < s - 1; ++t) p->mid[t] = lf_get_mid(R[t], vl, fwd);
          p->last = lf_get_last(R[s - 1], vl, fwd);
          p->buf = aligned_alloc(64, 4 * N * sizeof(double));
     } else {
          size_t ng = N / (size_t)R[0] / (size_t)vl;
          p->leaf = lf_get_leaf(R[0], vl, fwd);
          for (int t = 1; t < s - 1; ++t) p->dit[t] = lf_get_dit(R[t], vl, fwd);
          p->ditlast = lf_get_ditlast(R[s - 1], vl, fwd);
          p->gofs = malloc(ng * sizeof(unsigned));
          for (size_t g = 0; g < ng; ++g) p->gofs[g] = (unsigned)leaf_ofs(g * (size_t)vl, s, R, nst);
          for (int l = 0; l < vl; ++l) p->ldel[l] = (unsigned)leaf_ofs((size_t)l, s, R, nst);
          p->buf = aligned_alloc(64, 2 * N * sizeof(double));
     }
     {
          /* gather each pass's table from the base table w[m] = omega_N^m:
             pass (R, ns) entry (r, k) is omega_N^(r k N/(ns R)) */
          size_t tot = lf_twiddle_size(N, s, R), ns = (size_t)R[0], off = 0;
          p->tw = aligned_alloc(64, (tot * sizeof(double) + 63) / 64 * 64 + 64);
          for (int t = 1; t < s; ++t) {
               size_t Rt = (size_t)R[t], step = N / (ns * Rt);
               p->twoff[t] = off;
               for (size_t r = 1; r < Rt; ++r)
                    for (size_t k = 0; k < ns; ++k) {
                         size_t m = r * k * step;
                         p->tw[off + 2 * (r - 1) * ns + k] = base[2 * m];
                         p->tw[off + (2 * (r - 1) + 1) * ns + k] = base[2 * m + 1];
                    }
               off += 2 * (Rt - 1) * ns;
               ns *= Rt;
          }
     }
     return p;
}

void lf_execute(const lf_plan *p, const double *in, double *out)
{
     const size_t N = p->N;
     size_t ns;
     if (p->s == 1) {
          if (p->small) p->small(in, out);
          else { out[0] = in[0]; out[1] = in[1]; }
          return;
     }
     if (p->mode == LF_FUSED) { p->fused(in, out, p->tw); return; }
     if (p->mode == LF_INPLACE) {
          const int s = p->s;
          if (in == out) { memcpy(p->buf, in, 2 * N * sizeof(double)); in = p->buf; }
          p->leaf(in, out, N, p->gofs, p->ldel, 0, N / (size_t)p->R[0] / (size_t)p->vl);
          ns = (size_t)p->R[0];
          for (int t = 1; t < s - 1; ++t) {
               p->dit[t](out, p->tw + p->twoff[t], ns, 0, N / (ns * (size_t)p->R[t]));
               ns *= (size_t)p->R[t];
          }
          p->ditlast(out, p->tw + p->twoff[s - 1], ns, 0, ns);
          return;
     }
     {
          double *src = p->buf, *dst = p->buf + 2 * N, *tmp;
          p->first(in, src, src + N, N);
          ns = (size_t)p->R[0];
          for (int t = 1; t < p->s - 1; ++t) {
               p->mid[t](src, src + N, dst, dst + N, p->tw + p->twoff[t], N, ns);
               ns *= (size_t)p->R[t];
               tmp = src; src = dst; dst = tmp;
          }
          p->last(src, src + N, out, p->tw + p->twoff[p->s - 1], N, ns);
     }
}

void lf_destroy(lf_plan *p)
{
     if (!p) return;
     free(p->tw);
     free(p->buf);
     free(p->gofs);
     free(p);
}
