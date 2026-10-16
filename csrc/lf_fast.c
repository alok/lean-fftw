/* Executor of the fast engine (hand-written; trusted data movement only, no arithmetic). */
#include "lf_fast.h"
#include "lf_kernels.h"
#include <stdlib.h>
#include <string.h>

struct lf_plan {
     size_t N;
     int fwd, s, vl;
     int R[LF_MAXPASS];
     lf_small_fn small;
     lf_fused_fn fused;
     lf_first_fn first;
     lf_mid_fn mid[LF_MAXPASS];
     lf_last_fn last;
     double *tw;            /* all twiddle tables */
     size_t twoff[LF_MAXPASS];
     double *buf;           /* two split work arrays, 4N doubles */
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

static int try_vl(size_t N, int fwd, int s, const int *R, int vl)
{
     size_t ns = 1;
     if (!lf_get_first(R[0], vl, fwd)) return 0;
     for (int t = 0; t < s; ++t) {
          if ((N / (size_t)R[t]) % (size_t)vl) return 0;
          if (t >= 1) {
               if (ns % (size_t)vl) return 0;
               if (t < s - 1 && !lf_get_mid(R[t], vl, fwd)) return 0;
               if (t == s - 1 && !lf_get_last(R[t], vl, fwd)) return 0;
          }
          ns *= (size_t)R[t];
     }
     return ns == N;
}

int lf_radices_vl(size_t N, int fwd, int s, const int *R)
{
     if (s < 1 || s > LF_MAXPASS) return 0;
     if (s == 1) return ((size_t)R[0] == N && (N == 1 || lf_get_small((int)N, fwd))) ? 1 : 0;
     if (try_vl(N, fwd, s, R, 8)) return 8;
     if (try_vl(N, fwd, s, R, 4)) return 4;
     return 0;
}

int lf_fused_vl(size_t N, int fwd, int s, const int *R)
{
     static const int vls[] = { 8, 4 };
     if (s != 2 || (size_t)R[0] * (size_t)R[1] != N) return 0;
     for (int i = 0; i < 2; ++i)
          if (R[0] % vls[i] == 0 && R[1] % vls[i] == 0 && lf_get_fused(R[0], R[1], vls[i], fwd))
               return vls[i];
     return 0;
}

lf_plan *lf_plan_radices(size_t N, int fwd, int s, const int *R, const double *base, int fuse)
{
     int vl = fuse ? lf_fused_vl(N, fwd, s, R) : lf_radices_vl(N, fwd, s, R);
     lf_plan *p;
     if (!vl) return 0;
     p = calloc(1, sizeof *p);
     p->N = N; p->fwd = fwd; p->s = s; p->vl = vl;
     memcpy(p->R, R, (size_t)s * sizeof(int));
     if (s == 1) {
          p->small = N == 1 ? 0 : lf_get_small((int)N, fwd);
          return p;
     }
     if (fuse) p->fused = lf_get_fused(R[0], R[1], vl, fwd);
     else p->first = lf_get_first(R[0], vl, fwd);
     for (int t = 1; t < s - 1; ++t) p->mid[t] = lf_get_mid(R[t], vl, fwd);
     p->last = lf_get_last(R[s - 1], vl, fwd);
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
     if (!fuse) p->buf = aligned_alloc(64, 4 * N * sizeof(double));
     return p;
}

void lf_execute(const lf_plan *p, const double *in, double *out)
{
     const size_t N = p->N;
     double *src, *dst, *tmp;
     size_t ns;
     if (p->s == 1) {
          if (p->small) p->small(in, out);
          else { out[0] = in[0]; out[1] = in[1]; }
          return;
     }
     if (p->fused) { p->fused(in, out, p->tw); return; }
     src = p->buf; dst = p->buf + 2 * N;
     p->first(in, src, src + N, N);
     ns = (size_t)p->R[0];
     for (int t = 1; t < p->s - 1; ++t) {
          p->mid[t](src, src + N, dst, dst + N, p->tw + p->twoff[t], N, ns);
          ns *= (size_t)p->R[t];
          tmp = src; src = dst; dst = tmp;
     }
     p->last(src, src + N, out, p->tw + p->twoff[p->s - 1], N, ns);
}

void lf_destroy(lf_plan *p)
{
     if (!p) return;
     free(p->tw);
     free(p->buf);
     free(p);
}
