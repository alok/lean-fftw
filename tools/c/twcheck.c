/* Measures tau, the twiddle accuracy assumed (not proved) by refTransform_error: the largest
 * error of the Lean-computed base table omega_N^m (Trig.cosSin2PiTable, the table the fast
 * engine gathers every pass table from) against long-double cos/sin, for each N given.
 * Prints the max absolute error and the max error in units of 2^-53 (relative to 1, since
 * |cos|, |sin| <= 1) per size, and the overall maximum.
 *   twcheck N...
 */
#include "lf_lean.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
     const long double tp = 6.283185307179586476925286766559005768L;
     double worst = 0;
     lf_lean_init();
     for (int i = 1; i < argc; ++i) {
          size_t N = strtoul(argv[i], 0, 10);
          double mx = 0, mrel = 0;
          for (int fwd = 0; fwd <= 1; ++fwd) {
               double *b = lf_lean_base_table(N, fwd);
               for (size_t m = 0; m < N; ++m) {
                    /* reduce exactly in integers first: angle = 2 pi m / N */
                    long double a = tp * (long double)m / (long double)N;
                    long double c = cosl(a), s = fwd ? -sinl(a) : sinl(a);
                    long double ec = fabsl((long double)b[2 * m] - c), es = fabsl((long double)b[2 * m + 1] - s);
                    double e = (double)(ec > es ? ec : es);
                    /* relative error of the complex value (|omega| = 1) */
                    if (e > mx) mx = e;
                    (void)mrel;
               }
               free(b);
          }
          if (mx > worst) worst = mx;
          printf("{\"N\":%zu,\"tau_abs\":%.3g,\"tau_ulps_of_1\":%.3f}\n", N, mx, mx / ldexp(1.0, -53));
     }
     printf("{\"max_tau_abs\":%.3g,\"max_tau_ulps_of_1\":%.3f}\n", worst, worst / ldexp(1.0, -53));
     return 0;
}
