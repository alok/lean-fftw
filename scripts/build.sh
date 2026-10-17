#!/bin/sh
# Build the fast engine, the differential test and the libbench2 benchmark binary.
#   LEAN=<lean 4.35.0 toolchain dir> FFTW_SRC=<fftw-3.3.10 source tree, configured and built
#   (for libbench2.a only)> OUT=<build dir> scripts/build.sh
set -e
: "${LEAN:?set LEAN}" "${OUT:?set OUT}"
mkdir -p "$OUT"
lake build LeanFFTWExec:static
LIB=.lake/build/lib/liblean_x2dfftw_LeanFFTWExec.a
gcc -O2 -march=native -ffp-contract=off -Werror=incompatible-pointer-types \
    -c csrc/lf_kernels_gen.c -o "$OUT/lf_kernels_gen.o"
gcc -O2 -Wall -march=native -ffp-contract=off -c csrc/lf_fast.c -o "$OUT/lf_fast.o"
gcc -O2 -Wall -ffp-contract=off -I"$LEAN/include" -c csrc/lf_lean.c -o "$OUT/lf_lean.o"
gcc -O2 -Wall -ffp-contract=off -I"$LEAN/include" -c csrc/test_fast.c -o "$OUT/test_fast.o"
OBJS="$OUT/lf_lean.o $OUT/lf_fast.o $OUT/lf_kernels_gen.o"
"$LEAN/bin/leanc" -o "$OUT/test_fast" "$OUT/test_fast.o" $OBJS $LIB -lm
if [ -n "$FFTW_SRC" ]; then
     gcc -O2 -Wall -ffp-contract=off -I"$FFTW_SRC/libbench2" -I"$FFTW_SRC" -I"$LEAN/include" \
         -Icsrc -c bench/backends/bench-leanfftw.c -o "$OUT/bench-leanfftw.o"
     "$LEAN/bin/leanc" -o "$OUT/bench-lean" "$OUT/bench-leanfftw.o" $OBJS $LIB \
         "$FFTW_SRC/libbench2/libbench2.a" -lm
fi
