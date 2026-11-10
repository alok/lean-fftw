#!/bin/sh
# Build the engine, its tests and the libbench2 benchmark binary.
#   LEAN=<lean 4.35.0 toolchain dir> FFTW_SRC=<fftw-3.3.10 source tree, configured and built
#   (for libbench2.a only)> OUT=<build dir> scripts/build.sh
# The only C compiled here is the adapter that plugs the library into FFTW's benchmark
# program (bench/backends); the engine itself is assembly written by Lean.
set -e
: "${LEAN:?set LEAN}" "${OUT:?set OUT}"
mkdir -p "$OUT"
lake build LeanFFTWExec:static gen_asm
# the assembly engine: generated, checked and printed by Lean, assembled by `as`
mkdir -p .lake/build/asm
.lake/build/bin/gen_asm .lake/build/asm/lf_asm.s
as .lake/build/asm/lf_asm.s -o .lake/build/asm/lf_asm.o
lake build asm_test
cp .lake/build/bin/asm_test "$OUT/asm_test"
LIB=.lake/build/lib/liblean_x2dfftw_LeanFFTWExec.a
if [ -n "$FFTW_SRC" ]; then
     gcc -O2 -Wall -I"$FFTW_SRC/libbench2" -I"$FFTW_SRC" -I"$LEAN/include" \
         -c bench/backends/bench-leanfftw.c -o "$OUT/bench-leanfftw.o"
     "$LEAN/bin/leanc" -o "$OUT/bench-lean" "$OUT/bench-leanfftw.o" .lake/build/asm/lf_asm.o $LIB \
         "$FFTW_SRC/libbench2/libbench2.a" -lm
fi
