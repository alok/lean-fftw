#!/usr/bin/env python3
"""Measures kappa, the constant accuracy assumed (not proved) by the binary64 error theorems:
the largest relative error of the generated kernel constants against a 200-bit reference.

    lake env lean --run scripts/ErrorBound.lean consts 64 > consts.txt
    python3 tools/kappa.py consts.txt          # needs mpmath
"""
import struct
import sys

import mpmath as mp

mp.mp.prec = 200
worst, where = mp.mpf(0), None
n_consts = 0
for line in open(sys.argv[1]):
    name, k, n, bits = line.split()
    k, n = int(k), int(n)
    f = mp.mpf(struct.unpack("<d", struct.pack("<Q", int(bits)))[0])
    exact = {"cos": mp.cos, "sin": mp.sin, "tan": mp.tan}[name](2 * mp.pi * k / n)
    n_consts += 1
    if exact == 0:
        assert f == 0, line
        continue
    rel = abs((f - exact) / exact)
    if rel > worst:
        worst, where = rel, line.strip()
u = mp.mpf(2) ** -53
print(f"{n_consts} constants; max relative error {mp.nstr(worst, 5)} = {mp.nstr(worst / u, 4)} u "
      f"(u = 2^-53), at {where}")
