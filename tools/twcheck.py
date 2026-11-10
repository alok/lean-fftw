#!/usr/bin/env python3
"""Measures tau, the twiddle accuracy assumed (not proved) by refTransform_error: the largest
error of the base table omega_N^m that every pass table of the engine is gathered from,
against a 200-bit reference.

    asm_test twdump N... | python3 tools/twcheck.py

Prints, per size and overall, the largest absolute error of a real or imaginary part and
the same in units of 2^-53 (ulps of 1, since |cos|, |sin| <= 1).
"""
import json
import struct
import sys

from mpmath import mp, mpf, cos, sin, pi

mp.prec = 200


def dbl(bits):
    return mpf(struct.unpack("<d", struct.pack("<Q", int(bits)))[0])


worst = {}
for line in sys.stdin:
    n, fwd, m, re, im = line.split()
    n, fwd, m = int(n), int(fwd), int(m)
    a = 2 * pi * m / n
    c, s = cos(a), (-sin(a) if fwd else sin(a))
    e = max(abs(dbl(re) - c), abs(dbl(im) - s))
    worst[n] = max(worst.get(n, mpf(0)), e)
for n, e in worst.items():
    print(json.dumps({"N": n, "tau_abs": float(e), "tau_ulps_of_1": round(float(e * 2**53), 3)}))
if worst:
    e = max(worst.values())
    print(json.dumps({"max_tau_abs": float(e), "max_tau_ulps_of_1": round(float(e * 2**53), 3)}))
