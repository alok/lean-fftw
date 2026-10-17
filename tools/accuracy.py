#!/usr/bin/env python3
"""libbench2 `--accuracy` per size for several implementations.

    python3 tools/accuracy.py --out DIR --impl NAME=[cd=DIR:][env=K=V:]CMD ... [--rounds 10]

Writes DIR/accuracy.json and prints a table of forward relative L2 errors (libbench2's
multiple-precision reference FFT). The protocol requires Lean FFTW's forward L2 error to be
at most 2x FFTW's at every primary size.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench import SIZES, parse_impl, run1  # noqa: E402

KEYS = ["fwd_l1", "fwd_l2", "fwd_linf", "bwd_l1", "bwd_l2", "bwd_linf"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--impl", action="append", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--problem", default="ocfN")
    ap.add_argument("--sizes", type=int, nargs="*")
    ap.add_argument("--rounds", type=int, default=10)
    ap.add_argument("--impulse-rounds", type=int, default=0)
    a = ap.parse_args()
    impls = dict(parse_impl(s) for s in a.impl)
    os.makedirs(a.out, exist_ok=True)
    res = {}
    for n in a.sizes or SIZES:
        prob = a.problem.replace("N", str(n))
        for name, impl in impls.items():
            rc, out = run1(impl, [f"--accuracy-rounds={a.rounds}",
                                  f"--impulse-accuracy-rounds={a.impulse_rounds}",
                                  f"--accuracy={prob}"])
            vals = None
            for line in out.splitlines():
                parts = line.split()
                try:
                    if len(parts) == 6:
                        vals = [float(x) for x in parts]
                except ValueError:
                    pass
            res.setdefault(name, {})[n] = dict(zip(KEYS, vals)) if vals and rc == 0 else None
            print(json.dumps({"impl": name, "n": n, "rc": rc, "err": vals}))
            sys.stdout.flush()
        with open(os.path.join(a.out, "accuracy.json"), "w") as f:
            json.dump({"problem": a.problem, "rounds": a.rounds, "results": res}, f, indent=1)


if __name__ == "__main__":
    main()
