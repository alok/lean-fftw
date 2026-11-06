#!/usr/bin/env python3
"""Fit and check the planner's cost model on a log of measured candidates.

  costmodel.py LOG [--K 4 8 16 32]

LOG lines are written by the Lean planner when LF_PLAN_LOG is set:
  N fwd stage mode T Q time_ns vl arith mem [R0, R1, ...]
`arith` and `mem` are the proved operation counts of the candidate's Stockham schedule
(LeanFFTW.Gen.stockhamCost with Weights.arith and Weights.mem; LeanFFTW/Proof/Cost.lean).

The model predicts time as a per-schedule linear function of (arith/vl, mem/vl, passes*N,
1), fitted by least squares on relative error. For each size and each K it reports the
regret of measuring only the K candidates the model ranks best: the best measured time
among them over the best time of all candidates (1.00 = the planner loses nothing).
"""
import argparse, collections, math, re, sys

import numpy as np


def load(path):
    rows = []
    for line in open(path):
        m = re.match(r"(\d+) (\d) (\w+) (\d) (\d+) (\d+) ([0-9.e+]+) (\d+) (\d+) (\d+) \[(.*)\]", line)
        if not m or m.group(3) != "all":
            continue
        N, fwd, _, mode, T, Q, t, vl, a, mem, rs = m.groups()
        rs = [int(x) for x in rs.split(",")]
        t = float(t)
        if t >= 1e29:
            continue
        rows.append(dict(N=int(N), mode=int(mode), t=t, vl=max(int(vl), 1), a=int(a), m=int(mem),
                         s=len(rs), rs=rs))
    return rows


def feats(r):
    vl = r["vl"]
    return [r["a"] / vl, r["m"] / vl, r["s"] * r["N"] / 8.0, 1.0]


def regime(r):
    # working set of the transform, in bytes (in + out, interleaved complex)
    b = 32 * r["N"]
    return 0 if b <= 48 * 1024 else 1 if b <= 2 * 1024 * 1024 else 2


def fit(rows):
    coef = {}
    groups = collections.defaultdict(list)
    for r in rows:
        groups[(r["mode"], regime(r))].append(r)
    for key, rs in groups.items():
        X = np.array([feats(r) for r in rs])
        y = np.array([r["t"] for r in rs])
        w = 1.0 / y
        c, *_ = np.linalg.lstsq(X * w[:, None], y * w, rcond=None)
        coef[key] = c
    return coef


def predict(coef, r):
    c = coef.get((r["mode"], regime(r)))
    if c is None:
        return float("inf")
    return float(np.dot(c, feats(r)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--K", type=int, nargs="+", default=[4, 8, 16, 32])
    ap.add_argument("--holdout", action="store_true", help="fit on other sizes only")
    a = ap.parse_args()
    rows = load(a.log)
    byN = collections.defaultdict(list)
    for r in rows:
        byN[r["N"]].append(r)
    coef_all = fit(rows)
    print("size  cands  " + "  ".join(f"K={k:<3}" for k in a.K))
    worst = {k: 1.0 for k in a.K}
    logsum = {k: 0.0 for k in a.K}
    for N in sorted(byN):
        cs = byN[N]
        coef = fit([r for r in rows if r["N"] != N]) if a.holdout else coef_all
        best = min(r["t"] for r in cs)
        ranked = sorted(cs, key=lambda r: predict(coef, r))
        regs = []
        for k in a.K:
            reg = min(r["t"] for r in ranked[:k]) / best
            regs.append(reg)
            worst[k] = max(worst[k], reg)
            logsum[k] += math.log(reg)
        print(f"{N:<7} {len(cs):<5}  " + "  ".join(f"{x:5.3f}" for x in regs))
    n = len(byN)
    print("geomean        " + "  ".join(f"{math.exp(logsum[k] / n):5.3f}" for k in a.K))
    print("worst          " + "  ".join(f"{worst[k]:5.3f}" for k in a.K))


if __name__ == "__main__":
    main()
