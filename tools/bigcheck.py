#!/usr/bin/env python3
"""Run FFTW's bigcheck problem set (`check.pl -a`) through libbench2 `--verify`.

    python3 tools/bigcheck.py PROBLEMS BENCH OUTDIR --shard K/M [--batch 10]

PROBLEMS holds the problems check.pl asked for, one `verify <p>` or `cando <p>` per line
(recorded once with a stand-in bench program). Problems are deduplicated and put in a
fixed pseudo-random order, so any finished prefix is an unbiased sample. Shard K of M
takes every M-th problem. Results go to OUTDIR/shard-K.jsonl, one line per problem;
a rerun skips problems already recorded.
"""
import argparse
import json
import os
import random
import subprocess


def run(bench, args, timeout):
    try:
        p = subprocess.run([bench] + args, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return -1, "timeout"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("problems")
    ap.add_argument("bench")
    ap.add_argument("out")
    ap.add_argument("--shard", default="0/1")
    ap.add_argument("--batch", type=int, default=10)
    ap.add_argument("--seed", type=int, default=20261017)
    ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    k, m = map(int, a.shard.split("/"))
    seen, items = set(), []
    for line in open(a.problems):
        kind, prob = line.split(None, 1)
        prob = prob.strip()
        if (kind, prob) not in seen:
            seen.add((kind, prob))
            items.append((kind, prob))
    items.sort()
    random.Random(a.seed).shuffle(items)
    mine = items[k::m]
    os.makedirs(a.out, exist_ok=True)
    path = os.path.join(a.out, f"shard-{k}.jsonl")
    done = set()
    if os.path.exists(path):
        for line in open(path):
            r = json.loads(line)
            done.add((r["kind"], r["problem"]))
    todo = [x for x in mine if x not in done]
    with open(path, "a") as f:
        def record(kind, prob, ok, detail):
            f.write(json.dumps({"kind": kind, "problem": prob, "ok": ok, "detail": detail}) + "\n")
            f.flush()

        for kind, prob in [x for x in todo if x[0] == "cando"]:
            rc, out = run(a.bench, ["--can-do", prob], a.timeout)
            record(kind, prob, rc == 0 and out.strip().endswith("#f"), out.strip()[-200:])
        ver = [x for x in todo if x[0] == "verify"]
        for i in range(0, len(ver), a.batch):
            chunk = ver[i:i + a.batch]
            args = ["--verbose=1"]
            for _, prob in chunk:
                args += ["--verify", prob]
            rc, out = run(a.bench, args, a.timeout)
            lines = {ln.split()[0]: ln for ln in out.splitlines() if ln.split()}
            if rc == 0:
                for kind, prob in chunk:
                    record(kind, prob, True, lines.get(prob, ""))
                continue
            for kind, prob in chunk:  # find the failing problem(s)
                rc1, out1 = run(a.bench, ["--verbose=1", "--verify", prob], a.timeout)
                record(kind, prob, rc1 == 0, out1.strip()[-300:])


if __name__ == "__main__":
    main()
