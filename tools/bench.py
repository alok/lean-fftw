#!/usr/bin/env python3
"""Benchmark runner for the predeclared protocol (docs/BENCHMARK_PROTOCOL.md).

  bench.py verify  --impl NAME=CMD ...            libbench2 --verify on all primary sizes
  bench.py run     --out DIR --runs R --impl ...   interleaved speed runs, raw output kept
  bench.py analyze DIR [--ref NAME]               medians, geomean ratios, bootstrap CI

An implementation is NAME=CMD where CMD is a libbench2 binary plus options, optionally
prefixed by `cd=DIR:` (run in DIR, e.g. for FFTW wisdom files) and `env=K=V,K=V:`.
"""
import argparse, json, os, platform, random, re, shlex, subprocess, sys, time

SIZES = [2 ** k for k in range(1, 19)]
UNITS = {"ns": 1e-9, "us": 1e-6, "ms": 1e-3, "s": 1.0}


def parse_impl(spec):
    name, rest = spec.split("=", 1)
    cwd, env = None, {}
    while True:
        if rest.startswith("cd="):
            d, rest = rest[3:].split(":", 1)
            cwd = d
        elif rest.startswith("env="):
            e, rest = rest[4:].split(":", 1)
            for kv in e.split(","):
                k, v = kv.split("=", 1)
                env[k] = v
        else:
            break
    return name, {"cmd": shlex.split(rest), "cwd": cwd, "env": env}


def run1(impl, args, timeout=3600):
    env = dict(os.environ)
    env.update(impl["env"])
    if impl["cwd"]:
        os.makedirs(impl["cwd"], exist_ok=True)
    p = subprocess.run(impl["cmd"] + args, cwd=impl["cwd"], env=env, capture_output=True,
                       text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr


def parse_speed(out):
    m = re.search(r"setup:\s*([0-9.e+-]+)\s*(ns|us|ms|s),\s*time:\s*([0-9.e+-]+)\s*(ns|us|ms|s)", out)
    if not m:
        return None
    return float(m.group(1)) * UNITS[m.group(2)], float(m.group(3)) * UNITS[m.group(4)]


def environment():
    def sh(c):
        try:
            return subprocess.run(c, shell=True, capture_output=True, text=True).stdout.strip()
        except Exception as e:  # noqa
            return str(e)
    return {
        "date": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "lscpu": sh("lscpu"),
        "kernel": platform.release(),
        "gcc": sh("gcc --version | head -1"),
        "lean": sh("cat /home/claude/lean-fftw/lean-toolchain"),
        "lean_fftw_commit": sh("git -C /home/claude/lean-fftw rev-parse HEAD"),
        "lean_fftw_dirty": sh("git -C /home/claude/lean-fftw status --porcelain | wc -l"),
        "env": {k: os.environ.get(k) for k in ["MKL_THREADING_LAYER", "OMP_NUM_THREADS"]},
        "loadavg": os.getloadavg(),
    }


def cmd_verify(a):
    impls = dict(parse_impl(s) for s in a.impl)
    ok = True
    for name, impl in impls.items():
        for prob in a.problems or [f"ocf{n}" for n in SIZES]:
            rc, out = run1(impl, ["-v1", "--verify", prob])
            vals = re.findall(r"^\S+\s+([0-9.e+-]+)\s+([0-9.e+-]+)\s+([0-9.e+-]+)\s*$", out, re.M)
            good = rc == 0 and len(vals) == 1
            ok &= good
            print(f"{name} {prob} {'ok' if good else 'FAIL'} {' '.join(vals[0]) if vals else out.strip()[-200:]}")
            sys.stdout.flush()
    sys.exit(0 if ok else 1)


def cmd_run(a):
    impls = dict(parse_impl(s) for s in a.impl)
    os.makedirs(os.path.join(a.out, "raw"), exist_ok=True)
    meta = {"environment": environment(), "impls": impls, "sizes": a.sizes or SIZES,
            "runs": a.runs, "problem": a.problem, "seed": a.seed}
    with open(os.path.join(a.out, "meta.json"), "w") as f:
        json.dump(meta, f, indent=1)
    rng = random.Random(a.seed)
    rows = []
    sizes = a.sizes or SIZES
    for r in range(a.runs):
        order = [(n, name) for n in sizes for name in impls]
        rng.shuffle(order)
        for n, name in order:
            prob = a.problem.replace("N", str(n))
            rc, out = run1(impls[name], ["-s", prob])
            with open(os.path.join(a.out, "raw", f"{name}_{prob}_r{r}.txt"), "w") as f:
                f.write(out)
            sp = parse_speed(out)
            row = {"impl": name, "n": n, "run": r, "rc": rc,
                   "setup": sp[0] if sp else None, "time": sp[1] if sp else None}
            rows.append(row)
            print(json.dumps(row))
            sys.stdout.flush()
        with open(os.path.join(a.out, "results.json"), "w") as f:
            json.dump(rows, f)


def analyze(d, ref=None, comps=None, B=10000, seed=1, combine=None):
    """`combine` maps a new name to member implementations; its per-size statistic is the
    minimum of the members' medians (e.g. FFTW's best planner effort per size)."""
    import numpy as np
    rows = json.load(open(os.path.join(d, "results.json")))
    data = {}
    for r in rows:
        if r["time"] is None:
            continue
        data.setdefault(r["impl"], {}).setdefault(r["n"], []).append(r["time"])
    sizes = sorted({n for i in data for n in data[i]})
    med = {i: {n: float(np.median(data[i][n])) for n in data[i]} for i in data}
    combine = combine or {}
    for c, members in combine.items():
        members = [m for m in members if m in data]
        if members:
            med[c] = {n: min(med[m][n] for m in members if n in med[m]) for n in sizes}
            data[c] = {n: [] for n in sizes}
    impls = sorted(med)
    rng = np.random.default_rng(seed)

    def boot_meds(i, n):
        if i in combine:
            return np.min([boot_meds(m, n) for m in combine[i] if m in data and n in data[m]], axis=0)
        x = np.array(data[i][n])
        idx = rng.integers(0, len(x), size=(B, len(x)))
        return np.median(x[idx], axis=1)

    out = {"medians": med, "sizes": sizes}
    if ref:
        res = {}
        bl = {n: boot_meds(ref, n) for n in sizes}
        for c in (comps or [i for i in impls if i != ref]):
            if not all(n in data.get(c, {}) for n in sizes):
                continue
            ratios = {n: med[ref][n] / med[c][n] for n in sizes}
            g = float(np.exp(np.mean(np.log(list(ratios.values())))))
            lg = np.zeros(B)
            for n in sizes:
                lg += np.log(bl[n] / boot_meds(c, n))
            gs = np.exp(lg / len(sizes))
            res[c] = {"G": g, "ci95": [float(np.percentile(gs, 2.5)), float(np.percentile(gs, 97.5))],
                      "ratios": ratios}
        out["vs"] = res
    return out


def cmd_analyze(a):
    comb = {}
    for c in a.combine or []:
        k, v = c.split("=", 1)
        comb[k] = v.split(",")
    out = analyze(a.dir, a.ref, combine=comb)
    gm = {}
    import numpy as np
    for i, m in out["medians"].items():
        if all(n in m for n in out["sizes"]):
            gm[i] = float(np.exp(np.mean(np.log([m[n] for n in out["sizes"]]))))
    out["geomean_time"] = gm
    with open(os.path.join(a.dir, "analysis.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("geomean time (s):", json.dumps(gm, indent=1))
    hdr = "N".rjust(8) + "".join(i[:14].rjust(15) for i in out["medians"])
    print(hdr)
    for n in out["sizes"]:
        print(str(n).rjust(8) + "".join((f"{out['medians'][i].get(n, float('nan')):.4g}").rjust(15)
                                      for i in out["medians"]))
    for c, v in out.get("vs", {}).items():
        print(f"{a.ref} / {c}: G = {v['G']:.4f}  95% CI [{v['ci95'][0]:.4f}, {v['ci95'][1]:.4f}]")


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    v = sp.add_parser("verify")
    v.add_argument("--impl", action="append", required=True)
    v.add_argument("--problems", nargs="*")
    r = sp.add_parser("run")
    r.add_argument("--impl", action="append", required=True)
    r.add_argument("--out", required=True)
    r.add_argument("--runs", type=int, default=10)
    r.add_argument("--problem", default="ocfN")
    r.add_argument("--sizes", type=int, nargs="*")
    r.add_argument("--seed", type=int, default=20261016)
    z = sp.add_parser("analyze")
    z.add_argument("dir")
    z.add_argument("--ref")
    z.add_argument("--combine", action="append", help="NAME=impl1,impl2 (per-size min of medians)")
    a = ap.parse_args()
    {"verify": cmd_verify, "run": cmd_run, "analyze": cmd_analyze}[a.cmd](a)


if __name__ == "__main__":
    main()
