#!/usr/bin/env python3
"""Compile Lean modules of this repository without Lake (development helper).

  devbuild.py OUT ROOT [ROOT ...] [--exe NAME=ROOT] [--lib NAME=ROOT] [--link ARG ...]

Compiles the modules reachable from the ROOT modules (files under the repository root or
scripts/) in dependency order with `lean`, writing .olean/.ilean/.c under OUT, recompiling
only what changed. `--exe NAME=ROOT` links the C of ROOT's closure into OUT/NAME with leanc;
`--lib NAME=ROOT` archives its objects into OUT/NAME.a.
Modules that import Mathlib are not supported here (use `lake build`).
"""
import os, re, subprocess, sys, hashlib

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC_DIRS = [REPO, os.path.join(REPO, "scripts")]


def src_of(mod):
    rel = mod.replace(".", "/") + ".lean"
    for d in SRC_DIRS:
        p = os.path.join(d, rel)
        if os.path.exists(p):
            return p
    return None


def imports(path):
    out = []
    for line in open(path):
        m = re.match(r"^(?:public\s+)?import\s+(\S+)", line)
        if m:
            out.append(m.group(1))
        elif line.strip() and not line.startswith(("/-", "-/", "--", " ", "module")) and out:
            break
    return out


def closure(roots):
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        p = src_of(m)
        if p is None:
            return
        for i in imports(p):
            visit(i)
        order.append(m)
    for r in roots:
        visit(r)
    return order


def main():
    args = sys.argv[1:]
    out = os.path.abspath(args[0])
    roots, exes, libs, link, copts = [], [], [], [], []
    i = 1
    while i < len(args):
        if args[i] == "--exe":
            name, root = args[i + 1].split("=")
            exes.append((name, root))
            roots.append(root)
            i += 2
        elif args[i] == "--lib":
            name, root = args[i + 1].split("=")
            libs.append((name, root))
            roots.append(root)
            i += 2
        elif args[i] == "--link":
            link = args[i + 1:]
            break
        elif args[i] == "--copt":
            copts.append(args[i + 1])
            i += 2
        else:
            roots.append(args[i])
            i += 1
    os.makedirs(out, exist_ok=True)
    env = dict(os.environ)
    env["LEAN_PATH"] = out
    order = closure(roots)
    stamps = {}
    for m in order:
        p = src_of(m)
        base = os.path.join(out, m.replace(".", "/"))
        os.makedirs(os.path.dirname(base), exist_ok=True)
        h = hashlib.sha256(open(p, "rb").read())
        for d in imports(p):
            if d in stamps:
                h.update(stamps[d].encode())
        stamp = h.hexdigest()
        stamps[m] = stamp
        sf = base + ".stamp"
        if os.path.exists(sf) and open(sf).read() == stamp and os.path.exists(base + ".olean"):
            continue
        print(f"lean {m}", flush=True)
        r = subprocess.run(["lean", "-o", base + ".olean", "-i", base + ".ilean", "-c", base + ".c",
                            "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", p], env=env)
        if r.returncode != 0:
            sys.exit(1)
        open(sf, "w").write(stamp)
    def objects(root):
        objs = []
        for m in closure([root]):
            base = os.path.join(out, m.replace(".", "/"))
            o = base + ".o"
            if not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(base + ".c"):
                subprocess.check_call(["leanc", "-c", "-O3", "-DNDEBUG"] + copts + ["-o", o, base + ".c"])
            objs.append(o)
        return objs

    for name, root in exes:
        subprocess.check_call(["leanc", "-o", os.path.join(out, name)] + objects(root) + link)
        print(f"linked {os.path.join(out, name)}")
    for name, root in libs:
        a = os.path.join(out, name + ".a")
        if os.path.exists(a):
            os.remove(a)
        subprocess.check_call(["ar", "rcs", a] + objects(root))
        print(f"archived {a}")


if __name__ == "__main__":
    main()
