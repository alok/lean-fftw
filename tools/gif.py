#!/usr/bin/env python3
"""Render the optimization history as an animated GIF from a protocol run.

    python3 tools/gif.py RESULTS_DIR OUT.gif

Each frame shows one Lean FFTW iteration: speed relative to FFTW's best planner mode per
size (FFTW = 1, higher is faster), earlier iterations faded, MKL for reference, and the
iteration's geometric-mean ratio G with its bootstrap 95% CI. Only PIL and numpy are used.
"""
import os
import sys

from PIL import Image, ImageDraw, ImageFont

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench import analyze  # noqa: E402

LABELS = {
    "lean-i0": "i0  baseline: generated kernels, Stockham passes",
    "lean-i1": "i1  fused small transforms, in-place schedule",
    "lean-i2": "i2  FMA contraction",
    "lean-i3": "i3  interleaved-complex kernels for small N",
    "lean-i4": "i4  measuring planner, cache blocking",
    "lean-i5": "i5  two-pass interleaved kernels, better vectorizer",
}
FFTW = ["fftw-measure", "fftw-patient", "fftw-exhaustive"]
W, H = 960, 640
L, R, T, B = 80, 30, 90, 180


def font(size, bold=False):
    name = "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf"
    for d in ("/usr/share/fonts/truetype/dejavu", "/usr/share/fonts/dejavu"):
        p = os.path.join(d, name)
        if os.path.exists(p):
            return ImageFont.truetype(p, size)
    return ImageFont.load_default(size=size)


def main(d, out):
    iters = [i for i in LABELS if os.path.exists(os.path.join(d, "results.json"))]
    base = analyze(d, combine={"fftw": FFTW})
    med, sizes = base["medians"], base["sizes"]
    iters = [i for i in iters if i in med and all(n in med[i] for n in sizes)]
    stats = {}
    for i in iters:
        v = analyze(d, ref=i, comps=["fftw"], combine={"fftw": FFTW})["vs"]["fftw"]
        stats[i] = v
    speed = {i: [med["fftw"][n] / med[i][n] for n in sizes] for i in iters + ["mkl"] if i in med}
    ymax = max(1.6, max(max(s) for s in speed.values()) * 1.08)
    ymin = min(0.0, min(min(s) for s in speed.values()))
    import json
    import re
    lscpu = json.load(open(os.path.join(d, "meta.json")))["environment"].get("lscpu", "")
    m = re.search(r"Model name:\s*(.*)", lscpu)
    cpu = m.group(1).strip() if m else "unknown CPU"
    m = re.search(r"\nModel:\s*(\d+)", lscpu)
    cpu += f" (model {m.group(1)})" if m else ""
    f12, f14, f18, f22 = font(12), font(14), font(18), font(22, True)

    def X(k):
        return L + (W - L - R) * k / (len(sizes) - 1)

    def Y(v):
        return T + (H - T - B) * (ymax - v) / (ymax - ymin)

    def poly(dr, ys, color, width):
        pts = [(X(k), Y(y)) for k, y in enumerate(ys)]
        dr.line(pts, fill=color, width=width, joint="curve")
        for p in pts:
            dr.ellipse([p[0] - width, p[1] - width, p[0] + width, p[1] + width], fill=color)

    frames = []
    for fi, it in enumerate(iters):
        im = Image.new("RGB", (W, H), "white")
        dr = ImageDraw.Draw(im)
        dr.text((L, 18), "Lean FFTW vs FFTW 3.3.10: 1-D complex double, out of place", font=f22,
                fill="black")
        dr.text((L, 50), "speed relative to FFTW's best of measure/patient/exhaustive (higher is "
                "faster); one core of " + cpu, font=f12, fill=(80, 80, 80))
        v = ymin
        while v <= ymax + 1e-9:
            dr.line([(L, Y(v)), (W - R, Y(v))], fill=(225, 225, 225))
            dr.text((L - 40, Y(v) - 8), f"{v:.1f}", font=f12, fill=(90, 90, 90))
            v += 0.2
        for k, n in enumerate(sizes):
            dr.text((X(k) - 8, H - B + 8), f"2^{n.bit_length() - 1}", font=f12, fill=(90, 90, 90))
        dr.text(((W - L - R) // 2 + L - 20, H - B + 26), "size N", font=f12, fill=(90, 90, 90))
        dr.line([(L, Y(1.0)), (W - R, Y(1.0))], fill=(30, 90, 200), width=2)
        dr.text((W - R - 90, Y(1.0) - 20), "FFTW = 1", font=f14, fill=(30, 90, 200))
        if "mkl" in speed:
            poly(dr, speed["mkl"], (150, 150, 150), 1)
            dr.text((W - R - 90, Y(speed["mkl"][-1]) + 4), "MKL", font=f14, fill=(120, 120, 120))
        for prev in iters[:fi]:
            poly(dr, speed[prev], (245, 200, 170), 1)
        poly(dr, speed[it], (220, 80, 20), 3)
        s = stats[it]
        lo, hi = s["ci95"]
        dr.text((L, H - 125), LABELS[it], font=f18, fill="black")
        verdict = "meets the 10% target" if hi <= 0.90 else ("faster than FFTW" if hi < 1 else
                                                              "not yet faster than FFTW")
        dr.text((L, H - 95), f"G = geometric mean of time(Lean) / time(FFTW): {s['G']:.3f}",
                font=f14, fill=(60, 60, 60))
        dr.text((L, H - 75), f"95% CI [{lo:.3f}, {hi:.3f}]: {verdict}", font=f14, fill=(60, 60, 60))
        dr.text((L, H - 45), "faded: earlier iterations; grey: MKL (sequential)", font=f12,
                fill=(120, 120, 120))
        # G history, bottom right
        gx, gy, gw, gh = W - R - 250, H - 118, 250, 100
        g0, g1 = 0.6, max(1.3, max(stats[i]["ci95"][1] for i in iters) + 0.05)

        def GY(g):
            return gy + gh - gh * (g - g0) / (g1 - g0)
        dr.rectangle([gx, gy, gx + gw, gy + gh], outline=(200, 200, 200))
        dr.text((gx, gy - 18), "G by iteration (lower is better)", font=f12, fill=(90, 90, 90))
        for g, col, lab in ((1.0, (30, 90, 200), "1.0 parity"), (0.9, (30, 160, 60), "0.9 target")):
            dr.line([(gx, GY(g)), (gx + gw, GY(g))], fill=col)
            dr.text((gx + gw - 70, GY(g) - 14), lab, font=f12, fill=col)
        for j, i in enumerate(iters[:fi + 1]):
            cx = gx + 20 + j * (gw - 100) / max(1, len(iters) - 1)
            a, b = stats[i]["ci95"]
            dr.line([(cx, GY(a)), (cx, GY(b))], fill=(220, 80, 20), width=2)
            g = GY(stats[i]["G"])
            dr.ellipse([cx - 3, g - 3, cx + 3, g + 3], fill=(220, 80, 20))
        frames.append(im)
    durs = [1400] * (len(frames) - 1) + [4000]
    frames[0].save(out, save_all=True, append_images=frames[1:], duration=durs, loop=0,
                   optimize=True)
    print(f"wrote {out}: {len(frames)} frames")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
