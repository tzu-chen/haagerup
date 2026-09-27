"""Spectrum figure for the c=8 Haagerup letter.

Reads the exact exported data in ../c8_physics_20260927/data and writes
figures/spectrum.pdf (PGF backend, pdflatex, grayscale).

(a) Diagonal U theory: all Virasoro primaries with 0 < Delta <= 4.
(b) E8 theory with the first-factor H3 action: Z3-neutral Virasoro
    primaries with Delta <= 4.  Filled markers: M_0 x conj(E8), on which
    rho acts by d=(3+sqrt13)/2.  Hollow markers: M_b x conj(E8), on which
    rho acts by -1/d=(3-sqrt13)/2.  The Z3-charged states 2 M_a x conj(E8)
    are not shown.

Marker area grows with log(multiplicity). Standard library + matplotlib.
"""
import csv
import json
import math
import os
from fractions import Fraction

import matplotlib

matplotlib.use("pgf")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "c8_physics_20260927", "data")
OUT = os.path.join(HERE, "figures")

plt.rcParams.update({
    "pgf.texsystem": "pdflatex",
    "pgf.rcfonts": False,
    "pgf.preamble": r"\usepackage{amsmath}",
    "text.usetex": True,
    "font.family": "serif",
    "font.size": 8,
    "axes.labelsize": 8,
    "xtick.labelsize": 7,
    "ytick.labelsize": 7,
    "legend.fontsize": 7,
    "axes.linewidth": 0.5,
    "xtick.major.width": 0.5,
    "ytick.major.width": 0.5,
})


def diagonal_points(dmax):
    pts = []
    with open(os.path.join(DATA, "diagonal_spectrum.tsv")) as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            D = Fraction(row["Delta"])
            s = Fraction(row["spin"])
            n = int(row["Virasoro_primaries"])
            if 0 < D <= dmax and n > 0:
                pts.append((s, D, n))
    return pts


def e8_neutral_points(dmax):
    with open(os.path.join(DATA, "characters.json")) as fh:
        ch = json.load(fh)
    vir = {m["module"]: m["virasoro_primary_multiplicities_including_identity"]
           for m in ch["modules"]}
    vE = ch["holomorphic_E8"]["virasoro_primary_multiplicities_including_identity"]
    plus, minus = [], []
    for h in range(dmax + 1):
        for hb in range(dmax + 1 - h):
            s, D = h - hb, h + hb
            plus.append((s, D, vir["0"][h] * vE[hb]))       # h_0 = 0
            if h >= 1:
                minus.append((s, D, vir["b"][h - 1] * vE[hb]))  # h_b = 1
    return [p for p in plus if p[2]], [p for p in minus if p[2]]


def area(n):
    return 3.0 + 9.0 * math.log10(n) ** 1.15 if n > 1 else 3.0


def frame(ax, dmax, smax, marginal):
    ax.plot([0, smax], [0, smax], ls=":", lw=0.5, color="0.4")
    ax.plot([0, -smax], [0, smax], ls=":", lw=0.5, color="0.4")
    if marginal:
        ax.axhline(2, ls="--", lw=0.5, color="0.4")
    ax.set_xlim(-smax - 0.4, smax + 0.4)
    ax.set_ylim(-0.12, dmax + 0.15)
    ax.set_xlabel(r"spin $s=h-\bar h$")
    ax.set_ylabel(r"$\Delta=h+\bar h$")
    ax.set_xticks(range(-smax, smax + 1))
    ax.tick_params(direction="in", top=True, right=True)


def main():
    os.makedirs(OUT, exist_ok=True)
    fig, (a, b) = plt.subplots(1, 2, figsize=(7.0, 2.45))

    pa = diagonal_points(4)
    frame(a, 4, 4, marginal=True)
    a.scatter([float(s) for s, _, _ in pa], [float(D) for _, D, _ in pa],
              s=[area(n) for *_, n in pa], c="k", linewidths=0, zorder=3)
    a.set_yticks([0, 2 / 3, 1, 2, 3, 4])
    a.set_yticklabels([r"$0$", r"$\tfrac23$", r"$1$", r"$2$", r"$3$", r"$4$"])

    plus, minus = e8_neutral_points(4)
    frame(b, 4, 4, marginal=True)
    off = 0.16
    b.scatter([s - off for s, _, _ in plus], [D for _, D, _ in plus],
              s=[area(n) for *_, n in plus], c="k", linewidths=0, zorder=3)
    b.scatter([s + off for s, _, _ in minus], [D for _, D, _ in minus],
              s=[area(n) for *_, n in minus], facecolors="white",
              edgecolors="k", linewidths=0.6, zorder=3)
    b.set_yticks(range(5))
    handles = [
        Line2D([], [], ls="", marker="o", ms=4, mfc="k", mec="k",
               label=r"$\widehat\rho=\tfrac{3+\sqrt{13}}2$"),
        Line2D([], [], ls="", marker="o", ms=4, mfc="white", mec="k",
               mew=0.6, label=r"$\widehat\rho=\tfrac{3-\sqrt{13}}2$"),
    ]
    b.legend(handles=handles, loc="lower right", frameon=False,
             handletextpad=0.2, borderaxespad=0.3)

    for ax, lab in ((a, "(a)"), (b, "(b)")):
        ax.text(0.03, 0.04, lab, transform=ax.transAxes, va="bottom", ha="left")
    fig.tight_layout(pad=0.3, w_pad=1.5)
    fig.savefig(os.path.join(OUT, "spectrum.pdf"))

    def key(p):
        return (str(p[1]), str(p[0]), p[2])

    summary = {
        "panel_a_levels": len(pa),
        "panel_a_components": sum(n for *_, n in pa),
        "panel_a_relevant_scalars": sorted(key(p) for p in pa
                                           if p[0] == 0 and p[1] < 2),
        "panel_b_rho_plus": sorted(key(p) for p in plus),
        "panel_b_rho_minus": sorted(key(p) for p in minus),
    }
    with open(os.path.join(OUT, "spectrum_summary.json"), "w") as fh:
        json.dump(summary, fh, indent=1)
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
