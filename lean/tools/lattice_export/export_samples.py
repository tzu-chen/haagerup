#!/usr/bin/env python3
"""Export sample lattice-VOA modes from the Python engine for the Lean W1 cross-check.

Run from the repository root through the resource guard (tiny job, grade ceiling 4):
    ~/.local/bin/research-safe-run --memory-mib 512 --limit-mib 2048 --threads 1 -- \
        python3 lean/tools/lattice_export/export_samples.py

Engine: hi_cft_20260923_proof_general_modes_v2 installed into hi_cft_20260923_c8_exact
(the same path as the certificate scripts).  States are (momentum, oscillators):
momentum = 8 integer coordinates in the simple-root basis of E6+A2 (Gram matrix x.G, E6 nodes
0..5 with node 2 joined to 5, A2 nodes 6,7); oscillators = sorted tuple of codes k meaning the
unnormalized Heisenberg creation operator h_{k%8}(-(k//8+1)), h_i = simple coroot i.
`mode(u, n, v)` is u_(n) v (the n-th mode, Borcherds convention Y(u,z) = sum u_(n) z^(-n-1)).
Coefficients are rationals written as "p/q" strings.
"""
import json
import sys
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
import hi_cft_20260923_c8_exact as x  # noqa: E402
import hi_cft_20260923_proof_general_modes_v2 as g  # noqa: E402

g.install(4)
ZERO = x.ZERO


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def a(c):
    return [q(v) for v in x.A(c)]


def lattice_vectors(norm):
    """All lattice vectors of the given norm.  E6 and A2 are orthogonal summands; the
    inverse Cartan diagonals (at most 6 for E6, 2/3 for A2) bound the coordinates by
    sqrt(norm * 6) and sqrt(norm * 2/3)."""
    e6 = {}
    for v in product(range(-4, 5), repeat=6):
        w = v + (0, 0)
        nn = x.norm(w)
        if nn <= norm:
            e6.setdefault(nn, []).append(v)
    a2 = {}
    for v in product(range(-2, 3), repeat=2):
        w = (0,) * 6 + v
        nn = x.norm(w)
        if nn <= norm:
            a2.setdefault(nn, []).append(v)
    out = []
    for n1, vs in e6.items():
        for v in vs:
            for w in a2.get(norm - n1, []):
                out.append(v + w)
    return sorted(out)


def main():
    roots = lattice_vectors(2)
    norm4 = lattice_vectors(4)
    cartan = [(ZERO, (i,)) for i in range(8)]
    rootstates = [(r, ()) for r in roots]
    weight1 = cartan + rootstates
    # weight-two basis: h_i(-2), h_i(-1)h_j(-1), h_i(-1)e^r, e^b (norm 4)
    weight2 = ([(ZERO, (i + 8,)) for i in range(8)]
               + [(ZERO, (i, j)) for i in range(8) for j in range(i, 8)]
               + [(r, (i,)) for r in roots for i in range(8)]
               + [(b, ()) for b in norm4])
    vac = (ZERO, ())
    sel_roots = [r for r in roots if r in (
        (1, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 1, 1), (-1, -2, -3, -2, -1, -2, 0, 0),
        (1, 2, 3, 2, 1, 2, 0, 0), (0, 0, -1, 0, 0, -1, 0, 0), (0, 0, 0, 0, 0, 0, -1, 0))]
    us = ([vac] + cartan[:3] + [(r, ()) for r in sel_roots]
          + [(ZERO, (8,)), (ZERO, (0, 1)), (sel_roots[0], (2,)), (ZERO, (6, 6))])
    vs = ([vac] + cartan[::3] + [(r, ()) for r in sel_roots[:4]]
          + [(ZERO, (9,)), (ZERO, (0, 2)), (sel_roots[1], (0,)), (ZERO, (16,))])
    samples = []
    for u in us:
        for v in vs:
            for n in range(-3, 5):
                target = x.grade(u) + x.grade(v) - n - 1
                if target < 0 or target > 4:
                    continue
                out = g.basis_mode(u, n, v)
                samples.append({
                    'u': [list(u[0]), list(u[1])], 'n': n, 'v': [list(v[0]), list(v[1])],
                    'out': [[list(s[0]), list(s[1]), q(c)] for s, c in out]})

    def vec(d):
        return [[list(s[0]), list(s[1]), a(c)] for s, c in sorted(d.items())]

    data = {
        'conventions': __doc__,
        'gram': x.G,
        'roots': [list(r) for r in roots],
        'n_roots': len(roots),
        'n_norm4': len(norm4),
        'dim_B1': len(weight1),
        'dim_B2': len(weight2),
        'currents_left': [vec(d) for d in x.LEFT],
        'currents_right': [vec(d) for d in x.RIGHT],
        'omega': vec(x.omega()),
        'A0': list(x.A0),
        'COEFF': list(x.COEFF),
        'samples': samples,
    }
    out = Path(__file__).with_name('samples.json')
    out.write_text(json.dumps(data, indent=0))
    print(len(roots), len(norm4), len(weight1), len(weight2), len(samples),
          sum(len(s['out']) for s in samples))


if __name__ == '__main__':
    main()
