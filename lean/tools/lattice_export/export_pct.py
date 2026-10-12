#!/usr/bin/env python3
"""Export the PCT data of the weight-two space S2 for Lean (Benchmark.md section 5, item 3).

Written 4 October 2026 by the S2-replay agent; NOT run by its author (job admission is the root's).

The map.  The gauge-conjugated PCT of hi_cft_20260923_c8_exact_check.py (record
hi_cft_20260923_c8_exact_unitary_certificate.json, 'exact_PCT_preservation'), an antilinear
involution of V_L:
    theta( z * prod_k h_{k%8}(-(k/8+1)) e^alpha )
        = conj(z) * (-1)^(number of oscillators) * prod_i c_i^(alpha_i) * prod_k h(...) e^(-alpha),
    c = (5, 8, 9, 8, 5, 1, 2, 2),  conj: t -> -t on Q(s, t) (A.conj(2): (a, b, c, d) -> (a, b, -c, -d)).

The data.  For the 120 echelon basis vectors r_k of S2 in s2.json (export_s2.py, already made)
and for the field u, the script computes theta(v) and its coordinates in the basis r_j by the
same echelon reduction as export_s2.py (subtract at the pivots in increasing order); it asserts
that every remainder is zero, i.e. theta(S2) <= S2 (hence = S2, theta being an involution).
Self-contained: exact arithmetic in Q(s, t) with fractions.Fraction (the multiplication table of
LatticeVOA.QA.mul); it does not import the lattice engine.

Output lean/tools/lattice_export/pct.json (about 0.5 MB):
* 'map': the constants above;
* 'images': [{'k': k, 'coeffs': [[j, c_j], ...]}] meaning theta(r_k) = sum_j c_j r_j;
* 'u_image': the same for theta(u);
* 'source_sha256': s2.json, this script, hi_cft_20260923_c8_exact_check.py.

Run from the repository root through the resource guard (estimated peak 0.1 GiB, a few seconds):
    ~/.local/bin/research-safe-run --memory-mib 512 --limit-mib 1024 --threads 1 -- \\
        python3 lean/tools/lattice_export/export_pct.py
"""
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
COEFF = (5, 8, 9, 8, 5, 1, 2, 2)
ZERO = (Q(0), Q(0), Q(0), Q(0))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def mul(x, y):
    """Product in Q(s, t), s^2 = 13, t^2 = -3, basis 1, s, t, st (LatticeVOA.QA.mul)."""
    return (x[0] * y[0] + 13 * x[1] * y[1] - 3 * x[2] * y[2] - 39 * x[3] * y[3],
            x[0] * y[1] + x[1] * y[0] - 3 * (x[2] * y[3] + x[3] * y[2]),
            x[0] * y[2] + x[2] * y[0] + 13 * (x[1] * y[3] + x[3] * y[1]),
            x[0] * y[3] + x[3] * y[0] + x[1] * y[2] + x[2] * y[1])


def read(v):
    out = {}
    for a, o, c in v:
        key = (tuple(a), tuple(o))
        assert key not in out
        val = tuple(Q(x) for x in c)
        if val != ZERO:
            out[key] = val
    return out


def theta(v):
    out = {}
    for (alpha, osc), z in v.items():
        factor = Q((-1) ** len(osc))
        for c, power in zip(COEFF, alpha):
            factor *= Q(c) ** power
        key = (tuple(-a for a in alpha), osc)
        assert key not in out
        out[key] = (z[0] * factor, z[1] * factor, -z[2] * factor, -z[3] * factor)
    return out


def reduce(vector, basis, order):
    """Coordinates of vector in the echelon basis (pivots in increasing order); remainder 0."""
    out = dict(vector)
    coeffs = []
    for pivot, k in order:
        c = out.get(pivot)
        if c is None:
            continue
        coeffs.append([k, [q(x) for x in c]])
        for state, value in basis[k].items():
            new = tuple(a - b for a, b in zip(out.get(state, ZERO), mul(c, value)))
            if new == ZERO:
                out.pop(state, None)
            else:
                out[state] = new
        assert pivot not in out
    assert not out, 'theta(v) is not in the span of the basis'
    return coeffs


def main():
    s2_path = HERE / 's2.json'
    data = json.loads(s2_path.read_text())
    basis = [read(r) for r in data['basis']]
    assert len(basis) == 120
    order = []
    for k, r in enumerate(basis):
        pivot = min(r)
        assert r[pivot] == (1, 0, 0, 0), ('basis vector not normalized at its least state', k)
        order.append((pivot, k))
    order.sort()
    assert len({p for p, _ in order}) == 120, 'pivots not distinct'
    images = [{'k': k, 'coeffs': reduce(theta(r), basis, order)} for k, r in enumerate(basis)]
    u_image = reduce(theta(read(data['u'])), basis, order)
    out = {
        'format': 'lean-export-pct-v1',
        'map': {'momentum': 'alpha -> -alpha', 'sign': '(-1)^(number of oscillators)',
                'cocycle_gauge': list(COEFF), 'galois': 't -> -t (a, b, c, d) -> (a, b, -c, -d)',
                'source': 'hi_cft_20260923_c8_exact_check.py, pct()'},
        'images': images,
        'u_image': u_image,
        'source_sha256': {'lean/tools/lattice_export/s2.json': sha(s2_path),
                          'lean/tools/lattice_export/export_pct.py': sha(__file__),
                          'hi_cft_20260923_c8_exact_check.py':
                              sha(ROOT / 'hi_cft_20260923_c8_exact_check.py')},
    }
    path = HERE / 'pct.json'
    tmp = path.with_suffix('.json.tmp')
    tmp.write_text(json.dumps(out))
    tmp.replace(path)
    print(json.dumps({'output': str(path), 'bytes': path.stat().st_size,
                      'max_coeffs': max(len(i['coeffs']) for i in images),
                      'u_coeffs': len(u_image)}))


if __name__ == '__main__':
    main()
