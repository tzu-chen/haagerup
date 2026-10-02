#!/usr/bin/env python3
"""Export the generation certificate of the 120-dimensional weight-two space S2 for Lean (W2).

Replays hi_cft_20260923_c8_minimal_generators.py (record hi_cft_20260923_c8_minimal_generators.json)
with an instrumented echelon span that records every reduction.  Run from the repository root
through the resource guard (the original run took 1.6 s and 34 MB):
    ~/.local/bin/research-safe-run --memory-mib 1024 --limit-mib 2048 --threads 1 -- \
        python3 lean/tools/lattice_export/export_s2.py

Output s2.json:
* 'u': the three-vertex weight-two field u (same vector as the minimal-generators script);
* 'initial': the 24 initial vectors in insertion order: c_(-2)1 for the six currents c, then
  c_(-1)d for all ordered pairs, then omega, then u (in that order, as in the script; vectors
  that reduce to zero against the span are still listed);
* 'ops': operator names; op i acts on a vector v as
  0: eL_(0) v, 1: fL_(0) v, 2: eR_(0) v, 3: fR_(0) v, 4: u_(1) v
  (LEFT = (hL, eL, fL), RIGHT = (hR, eR, fR) as in hi_cft_20260923_c8_exact.py);
* 'basis': the 120 basis vectors r_k (k = 0..119) in insertion order; each is normalized to
  coefficient 1 at its pivot state and has coefficient 0 at the pivots of the earlier basis
  vectors in its weight block (echelon form);
* 'relations': one record per reduction, {'source': ['initial', i] or ['op', op, k],
  'new': k_new or null, 'scale': s, 'coeffs': [[k_i, c_i], ...]} meaning
  source_vector = s * r_{k_new} + sum_i c_i r_{k_i}   (s omitted when 'new' is null);
  the 'op' records cover every basis vector and every operator, so they certify that the span
  of the r_k is closed under the five operators and contains the initial vectors.
States as in export_samples.py; coefficients are 4-tuples "p/q" over the basis 1, s, t, st of
Q(s, t), s^2 = 13, t^2 = -3.
"""
import json
import sys
from collections import deque
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
import hi_cft_20260923_c8_exact as x  # noqa: E402


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def a4(c):
    return [q(v) for v in x.A(c)]


def vec(d):
    return [[list(s[0]), list(s[1]), a4(c)] for s, c in sorted(d.items())]


class InstrumentedSpan:
    def __init__(self):
        self.blocks = {}
        self.basis = []

    def reduce(self, vector):
        """Return (remainder, [(k, c)]) with vector = remainder + sum c * r_k."""
        if not vector:
            return {}, []
        weights = {x.weight(s) for s in vector}
        assert len(weights) == 1, weights
        block = self.blocks.setdefault(next(iter(weights)), {})
        out = vector.copy()
        coeffs = []
        for pivot, (k, v) in sorted(block.items()):
            if pivot in out:
                c = out[pivot]
                coeffs.append((k, c))
                out = x.vadd((1, out), (-c, v))
        return out, coeffs

    def insert(self, vector, source, relations):
        out, coeffs = self.reduce(vector)
        rec = {'source': source, 'coeffs': [[k, a4(c)] for k, c in coeffs]}
        new = None
        if out:
            pivot = min(out)
            scale = out[pivot]
            r = {s: c * scale.inv() for s, c in out.items()}
            new = len(self.basis)
            self.basis.append(r)
            self.blocks[x.weight(next(iter(r)))][pivot] = (new, r)
            rec['scale'] = a4(scale)
        rec['new'] = new
        relations.append(rec)
        return new


def main():
    u = {((0, 0, 0, 0, 0, -1, 1, 1), ()): x.ONE,
         ((0, 0, 0, 1, 1, -1, 0, 0), ()): x.A((0, Q(1, 20), Q(3, 20), 0)),
         ((1, 1, 0, 0, 0, -1, 0, 0), ()): x.A((0, Q(1, 20), Q(-3, 20), 0))}
    currents = x.LEFT + x.RIGHT
    initial = []
    for c in currents:
        initial.append(x.mode(c, -2, x.VAC))
    for c in currents:
        for d in currents:
            initial.append(x.mode(c, -1, d))
    initial.append(x.omega())
    initial.append(u)
    ops = [lambda v: x.mode(x.LEFT[1], 0, v), lambda v: x.mode(x.LEFT[2], 0, v),
           lambda v: x.mode(x.RIGHT[1], 0, v), lambda v: x.mode(x.RIGHT[2], 0, v),
           lambda v: x.mode(u, 1, v)]
    span = InstrumentedSpan()
    relations = []
    queue = deque()
    for i, v in enumerate(initial):
        k = span.insert(v, ['initial', i], relations)
        if k is not None:
            queue.append(k)
    n_initial = len(span.basis)
    while queue:
        k = queue.popleft()
        for o, op in enumerate(ops):
            new = span.insert(op(span.basis[k]), ['op', o, k], relations)
            if new is not None:
                queue.append(new)
    assert n_initial == 24 and len(span.basis) == 120, (n_initial, len(span.basis))
    out = {
        'record': 'hi_cft_20260923_c8_minimal_generators.json',
        'u': vec(u),
        'initial': [vec(v) for v in initial],
        'ops': ['eL_(0)', 'fL_(0)', 'eR_(0)', 'fR_(0)', 'u_(1)'],
        'basis': [vec(r) for r in span.basis],
        'relations': relations,
    }
    path = Path(__file__).with_name('s2.json')
    path.write_text(json.dumps(out))
    sizes = [len(r) for r in span.basis]
    print(len(initial), n_initial, len(span.basis), len(relations), max(sizes), sum(sizes),
          max(len(r['coeffs']) for r in relations), path.stat().st_size)


if __name__ == '__main__':
    main()
