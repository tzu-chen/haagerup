#!/usr/bin/env python3
"""Export the nine exact fields of hi_cft_20260923_c8_exact_fields.json, the current action on
them and their singular products, for the Lean W1/W2 cross-check (requested by the W1 agent).

Run from the repository root through the resource guard (tiny job, grades <= 3):
    ~/.local/bin/research-safe-run --memory-mib 512 --limit-mib 2048 --threads 1 -- \
        python3 lean/tools/lattice_export/export_fields.py

Conventions as in export_samples.py; coefficients are 4-tuples over the basis 1, s, t, st of
Q(s, t), s^2 = 13, t^2 = -3, written as "p/q" strings.
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
import hi_cft_20260923_c8_exact as x  # noqa: E402
import hi_cft_20260923_proof_general_modes_v2 as g  # noqa: E402

g.install(4)


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def vec(d):
    return [[list(s[0]), list(s[1]), [q(v) for v in x.A(c)]] for s, c in sorted(d.items())]


def main():
    F = [x.read_field(r) for r in
         json.loads((ROOT / 'hi_cft_20260923_c8_exact_fields.json').read_text())['fields']]
    C = list(x.LEFT) + list(x.RIGHT)
    out = {
        'source': 'hi_cft_20260923_c8_exact_fields.json',
        'fields': [vec(f) for f in F],
        'current_on_field': [{'a': a, 'n': n, 'i': i, 'out': vec(x.mode(C[a], n, F[i]))}
                             for a in range(6) for n in (0, 1) for i in range(len(F))],
        'field_products': [{'i': i, 'n': n, 'j': j, 'out': vec(x.mode(F[i], n, F[j]))}
                           for i in range(len(F)) for j in range(len(F)) for n in (0, 1, 2, 3)],
    }
    path = Path(__file__).with_name('fields.json')
    path.write_text(json.dumps(out))
    print(len(F), len(out['current_on_field']), len(out['field_products']),
          sum(len(r['out']) for r in out['field_products']))


if __name__ == '__main__':
    main()
