#!/usr/bin/env python3
"""Export the exact weight-four triplet q+, q0, q- (P4) for Lean (Benchmark.md section 5, item 3).

Written 4 October 2026 by the S2-replay agent; NOT run by its author (job admission is the root's).

Source: hi_cft_20260923_next_structure_p4_controls.vectors.json.gz (format exact-p4-triplet-v1,
500 KB gzip), written by hi_cft_20260923_next_structure_p4_controls.py; its SHA-256 is checked
against 'vectors_sha256' of hi_cft_20260923_next_structure_p4_controls.json.  The triplet is
    q+ = P4_plus  (weight (0, 2), 2,313 terms),
    q0 = P4_zero  = F_R(0) q+   (2,363 terms),
    q- = P4_minus = F_R(0) q0   (2,313 terms),
a (1, 3) K-type (the 18 current zero-mode controls and 6 positive Virasoro controls of the
record are copied; the Virasoro controls express L(1) q, L(2) q through the checkpoint rows
r2_*, r3_* exported by export_s3.py).

No lattice arithmetic: coefficients are normalized with fractions.Fraction and terms sorted.
Output lean/tools/lattice_export/p4.json (about 1 MB), conventions of s2.json:
* 'fields': [{'id', 'grade', 'weight', 'vector'}] for P4_plus, P4_zero, P4_minus;
* 'current_controls', 'virasoro_controls', 'provenance': copied verbatim;
* 'source_sha256'.

Run from the repository root through the resource guard (estimated peak 0.1 GiB, < 5 s):
    ~/.local/bin/research-safe-run --memory-mib 512 --limit-mib 1024 --threads 1 -- \\
        python3 lean/tools/lattice_export/export_p4.py
"""
import gzip
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RECORD = ROOT / 'hi_cft_20260923_next_structure_p4_controls.json'
VECTORS = ROOT / 'hi_cft_20260923_next_structure_p4_controls.vectors.json.gz'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def normalize(vector):
    terms = {}
    for a, o, c in vector:
        key = (tuple(int(v) for v in a), tuple(int(k) for k in o))
        assert key not in terms, ('repeated state', key)
        cs = [Q(v) for v in c]
        assert len(cs) == 4
        if any(cs):
            terms[key] = cs
    return [[list(a), list(o), [q(v) for v in cs]] for (a, o), cs in sorted(terms.items())]


def main():
    record = json.loads(RECORD.read_text())
    assert record['status'] == 'exact_P4_triplet_and_lower_controls_passed'
    digest = sha(VECTORS)
    assert digest == record['vectors_sha256'], 'vectors file changed since the record'
    with gzip.open(VECTORS, 'rt', encoding='utf-8') as stream:
        payload = json.load(stream)
    assert payload['format'] == 'exact-p4-triplet-v1'
    names = [f['id'] for f in payload['fields']]
    assert names == ['P4_plus', 'P4_zero', 'P4_minus'], names
    fields = [{'id': f['id'], 'grade': f['grade'], 'weight': f['weight'],
               'vector': normalize(f['vector'])} for f in payload['fields']]
    assert [len(f['vector']) for f in fields] == record['field_terms'], record['field_terms']
    out = {
        'format': 'lean-export-p4-v1',
        'triplet_definition': payload['provenance'].get('triplet_definition'),
        'fields': fields,
        'current_controls': payload['current_controls'],
        'virasoro_controls': payload['virasoro_controls'],
        'provenance': payload['provenance'],
        'source_sha256': {str(RECORD.relative_to(ROOT)): sha(RECORD),
                          str(VECTORS.relative_to(ROOT)): digest},
    }
    path = Path(__file__).with_name('p4.json')
    tmp = path.with_suffix('.json.tmp')
    tmp.write_text(json.dumps(out))
    tmp.replace(path)
    print(json.dumps({'output': str(path), 'bytes': path.stat().st_size,
                      'terms': [len(f['vector']) for f in fields]}))


if __name__ == '__main__':
    main()
