#!/usr/bin/env python3
"""Export the exact 956-dimensional weight-three space S3 for Lean (Benchmark.md section 5, item 3).

Written 4 October 2026 by the S2-replay agent; NOT run by its author (job admission is the root's).

Source: the frozen exact Cartan-span checkpoint
    hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024   (format exact-cartan-span-v1),
the same input as hi_cft_20260923_c8two_structure_saturation.py,
hi_cft_20260923_c8two_structure_charged_span.py and hi_cft_20260923_next_structure_lower_closure.py:
* manifest.json: 'order'['3'] lists the 956 row ids (the first 634 span N3), 'files_sha256';
* grade3_weight_*.json.gz (77 block files, 9.4 MB gzip, 33.7 MB JSON, about 220,000 terms):
  {"grade": 3, "weight": [...], "rows": [{id, grade, weight, recipe, elimination, scale, vector}]};
* grade2_weight_*.json.gz (the checkpoint's own echelon basis of S2, 120 rows) and fields.json.gz
  (the named inputs 'vacuum', 'current<i>', 'source<i>', 'f<nnnnn>' referenced by the recipes).

The script does no lattice arithmetic: it parses the JSON, normalizes every coefficient with
fractions.Fraction, sorts the terms, checks the echelon invariants that the certificates assert
(coefficient 1 at the least state, pivots distinct within each (grade, weight) block; grades and
weights of the individual states are left to the Lean checks) and the file hashes, and writes

    lean/tools/lattice_export/s3.json   (about 40 MB)

with the conventions of s2.json: a state is [momentum (8 integers), codes]; a coefficient is a
4-tuple of "p/q" strings over the basis 1, s, t, st of Q(s, t), s^2 = 13, t^2 = -3.
* 'order3': the 956 ids in basis order; 'normal_dimension': 634;
* 'rows3': one record per id in order3: {'id', 'weight', 'pivot', 'recipe', 'elimination',
  'scale', 'vector'} ('recipe', 'elimination', 'scale' copied verbatim: how the row was produced
  from earlier rows and the named inputs, for a later replay of S3 <= U);
* 'order2', 'rows2': the same for the checkpoint's 120 grade-two rows;
* 'inputs': the records of fields.json.gz with normalized vectors;
* 'source_sha256': manifest, block files and fields file (block hashes checked against the
  manifest).

Run from the repository root through the resource guard.  Estimated peak 0.5-0.7 GiB (the parsed
rows as Python lists of strings, about 220,000 terms, plus the output string); well under a
minute:
    ~/.local/bin/research-safe-run --memory-mib 1024 --limit-mib 2048 --threads 1 -- \\
        python3 lean/tools/lattice_export/export_s3.py
"""
import gzip
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CHECKPOINT = ROOT / 'hi_cft_20260923_next_grade4_checkpoint' / 'checkpoint_000024'
MAX_TERMS = 400000
MIB = 1024 ** 2


def sha(path):
    out = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(MIB), b''):
            out.update(chunk)
    return out.hexdigest()


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def normalize(vector):
    """Sorted terms (momentum, codes, [4 Fractions]) without zero coefficients."""
    terms = {}
    for a, o, c in vector:
        key = (tuple(int(v) for v in a), tuple(int(k) for k in o))
        assert key not in terms, ('repeated state', key)
        cs = [Q(v) for v in c]
        assert len(cs) == 4
        if any(cs):
            terms[key] = cs
    return sorted((a, o, cs) for (a, o), cs in terms.items())


def packed(terms):
    return [[list(a), list(o), [q(v) for v in cs]] for a, o, cs in terms]


def read_rows(grade, meta, hashes):
    rows, blocks, total = {}, {}, 0
    for filename in meta['block_files']:
        if not filename.startswith(f'grade{grade}_'):
            continue
        path = CHECKPOINT / filename
        digest = sha(path)
        assert digest == meta['files_sha256'][filename], ('block hash mismatch', filename)
        hashes[str(path.relative_to(ROOT))] = digest
        with gzip.open(path, 'rt', encoding='utf-8') as stream:
            block = json.load(stream)
        assert block['grade'] == grade
        for rec in block['rows']:
            name = rec['id']
            assert rec['grade'] == grade and name not in rows, name
            weight = tuple(rec['weight'])
            assert weight == tuple(block['weight'])
            terms = normalize(rec['vector'])
            assert terms, ('empty row', name)
            pivot = (terms[0][0], terms[0][1])
            assert terms[0][2] == [1, 0, 0, 0], ('row not normalized at its least state', name)
            seen = blocks.setdefault(weight, {})
            assert pivot not in seen, ('repeated pivot', name, seen.get(pivot))
            seen[pivot] = name
            rows[name] = {'id': name, 'weight': list(weight),
                          'pivot': [list(pivot[0]), list(pivot[1])],
                          'recipe': rec.get('recipe'), 'elimination': rec.get('elimination'),
                          'scale': rec.get('scale'), 'vector': packed(terms)}
            total += len(terms)
            assert total <= MAX_TERMS, 'term budget'
    return rows, total


def main():
    manifest = CHECKPOINT / 'manifest.json'
    meta = json.loads(manifest.read_text())
    assert meta['format'] == 'exact-cartan-span-v1' and meta['completed_grade3']
    assert meta['dimensions']['2'] == 120 and meta['dimensions']['3'] == 956
    order2, order3 = meta['order']['2'], meta['order']['3']
    assert len(order2) == len(set(order2)) == 120
    assert len(order3) == len(set(order3)) == 956
    assert any(h['stage'] == 'grade3 translation descendants' and h['dimensions']['3'] == 634
               for h in meta['history'])
    hashes = {str(manifest.relative_to(ROOT)): sha(manifest)}
    rows2, terms2 = read_rows(2, meta, hashes)
    rows3, terms3 = read_rows(3, meta, hashes)
    assert set(rows2) == set(order2) and set(rows3) == set(order3)
    fields_path = CHECKPOINT / 'fields.json.gz'
    hashes[str(fields_path.relative_to(ROOT))] = sha(fields_path)
    with gzip.open(fields_path, 'rt', encoding='utf-8') as stream:
        inputs = json.load(stream)
    names = set()
    for rec in inputs:
        assert rec['id'] not in names
        names.add(rec['id'])
        if 'vector' in rec:
            rec['vector'] = packed(normalize(rec['vector']))
    out = {
        'format': 'lean-export-s3-v1',
        'checkpoint': str(CHECKPOINT.relative_to(ROOT)),
        'normal_dimension': 634,
        'order2': order2, 'rows2': [rows2[n] for n in order2],
        'order3': order3, 'rows3': [rows3[n] for n in order3],
        'inputs': inputs,
        'terms': {'2': terms2, '3': terms3},
        'source_sha256': hashes,
    }
    path = Path(__file__).with_name('s3.json')
    tmp = path.with_suffix('.json.tmp')
    tmp.write_text(json.dumps(out))
    tmp.replace(path)
    print(json.dumps({'output': str(path), 'bytes': path.stat().st_size, 'rows2': len(order2),
                      'rows3': len(order3), 'terms2': terms2, 'terms3': terms3,
                      'max_row_terms': max(len(r['vector']) for r in out['rows3']),
                      'inputs': len(inputs)}))


if __name__ == '__main__':
    main()
