"""Export explicit Potts/PF13 grade-three membership witnesses.

Run only through hi_cft_safe_run.py. Example (root coordinates the job):
  python hi_cft_safe_run.py --limit-mib 2048 -- timeout 600s python \
    c8_reviewability_20260927/export_membership_witnesses.py \
    --output c8_reviewability_20260927/membership_witnesses.json

No original record is overwritten. No NumPy, SciPy, or general ambient
basis is imported. The original exact grade<=4 engine is used only with
target grade<=3; its creation/mode caches are bounded (2048/12000 items).
The S2 span has 120 vectors, the Cartan-zero S3 span at most 58. Tracking
has at most 58 coefficients per row; all spans are capped below 160.
Persistent sparse coefficients are capped at 250000, individual vectors
at 12000 and coefficient numerator/denominator sizes at 4096 bits.

Original membership peak was <0.12 GiB. Raw-source copies, tracking, and
serialization are budgeted below an additional 0.4 GiB; estimate <0.75
GiB overall, with launcher hard AS2GiB and permanent host/RSS limits.
The independent coordinate-sum verifier needs only the exported field
arithmetic and source vectors. It does NOT by itself validate that each
source vector is the mode product named in its provenance recipe.
"""

import argparse
import csv
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
from time import monotonic


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
MAX_VECTOR_TERMS = 12000
MAX_PERSISTENT_TERMS = 250000
MAX_BITS = 4096


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=int, default=560)
    args = parser.parse_args()
    hard_as = resource.getrlimit(resource.RLIMIT_AS)[0]
    assert 0 < hard_as <= 2 * 1024**3, 'Use the guarded 2GiB launcher'
    assert 1 <= args.seconds <= 560
    assert not args.output.exists(), 'Refusing to overwrite an output'
    coefficient_path = args.output.with_suffix('.coefficients.tsv')
    assert not coefficient_path.exists()
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('time cap')))
    signal.alarm(args.seconds)
    started = monotonic()

    import hi_cft_20260923_c8_exact as x
    import hi_cft_20260923_proof_exact4 as ex
    ex.install()

    def bounded(vector):
        assert len(vector) <= MAX_VECTOR_TERMS, 'individual vector support cap'
        for coefficient in vector.values():
            assert max(max(abs(q.numerator).bit_length(),
                           q.denominator.bit_length())
                       for q in coefficient) <= MAX_BITS, 'coefficient cap'
        return vector

    def read(rows):
        return bounded({(tuple(r['momentum']), tuple(r['oscillators'])):
                        x.A(r['coefficient']) for r in rows})

    def pack(vector):
        return [{'momentum': list(a), 'oscillators': list(o),
                 'coefficient': list(map(str, c))}
                for (a, o), c in sorted(vector.items())]

    def mode(a, n, b):
        if not a or not b:
            return {}
        target = x.grade(next(iter(a))) + x.grade(next(iter(b))) - n - 1
        assert 0 <= target <= 3, 'Only grade<=3 products are authorized'
        return bounded(x.mode(a, n, b))

    source_paths = [ROOT / name for name in (
        'hi_cft_20260923_c8_exact_fields.json',
        'hi_cft_20260923_proof_potts_exact.json',
        'hi_cft_20260923_proof_pf13_exact.json')]
    assert all(p.stat().st_size < 8 * 1024**2 for p in source_paths)
    data, potts, pf13 = [json.loads(p.read_text()) for p in source_paths]
    targets = {'Potts_w': read(potts['weight_three_primary']),
               'PF13_w': read(pf13['primary'])}
    currents = x.LEFT + x.RIGHT
    s2 = x.Span()
    s2_vectors, s2_recipes = [], []

    def add2(vector, recipe):
        bounded(vector)
        if s2.reduce(vector, True):
            s2_vectors.append(vector)
            s2_recipes.append(recipe)
            assert s2.dimension <= 120 < 160

    for i, a in enumerate(currents):
        add2(mode(a, -2, x.VAC), {'kind': 'current_mode_vacuum',
                                 'current': i, 'mode': -2})
        for j, b in enumerate(currents):
            add2(mode(a, -1, b), {'kind': 'current_mode_current',
                                  'left_current': i, 'mode': -1,
                                  'right_current': j})
    omega = x.omega()
    add2(omega, {'kind': 'ambient_conformal_vector'})
    add2(x.read_field(data['fields'][-1]),
         {'kind': 'saved_field', 'field_index': len(data['fields']) - 1})
    for field_index, row in enumerate(data['fields'][:-1]):
        left = x.read_field(row)
        n, m = row['dimensions']
        for i in range(n):
            right = left
            for j in range(m):
                add2(right, {'kind': 'current_descendant',
                             'field_index': field_index,
                             'left_lowering_power': i,
                             'right_lowering_power': j})
                right = mode(currents[5], 0, right)
            assert not right
            left = mode(currents[2], 0, left)
        assert not left
    assert s2.dimension == len(s2_vectors) == 120
    # Free normalized S2 elimination copies; the original S2 vectors and
    # recipes are all that subsequent grade-three products need.
    del s2

    # Each row is a normalized lattice vector together with its expansion
    # in the independent, unreduced grade-three source vectors retained here.
    rows = {}
    sources, source_recipes = [], []
    persistent = sum(map(len, s2_vectors)) + sum(map(len, targets.values()))

    def combine_coefficients(left, factor, right):
        out = left.copy()
        for i, c in right.items():
            value = out.get(i, x.ZERO_A) + factor * c
            if value:
                out[i] = value
            else:
                out.pop(i, None)
        assert len(out) <= 58
        return out

    def add3(vector, recipe):
        nonlocal persistent
        bounded(vector)
        if not vector:
            return
        assert {x.weight(s) for s in vector} == {(0, 0)}
        out = vector.copy()
        source_index = len(sources)
        tracking = {source_index: x.ONE}
        for pivot, (row, expansion) in sorted(rows.items()):
            if pivot in out:
                scalar = out[pivot]
                out = bounded(x.vadd((1, out), (-scalar, row)))
                tracking = combine_coefficients(tracking, -scalar, expansion)
        if not out:
            return
        assert len(rows) < 58 < 160
        pivot = min(out)
        scale = out[pivot].inv()
        out = bounded({s: scale * c for s, c in out.items()})
        tracking = {i: scale * c for i, c in tracking.items()}
        rows[pivot] = out, tracking
        sources.append(vector)
        source_recipes.append(recipe)
        persistent += len(vector) + len(out) + len(tracking)
        assert persistent <= MAX_PERSISTENT_TERMS, 'persistent support cap'

    def target_expression(target):
        out, expression = target.copy(), {}
        for pivot, (row, expansion) in sorted(rows.items()):
            if pivot in out:
                scalar = out[pivot]
                out = bounded(x.vadd((1, out), (-scalar, row)))
                expression = combine_coefficients(expression, scalar, expansion)
        return None if out else expression

    weight = lambda v: x.weight(next(iter(v)))
    for i, current in enumerate(currents):
        wanted = tuple(-a for a in weight(current))
        for j, vector in enumerate(s2_vectors):
            if weight(vector) == wanted:
                add3(mode(current, -1, vector),
                     {'kind': 'current_times_S2', 'current': i,
                      'mode': -1, 'S2_index': j})
    for j, vector in enumerate(s2_vectors):
        if weight(vector) == (0, 0):
            add3(mode(omega, 0, vector),
                 {'kind': 'translation_of_S2', 'S2_index': j})
    assert len(rows) == 40
    found = {}

    def record_targets(pair_count):
        for name, target in targets.items():
            if name in found:
                continue
            expression = target_expression(target)
            if expression is not None:
                reconstructed = {}
                for i, coefficient in expression.items():
                    reconstructed = bounded(x.vadd((1, reconstructed),
                                                    (coefficient, sources[i])))
                assert reconstructed == target
                found[name] = {'target': pack(target),
                               'span_rank_at_discovery': len(rows),
                               'zero_weight_pairs_at_discovery': pair_count,
                               'expression': [{'source_index': i,
                                               'coefficient': list(map(str, c))}
                                              for i, c in sorted(expression.items())]}
                print(json.dumps({'target': name, 'rank': len(rows),
                                  'selected_sources': len(expression),
                                  'seconds': monotonic() - started}), flush=True)

    record_targets(0)
    pair_count = 0
    for i in sorted(range(len(s2_vectors)), key=lambda j: len(s2_vectors[j])):
        wanted = tuple(-a for a in weight(s2_vectors[i]))
        for j, vector in enumerate(s2_vectors):
            if weight(vector) != wanted:
                continue
            pair_count += 1
            add3(mode(s2_vectors[i], 0, vector),
                 {'kind': 'S2_zero_product', 'left_S2_index': i,
                  'mode': 0, 'right_S2_index': j})
            record_targets(pair_count)
            if len(found) == len(targets):
                break
        if len(found) == len(targets):
            break
    assert set(found) == set(targets)
    assert found['Potts_w']['span_rank_at_discovery'] == 41
    assert found['PF13_w']['span_rank_at_discovery'] == 58

    out = {
        'format': 'explicit-grade-three-membership-v1',
        'arithmetic': 'Q(s,t); s^2=13, t^2=-3; basis [1,s,t,st]',
        'source_sha256': {str(p.relative_to(ROOT)):
                          hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in source_paths},
        'exporter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'current_order': ['H_left', 'E_left', 'F_left',
                          'H_right', 'E_right', 'F_right'],
        'S2_sources': [{'index': i, 'recipe': s2_recipes[i], 'vector': pack(v)}
                       for i, v in enumerate(s2_vectors)],
        'S3_sources': [{'index': i, 'recipe': source_recipes[i], 'vector': pack(v)}
                       for i, v in enumerate(sources)],
        'targets': found,
        'S3_rank': len(rows),
        'zero_weight_pairs': pair_count,
        'persistent_sparse_terms': persistent,
        'seconds': monotonic() - started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': ('Explicit linear identities for the two saved primaries in '
                  'specified generated grade-three words. Coordinate-sum '
                  'verification alone does not verify the words are the '
                  'stated mode products or authenticate the S2 construction.')}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as f:
        json.dump(out, f, indent=2)
        f.write('\n')
    with coefficient_path.open('x', newline='') as f:
        writer = csv.writer(f, delimiter='\t')
        writer.writerow(['target', 'source_index', 'q0', 'qs', 'qt', 'qst',
                         'source_word_recipe'])
        for name, result in found.items():
            for term in result['expression']:
                i = term['source_index']
                writer.writerow([name, i, *term['coefficient'],
                                 json.dumps(source_recipes[i], sort_keys=True)])
    print(json.dumps({k: out[k] for k in ('S3_rank', 'zero_weight_pairs',
                                        'persistent_sparse_terms', 'seconds',
                                        'peak_rss_KiB')}), flush=True)


if __name__ == '__main__':
    main()
