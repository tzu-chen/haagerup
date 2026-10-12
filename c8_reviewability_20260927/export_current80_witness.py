"""Export the eighty-current cyclic basis, matrices, metric and recipes.

Root runs serially through hi_cft_safe_run.py --limit-mib 2048, with
timeout 180s. No NumPy/SciPy, ambient higher-grade bases, workers, or
unbounded caches. The original engine is used only in grades 0,1,2.
Finite allocation: 86 ambient states, 80 complement rows, 80 cyclic
rows, at most 30 sparse 86x86 matrices and their metric products.
Caps: 100000 matrix entries, 250000 total saved vector entries,
4096-bit coefficients, 120s internal timeout. Estimate <0.3GiB (the
original untracked producer used 26MiB and <1s); hard guard AS2GiB.

Unlike the old summary, this exports explicit row identities. A
separate stdlib verifier can check metric adjoints, cyclic recipes,
distinct pivots, and membership using the supplied matrices. Matrix
identification with actual lattice zero modes remains the independent
provenance boundary, with all field coordinates and mode indices given.
"""

import argparse
from collections import deque
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
import resource
import signal
import sys
from time import monotonic


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
TORUS = (5, 8, 9, 8, 5, 1, 2, 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2 * 1024**3
    assert not args.output.exists()
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('120s cap')))
    signal.alarm(120)
    started = monotonic()
    import hi_cft_20260923_c8_exact as x

    source = ROOT / 'hi_cft_20260923_c8_exact_fields.json'
    pct_source = ROOT / 'hi_cft_20260923_c8_exact_unitary_certificate.json'
    data = json.loads(source.read_text())
    pct_record = json.loads(pct_source.read_text())
    assert pct_record['exact_PCT_preservation']
    assert pct_record['source_sha256'][source.name] == hashlib.sha256(source.read_bytes()).hexdigest()

    def pack(v):
        return [[i, list(map(str, c))] for i, c in sorted(v.items())]

    def pack_field(v):
        return [{'momentum': list(a), 'oscillators': list(o),
                 'coefficient': list(map(str, c))}
                for (a, o), c in sorted(v.items())]

    def add(v, i, c):
        c = v.get(i, x.ZERO_A) + c
        if c:
            v[i] = c
        else:
            v.pop(i, None)

    def bounded(v, limit=12000):
        assert len(v) <= limit
        assert all(max(max(abs(q.numerator).bit_length(),
                           q.denominator.bit_length()) for q in c) <= 4096
                   for c in v.values())
        return v

    def pct(v):
        out = {}
        for (a, osc), c in v.items():
            factor = Q((-1) ** len(osc))
            for t, n in zip(TORUS, a):
                factor *= Q(t) ** n
            out[tuple(-n for n in a), osc] = c.conj(2) * factor
        return out

    roots, todo = set(x.SIMPLE), list(x.SIMPLE)
    while todo:
        a = todo.pop()
        for i in range(8):
            b = list(a)
            b[i] -= x.dot(a, x.SIMPLE[i])
            b = tuple(b)
            if b not in roots:
                roots.add(b)
                todo.append(b)
                assert len(roots) <= 78
    assert len(roots) == 78
    states = [(x.ZERO, (i,)) for i in range(8)] + [(a, ()) for a in sorted(roots)]
    index = {state: i for i, state in enumerate(states)}
    assert len(index) == 86

    def coordinates(v):
        assert set(v) <= index.keys()
        return bounded({index[state]: c for state, c in v.items()}, 86)

    gram = []
    for j, (a, osc) in enumerate(states):
        if osc:
            gram.append({i: x.A(x.G[i][j]) for i in range(8) if x.G[i][j]})
        else:
            norm = Q(1)
            for t, n in zip(TORUS, a):
                norm *= Q(t) ** n
            assert norm > 0
            gram.append({j: x.A(norm)})

    def apply(matrix, v):
        out = {}
        for j, c in v.items():
            for i, d in matrix[j].items():
                add(out, i, c * d)
        return bounded(out, 86)

    currents = x.LEFT + x.RIGHT
    dual = [(currents[0], Q(1, 2)), (currents[2], Q(1)),
            (currents[1], Q(1)), (currents[3], Q(1, 78)),
            (currents[5], Q(1, 39)), (currents[4], Q(1, 39))]
    bilinear = lambda a, b: x.mode(a, 1, b).get((x.ZERO, ()), x.ZERO_A)

    def complement(v):
        return x.vadd((1, v), *[(-bilinear(v, d) * c, j)
                                for j, (d, c) in zip(currents, dual)])

    space = x.Span()
    for state in states:
        space.reduce(complement({state: x.ONE}), True)
        assert space.dimension <= 80
    assert space.dimension == 80
    complement_fields = [v for block in space.blocks.values() for v in block.values()]
    complement_rows = [coordinates(v) for v in complement_fields]
    omega = x.omega()
    fields = [('K%d' % i, a) for i, a in enumerate(currents)]
    fields += [('field%d' % i, x.read_field(row)) for i, row in enumerate(data['fields'])]
    matrices, operator_records = [], []

    def make_matrix(components):
        columns = []
        for state in states:
            out = {}
            for a, n, coefficient in components:
                out = x.vadd((1, out), (coefficient, x.mode(a, n, {state: x.ONE})))
            columns.append(coordinates(out))
        return columns

    matrix_entries = 0
    for name, a in fields:
        weight = x.grade(next(iter(a)))
        assert weight in (1, 2)
        original = [(a, weight - 1, x.ONE)]
        # Full unitary zero-mode adjoint formula, including possible L(1)
        # corrections. No quasiprimary assumption is silently introduced.
        adjoint, derivative = [], pct(a)
        for j in range(weight + 1):
            if not derivative:
                break
            adjoint.append((derivative, weight - j - 1,
                            x.A(Q((-1) ** weight, factorial(j)))))
            derivative = x.mode(omega, 2, derivative)
        pair = [make_matrix(original), make_matrix(adjoint)]
        h_a = [apply(gram, col) for col in pair[0]]
        h_b = [apply(gram, col) for col in pair[1]]
        for i in range(86):
            for j in range(86):
                assert h_a[i].get(j, x.ZERO_A).conj(2) == h_b[j].get(i, x.ZERO_A)
        for label, components, matrix in ((name, original, pair[0]),
                                           ('adjoint:' + name, adjoint, pair[1])):
            matrix_entries += sum(map(len, matrix))
            assert matrix_entries <= 100000
            for vector in complement_fields:
                image = apply(matrix, coordinates(vector))
                actual = {states[i]: c for i, c in image.items()}
                assert not space.reduce(actual), 'complement invariance'
            matrices.append(matrix)
            operator_records.append({'name': label,
                                     'components': [{'field': pack_field(v), 'mode': n,
                                                     'coefficient': list(map(str, c))}
                                                    for v, n, c in components],
                                     'matrix_columns': [pack(v) for v in matrix]})
    assert len(matrices) == 30
    for vector in complement_fields:
        for current in currents:
            assert not x.mode(current, 1, vector)
        assert not x.mode(x.read_field(data['fields'][-2]), 2, vector)

    unique = [i for i, state in enumerate(states) if x.weight(state) == (0, 10)]
    assert len(unique) == 1
    seed = {unique[0]: x.ONE}
    assert not space.reduce({states[unique[0]]: x.ONE})
    cyclic_rows, recipes, pivots, queue = [], [], {}, deque()

    def insert(vector, recipe):
        out, reductions = vector.copy(), []
        for pivot, row_id in sorted(pivots.items()):
            if pivot in out:
                c = out[pivot]
                reductions.append([row_id, list(map(str, c))])
                for i, d in cyclic_rows[row_id].items():
                    add(out, i, -c * d)
        if not out:
            return
        pivot = min(out)
        scale = out[pivot].inv()
        out = bounded({i: scale * c for i, c in out.items()}, 86)
        row_id = len(cyclic_rows)
        assert row_id < 80
        pivots[pivot] = row_id
        cyclic_rows.append(out)
        recipes.append({'input': recipe, 'reductions': reductions,
                        'scale': list(map(str, scale)), 'pivot': pivot})
        queue.append(row_id)

    insert(seed, {'seed_basis_index': unique[0]})
    while queue and len(cyclic_rows) < 80:
        parent = queue.popleft()
        for op, matrix in enumerate(matrices):
            insert(apply(matrix, cyclic_rows[parent]), {'parent': parent, 'operator': op})
            if len(cyclic_rows) == 80:
                break
    assert len(cyclic_rows) == 80
    saved_terms = matrix_entries + sum(map(len, cyclic_rows)) + sum(map(len, complement_rows))
    assert saved_terms <= 250000
    output = {
        'format': 'explicit-current80-cyclicity-v1',
        'arithmetic': 'Q(s,t), s^2=13, t^2=-3; coefficient order 1,s,t,st',
        'ambient_states': [{'momentum': list(a), 'oscillators': list(o)} for a, o in states],
        'hermitian_gram_columns': [pack(v) for v in gram],
        'current_coordinates': [pack(coordinates(v)) for v in currents],
        'complement_rows': [pack(v) for v in complement_rows],
        'operators': operator_records,
        'unique_seed_basis_index': unique[0], 'seed_weight': [0, 10],
        'seed_eigenspace_dimension': 1,
        'cyclic_rows': [pack(v) for v in cyclic_rows], 'recipes': recipes,
        'cyclic_dimension': 80,
        'exact_adjoint_checks': True,
        'exact_complement_invariance': True,
        'exact_current_plane_annihilation': True,
        'exact_u_lowering_annihilation': True,
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (source, pct_source, ROOT / 'hi_cft_20260923_c8_exact.py')},
        'exporter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'matrix_entries': matrix_entries, 'saved_sparse_entries': saved_terms,
        'seconds': monotonic() - started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': ('Explicit metric, actual zero-mode matrices and cyclic row recipes. '
                  'Independent verification of supplied matrix algebra need not trust '
                  'the mode engine, but identification of those matrices with actual '
                  'lattice operators is a separate provenance check.')}
    with args.output.open('x') as f:
        json.dump(output, f, indent=2)
        f.write('\n')
    print(json.dumps({k: output[k] for k in ('cyclic_dimension', 'unique_seed_basis_index',
                                           'matrix_entries', 'saved_sparse_entries',
                                           'seconds', 'peak_rss_KiB')}), flush=True)


if __name__ == '__main__':
    main()
