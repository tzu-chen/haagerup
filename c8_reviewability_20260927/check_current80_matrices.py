"""Independent exact finite-matrix verification of the current80 witness.

Stdlib only; no exporter or lattice mode engine is imported. Run serially
under hi_cft_safe_run.py --limit-mib 1024 with an outer180s timeout.
At most86 ambient coordinates,30 sparse matrices,80+80rows; input<=30MiB,
totalstoredsparseentries<=250000, 4096-bit inputcoefficients. Estimate
<0.3GiB. Matrix identification with the supplied field-mode recipes is
EXCLUDED: this verifies the finite linear-algebra certificate itself.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import signal


ZERO = (Q(0),) * 4
ONE = (Q(1), Q(0), Q(0), Q(0))
G = [[2 * (i == j) for j in range(8)] for i in range(8)]
for i, j in ((0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (6, 7)):
    G[i][j] = G[j][i] = -1
A0 = (-1, -2, -3, -2, -1, -2, 0, 0)
H = (5, 8, 9, 8, 5, 0, 2, 2)
TORUS = (5, 8, 9, 8, 5, 1, 2, 2)


def k(q):
    return (Q(q), Q(0), Q(0), Q(0))


def plus(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def times(a, b):
    answer = [Q(0)] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            answer[i ^ j] += x * y * (13 if i & j & 1 else 1) * (
                -3 if i & j & 2 else 1)
    return tuple(answer)


def conjugate(a, mask=2):
    return tuple((-q if (i & mask).bit_count() % 2 else q)
                 for i, q in enumerate(a))


def inverse(a):
    assert a != ZERO
    numerator = times(times(conjugate(a, 1), conjugate(a, 2)), conjugate(a, 3))
    denominator = times(a, numerator)
    assert denominator[1:] == (0, 0, 0) and denominator[0] != 0
    return tuple(q / denominator[0] for q in numerator)


def coefficient(row):
    assert len(row) == 4 and all(type(q) is str for q in row)
    answer = tuple(Q(q) for q in row)
    assert max(max(abs(q.numerator).bit_length(), q.denominator.bit_length())
               for q in answer) <= 4096
    return answer


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        assert key not in out, 'duplicate JSON object key'
        out[key] = value
    return out


def vector(rows):
    assert len(rows) <= 86
    out = {}
    for i, row in rows:
        assert type(i) is int and 0 <= i < 86 and i not in out
        c = coefficient(row)
        assert c != ZERO
        out[i] = c
    return out


def add_to(out, i, value):
    value = plus(out.get(i, ZERO), value)
    if value == ZERO:
        out.pop(i, None)
    else:
        out[i] = value


def subtract_scaled(out, scalar, row):
    out = out.copy()
    for i, c in row.items():
        add_to(out, i, neg(times(scalar, c)))
    return out


def apply(matrix, v):
    out = {}
    for j, c in v.items():
        for i, d in matrix[j].items():
            add_to(out, i, times(c, d))
    return out


def inner(v, w, gram):
    image = apply(gram, w)
    answer = ZERO
    for i, c in v.items():
        answer = plus(answer, times(conjugate(c), image.get(i, ZERO)))
    return answer


def pairing(a, b):
    return sum(a[i] * G[i][j] * b[j] for i in range(8) for j in range(8))


def reduce(v, pivots):
    out = v.copy()
    for pivot, row in sorted(pivots.items()):
        if pivot in out:
            out = subtract_scaled(out, out[pivot], row)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    assert args.certificate.stat().st_size <= 30 * 1024**2
    assert not args.output.exists()
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('120s cap')))
    signal.alarm(120)
    doc = json.loads(args.certificate.read_text(), object_pairs_hook=unique_object)
    assert doc['format'] == 'explicit-current80-cyclicity-v1'
    stored_entries = sum(len(row) for key in ('hermitian_gram_columns',
                          'current_coordinates', 'complement_rows', 'cyclic_rows')
                         for row in doc[key])
    for record in doc['operators']:
        stored_entries += sum(map(len, record['matrix_columns']))
        assert len(record['components']) <= 3
        stored_entries += sum(len(component['field']) for component in record['components'])
    assert stored_entries <= 250000
    assert len(doc['ambient_states']) == 86
    states = []
    for row in doc['ambient_states']:
        a, osc = tuple(row['momentum']), tuple(row['oscillators'])
        assert len(a) == 8 and all(type(v) is int for v in a)
        assert all(type(v) is int and v >= 0 for v in osc)
        states.append((a, osc))
    assert len(set(states)) == 86
    assert states[:8] == [((0,) * 8, (i,)) for i in range(8)]
    assert all(not osc and pairing(a, a) == 2 for a, osc in states[8:])
    root_index = {a: i for i, (a, osc) in enumerate(states) if not osc}
    simple = [tuple(int(i == j) for j in range(8)) for i in range(8)]
    assert all(a in root_index for a in simple)
    for a in root_index:
        for j in range(8):
            reflected = list(a)
            reflected[j] -= pairing(a, simple[j])
            assert tuple(reflected) in root_index

    # Exact LDL decomposition proves positivity of the Heisenberg block.
    lower, diagonal = [[Q(i == j) for j in range(8)] for i in range(8)], []
    for j in range(8):
        d = Q(G[j][j]) - sum(lower[j][r] ** 2 * diagonal[r] for r in range(j))
        assert d > 0
        diagonal.append(d)
        for i in range(j + 1, 8):
            lower[i][j] = (Q(G[i][j]) - sum(lower[i][r] * lower[j][r] * diagonal[r]
                                             for r in range(j))) / d
    gram = [vector(row) for row in doc['hermitian_gram_columns']]
    assert len(gram) == 86
    for j, (a, osc) in enumerate(states):
        if j < 8:
            expected = {i: k(G[i][j]) for i in range(8) if G[i][j]}
        else:
            norm = Q(1)
            for t, n in zip(TORUS, a):
                norm *= Q(t) ** n
            assert norm > 0
            expected = {j: k(norm)}
        assert gram[j] == expected

    currents = [vector(row) for row in doc['current_coordinates']]
    expected_currents = [
        {i: k(c) for i, c in enumerate(A0) if c},
        {root_index[A0]: ONE}, {root_index[tuple(-v for v in A0)]: k(-1)},
        {i: k(c) for i, c in enumerate(H) if c},
        {root_index[simple[i]]: ONE for i, c in enumerate(H) if c},
        {root_index[tuple(-v for v in simple[i])]: k(-c) for i, c in enumerate(H) if c}]
    assert currents == expected_currents

    complement = [vector(row) for row in doc['complement_rows']]
    assert len(complement) == 80
    pivots = {}
    for row in complement:
        assert all(inner(current, row, gram) == ZERO for current in currents)
        residual = reduce(row, pivots)
        assert residual, 'dependent complement basis'
        pivot = min(residual)
        scale = inverse(residual[pivot])
        pivots[pivot] = {i: times(scale, c) for i, c in residual.items()}
    assert len(pivots) == 80

    assert len(doc['operators']) == 30
    matrices = []
    for record in doc['operators']:
        matrix = [vector(col) for col in record['matrix_columns']]
        assert len(matrix) == 86
        matrices.append(matrix)
    assert sum(sum(map(len, m)) for m in matrices) <= 100000
    for i in range(0, 30, 2):
        assert doc['operators'][i + 1]['name'] == 'adjoint:' + doc['operators'][i]['name']
        ha = [apply(gram, col) for col in matrices[i]]
        hb = [apply(gram, col) for col in matrices[i + 1]]
        for r in range(86):
            for s in range(86):
                assert conjugate(ha[r].get(s, ZERO)) == hb[s].get(r, ZERO)
    for matrix in matrices:
        for row in complement:
            assert not reduce(apply(matrix, row), pivots), 'noninvariant complement'

    for op, cartan in ((0, A0), (6, H)):
        for j, (a, osc) in enumerate(states):
            charge = pairing(cartan, a)
            expected = {j: k(charge)} if charge else {}
            assert matrices[op][j] == expected
    unique = [i for i, (a, osc) in enumerate(states)
              if (pairing(A0, a), pairing(H, a)) == (0, 10)]
    assert len(unique) == 1 and doc['unique_seed_basis_index'] == unique[0]
    seed = {unique[0]: ONE}
    assert not reduce(seed, pivots)

    rows = [vector(row) for row in doc['cyclic_rows']]
    assert len(rows) == len(doc['recipes']) == 80
    used_pivots = set()
    for i, (row, recipe) in enumerate(zip(rows, doc['recipes'])):
        data = recipe['input']
        if i == 0:
            assert data == {'seed_basis_index': unique[0]}
            out = seed.copy()
        else:
            parent, operator = data['parent'], data['operator']
            assert type(parent) is int and 0 <= parent < i
            assert type(operator) is int and 0 <= operator < 30
            out = apply(matrices[operator], rows[parent])
        reductions = set()
        for earlier, scalar in recipe['reductions']:
            assert type(earlier) is int and 0 <= earlier < i and earlier not in reductions
            reductions.add(earlier)
            c = coefficient(scalar)
            assert c != ZERO
            out = subtract_scaled(out, c, rows[earlier])
        scale = coefficient(recipe['scale'])
        assert scale != ZERO
        out = {j: times(scale, c) for j, c in out.items()}
        assert out == row, 'cyclic row recipe mismatch'
        assert row and min(row) == recipe['pivot']
        pivot = recipe['pivot']
        assert row[pivot] == ONE and pivot not in used_pivots
        assert not used_pivots.intersection(row), 'old cyclic pivot survived elimination'
        used_pivots.add(pivot)
        assert not reduce(row, pivots)
    assert len(used_pivots) == 80
    output = {
        'status': 'pass', 'arithmetic': 'independent stdlib Fraction field and sparse matrix arithmetic',
        'ambient_dimension': 86, 'complement_dimension': 80, 'cyclic_dimension': 80,
        'positive_Heisenberg_LDL_diagonal': list(map(str, diagonal)),
        'Hermitian_Gram_from_lattice_and_positive_gauge': True,
        'six_current_vectors_match_explicit_formulas': True,
        'complement_is_current_orthogonal': True,
        'all_15_adjoint_pairs_verified': True,
        'all_30_operators_preserve_complement': True,
        'Cartan_matrices_match_lattice_weights': True,
        'unique_joint_Cartan_eigenline': [0, 10],
        'all_80_cyclic_recipes_and_independence_verified': True,
        'certificate_sha256': hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': ('Finite linear algebra of supplied exact matrices only. Their identification '
                  'with actual lattice zero modes, generator membership and lowering-mode '
                  'annihilation assertions are not independently verified by this checker.')}
    with args.output.open('x') as f:
        json.dump(output, f, indent=2)
        f.write('\n')
    print(json.dumps(output), flush=True)


if __name__ == '__main__':
    main()
