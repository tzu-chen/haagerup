"""Independent, non-mode finite-field rank/provenance audit of the X2 file.

Root-only numerical job: <=2 GiB AS, 60s alarm, expected <0.1 GiB RSS.
Uses only the Python standard library, not the producer's VOA mode engine.
Recomputes exact X1 Gram/orthogonality and all1250 saved-vector pivots.
Checks mode-word grading, weights and references, but deliberately does
not re-evaluate mode coefficients; that remains deterministic producer
replay plus the previously audited lattice-mode formulas.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


G = [[2*int(i == j) for j in range(8)] for i in range(8)]
for i, j in ((0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (6, 7)):
    G[i][j] = G[j][i] = -1
ZERO = (0,)*8
A0 = (-1, -2, -3, -2, -1, -2, 0, 0)
H = (5, 8, 9, 8, 5, 0, 2, 2)


def dot(a, b):
    return sum(a[i]*G[i][j]*b[j] for i in range(8) for j in range(8))


def weight(s):
    return (dot(A0, s[0]), dot(H, s[0]))


def grade(s):
    return dot(s[0], s[0])//2+sum(i//8+1 for i in s[1])


def epsilon(a, b):
    parity = sum(a[i]*b[i] for i in range(8))
    parity += sum(a[i]*b[j]*G[i][j] for i in range(8) for j in range(i))
    return -1 if parity % 2 else 1


def plus(a, b):
    return tuple(x+y for x, y in zip(a, b))


def currents():
    simple = [tuple(int(i == j) for i in range(8)) for j in range(8)]
    def cartan(a):
        return {(ZERO, (i,)): Q(c) for i, c in enumerate(a) if c}
    return [cartan(A0), {(A0, ()): Q(1)},
            {(tuple(-v for v in A0), ()): Q(-1)}, cartan(H),
            {(simple[i], ()): Q(1) for i, c in enumerate(H) if c},
            {(tuple(-v for v in simple[i]), ()): Q(-c) for i, c in enumerate(H) if c}]


def pair(u, v):
    answer = Q(0)
    for (a, ao), c in u.items():
        for (b, bo), d in v.items():
            if a == b == ZERO and len(ao) == len(bo) == 1:
                answer += c*d*G[ao[0]][bo[0]]
            elif not ao and not bo and dot(a, a) == 2 and plus(a, b) == ZERO:
                answer += c*d*epsilon(a, b)
    return answer


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def independent_insert(vector, blocks, block, pivot_key, prime):
    out = dict(vector)
    rows = blocks.setdefault(block, {})
    for pivot in sorted(rows, key=pivot_key):
        coefficient = out.get(pivot, 0)
        if coefficient:
            for coordinate, value in rows[pivot].items():
                updated = (out.get(coordinate, 0)-coefficient*value) % prime
                if updated:
                    out[coordinate] = updated
                else:
                    out.pop(coordinate, None)
    assert out, 'Saved vector is linearly dependent'
    pivot = min(out, key=pivot_key)
    inverse = pow(out[pivot], -1, prime)
    out = {i: c*inverse % prime for i, c in out.items()}
    rows[pivot] = out
    return pivot, out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--certificate', default='hi_cft_20260923_next_x2_conditional_rank.json')
    ap.add_argument('--output', default='hi_cft_20260923_next_x2_replay.json')
    args = ap.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('60-second cap')))
    signal.alarm(60)
    started = monotonic()
    source, output = Path(args.certificate), Path(args.output)
    assert not output.exists() and source.stat().st_size < 8*1024**2
    cert = json.loads(source.read_text())
    assert cert['status'] == 'complete'
    p = cert['prime']
    assert p == 1000003 and all(p % d for d in range(2, 1001))
    assert [r*r % p for r in cert['square_roots_mod_prime']] == [13, p-3]
    for filename, expected in cert['source_sha256'].items():
        assert hashlib.sha256(Path(filename).read_bytes()).hexdigest() == expected
    basis = [(tuple(a), tuple(o)) for a, o in cert['B2_basis']]
    assert len(basis) == len(set(basis)) == 1370
    assert all(grade(s) == 2 for s in basis)
    block_dimensions = Counter(weight(s) for s in basis)
    assert {str(w): n for w, n in sorted(block_dimensions.items())} == cert['Cartan_block_dimensions']
    cs = currents()
    gram = [[pair(c, d) for d in cs] for c in cs]
    assert gram == [[Q(c) for c in row] for row in cert['X1_Gram_matrix']]
    x1_weights, x1_blocks = [], {}
    for definition in cert['X1_exact_projection_words']:
        a, o = definition['ambient_state']
        state = (tuple(a), tuple(o))
        assert grade(state) == 1
        coefficients = list(map(Q, definition['subtract_current_coefficients']))
        assert len(coefficients) == 6
        vector = {state: Q(1)}
        for coefficient, c in zip(coefficients, cs):
            for s, value in c.items():
                vector[s] = vector.get(s, 0)-coefficient*value
        vector = {s: c for s, c in vector.items() if c}
        assert vector and all(pair(c, vector) == 0 for c in cs)
        w = weight(state)
        assert all(weight(s) == w for s in vector)
        modular = {}
        for s, c in vector.items():
            assert c.denominator % p
            value = c.numerator*pow(c.denominator, -1, p) % p
            if value:
                modular[s] = value
        independent_insert(modular, x1_blocks, w, lambda s: s, p)
        x1_weights.append(w)
    assert len(x1_weights) == sum(map(len, x1_blocks.values())) == 80

    # The saved operator labels have exact U-word definitions. Recover
    # their weights without calling any lattice modes.
    field_file = Path('hi_cft_20260923_c8_exact_fields.json')
    fields = json.loads(field_file.read_text())['fields']
    field_weights = []
    for field in fields:
        weights = {weight((tuple(row['momentum']), tuple(row['oscillators'])))
                   for row in field['coefficients']}
        assert len(weights) == 1
        field_weights.append(weights.pop())
    current_weights = [next(iter({weight(s) for s in c})) for c in cs]
    operator_weights = []
    for i, row in enumerate(cert['S2_operators']):
        assert row['id'] == i and len(row['vector_sha256']) == 64
        word = row['word']
        kind = word['kind']
        if kind == 'current_derivative':
            w = current_weights[word['current']]
        elif kind == 'current_product':
            w = plus(current_weights[word['left']], current_weights[word['right']])
        elif kind == 'ambient_stress':
            w = (0, 0)
        elif kind == 'field':
            w = field_weights[word['field']]
        else:
            assert kind == 'field_descendant'
            w = plus(field_weights[word['field']],
                     (-2*word['left_lowering'], -2*word['right_lowering']))
        operator_weights.append(w)
    assert len(operator_weights) == 120
    u_entries = cert['actual_u']['vector']
    u_weights = {weight(basis[i]) for i, _ in u_entries}
    assert len(u_weights) == 1
    u_weight = u_weights.pop()

    rank_blocks, saved_weights = {}, []
    vector_file = Path(cert['independent_vectors_file'])
    assert vector_file.stat().st_size < 32*1024**2
    running_hash = hashlib.sha256()
    maximum_terms = 0
    with vector_file.open('rb') as handle:
        for idx, line in enumerate(handle):
            assert line.endswith(b'\n')
            running_hash.update(line)
            row = json.loads(line)
            assert row['id'] == idx
            coordinates = row['vector']
            assert coordinates and coordinates == sorted(coordinates)
            assert len({i for i, _ in coordinates}) == len(coordinates)
            assert all(0 <= i < 1370 and 0 < c < p for i, c in coordinates)
            w = tuple(row['Cartan_weight'])
            assert all(weight(basis[i]) == w for i, _ in coordinates)
            word = row['word']
            op = word['operator']
            if word['kind'] == 'X1_mode':
                j = word['X1']
                assert 0 <= j < 80
                base_weight = x1_weights[j]
                if op[0] == 'current':
                    assert word['mode'] == -1
                    operator_weight = current_weights[op[1]]
                else:
                    assert op[0] == 'S2' and word['mode'] == 0
                    operator_weight = operator_weights[op[1]]
            else:
                assert word['kind'] == 'accepted_mode' and 0 <= word['source'] < idx
                base_weight = saved_weights[word['source']]
                if op[0] == 'current':
                    assert op[1] in (1, 2, 4, 5) and word['mode'] == 0
                    operator_weight = current_weights[op[1]]
                else:
                    assert op == ['u'] and word['mode'] == 1
                    operator_weight = u_weight
            assert plus(base_weight, operator_weight) == w
            pivot, echelon = independent_insert(dict(coordinates), rank_blocks, w,
                                                lambda i: basis[i], p)
            assert pivot == row['pivot_state_id']
            assert digest([[i, c] for i, c in sorted(echelon.items())]) == row['echelon_row_sha256']
            saved_weights.append(w)
            maximum_terms = max(maximum_terms, len(coordinates), len(echelon))
    assert running_hash.hexdigest() == cert['independent_vectors_sha256']
    rank = sum(map(len, rank_blocks.values()))
    assert rank == len(saved_weights) == cert['independent_vectors'] == cert['rank_lower_bound'] == 1250
    assert {str(w): len(b) for w, b in sorted(rank_blocks.items())} == cert['Cartan_block_ranks']
    result = {'rank_independently_verified': rank, 'prime': p,
              'exact_X1_orthogonality_verified': True, 'X1_rank_verified': 80,
              'all_source_hashes_verified': True, 'all_vector_hashes_and_pivots_verified': True,
              'all_word_references_grading_and_Cartan_weights_verified': True,
              'mode_coefficients_reevaluated': False,
              'scope': 'Independent rank and exact-X1 audit. Word structure and weights are checked; equality of each saved vector to its stated mode word is supplied by the frozen producer, not re-evaluated here.',
              'maximum_saved_or_echelon_vector_terms': maximum_terms,
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              'source_sha256': {str(f): hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in (Path(__file__), source, vector_file, field_file)}}
    output.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print(result, flush=True)


if __name__ == '__main__':
    main()
