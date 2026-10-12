"""Bounded split-prime certificate for descendants of K1-perp in B2.

Root alone may run this through hi_cft_safe_run.py, at <=2 GiB AS.
Estimated RSS <0.25 GiB, conservative budget0.5 GiB, hard alarm300s.
No statement of properness is assumed by the calculation. If U is proper,
its established B=U+X decomposition identifies the exact K1-perp with X1.
All recorded mode words then belong to X2. Rank1250 forces U2=S2;
rank>1250 contradicts properness. A smaller rank is inconclusive.
"""
import argparse
from collections import Counter, deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3


PRIME = 1000003
VACUUM_STATE = (x.ZERO, ())


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def roots_and_bases():
    roots, todo = set(x.SIMPLE), list(x.SIMPLE)
    while todo:
        a = todo.pop()
        for i, simple in enumerate(x.SIMPLE):
            b = list(a)
            b[i] -= x.dot(a, simple)
            b = tuple(b)
            if b not in roots:
                roots.add(b)
                todo.append(b)
    assert len(roots) == 78 and all(x.norm(a) == 2 for a in roots)
    norm4 = {x.plus(a, b) for a in roots for b in roots if x.dot(a, b) == 0}
    assert len(norm4) == 702
    basis1 = ([(x.ZERO, (i,)) for i in range(8)]
              + [(a, ()) for a in sorted(roots)])
    basis2 = ([(x.ZERO, (8+i,)) for i in range(8)]
              + [(x.ZERO, (i, j)) for i, j in combinations_with_replacement(range(8), 2)]
              + [(a, (i,)) for a in sorted(roots) for i in range(8)]
              + [(a, ()) for a in sorted(norm4)])
    # Completeness of this norm4 list is independently certified by rational
    # LDL in next_residual_ambient2.json; only containment is needed for rank.
    assert len(basis1) == 86 and len(set(basis2)) == len(basis2) == 1370
    return basis1, basis2


def rational_coefficient(value):
    assert value[1:] == (0, 0, 0)
    return value[0]


def pairing(u, v):
    out = x.mode(u, 1, v)
    assert set(out) <= {VACUUM_STATE}
    return rational_coefficient(out.get(VACUUM_STATE, x.ZERO_A))


def exact_complement(basis1):
    """Exact rational orthogonal projection; no numerical recognition."""
    currents = x.LEFT+x.RIGHT
    gram = [[pairing(c, d) for d in currents] for c in currents]
    inverse = x.inverse(gram)
    span, vectors, definitions = x.Span(), [], []
    for state in basis1:
        v = {state: x.ONE}
        b = [pairing(c, v) for c in currents]
        coefficients = [sum(inverse[i][j]*b[j] for j in range(6))
                        for i in range(6)]
        projected = x.vadd((1, v), *[(-a, c) for a, c in zip(coefficients, currents)])
        assert all(pairing(c, projected) == 0 for c in currents)
        if span.reduce(projected, True):
            vectors.append(projected)
            definitions.append({'ambient_state': [list(state[0]), list(state[1])],
                                'subtract_current_coefficients': list(map(str, coefficients))})
    assert span.dimension == len(vectors) == 80
    return vectors, definitions, gram


def s2_operators(data):
    """Raw, known U words, retaining independent representatives mod p."""
    span, operators = x.Span(), []
    def add(v, word):
        if span.reduce(v, True):
            operators.append((v, word))
    currents = x.LEFT+x.RIGHT
    for i, c in enumerate(currents):
        add(x.mode(c, -2, x.VAC), {'kind': 'current_derivative', 'current': i})
        for j, d in enumerate(currents):
            add(x.mode(c, -1, d), {'kind': 'current_product', 'left': i, 'right': j})
    add(x.omega(), {'kind': 'ambient_stress'})
    add(x.read_field(data['fields'][-1]), {'kind': 'field', 'field': len(data['fields'])-1})
    for i, row in enumerate(data['fields'][:-1]):
        n, m = row['dimensions']
        for j, v in enumerate(x.descendants(x.read_field(row), n, m)):
            add(v, {'kind': 'field_descendant', 'field': i,
                    'left_lowering': j//m, 'right_lowering': j % m})
    assert span.dimension == len(operators) == 120
    return operators


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', default='hi_cft_20260923_next_x2_conditional_rank.json')
    ap.add_argument('--seconds', type=int, default=300)
    args = ap.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    assert 0 < args.seconds <= 300
    output = Path(args.output)
    records_path = output.with_suffix('.vectors.jsonl')
    assert not output.exists() and not records_path.exists(), 'Refusing overwrite'
    sources = [Path(__file__), Path(x.__file__), Path(g3.__file__),
               Path('hi_cft_20260923_next_grade4_exact.py'),
               Path('hi_cft_20260923_c8_exact_fields.json')]
    source_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    started = monotonic()
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('300-second cap')))
    signal.alarm(args.seconds)
    # Replace, rather than wrap, the original cached functions so that only
    # one bounded cache remains live at each layer. Stay in grades0,1,2.
    x.vertex = lru_cache(maxsize=4096)(x.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=4096)(x.basis_mode.__wrapped__)
    basis1, basis2 = roots_and_bases()
    state_ids = {state: i for i, state in enumerate(basis2)}
    block_dimensions = Counter(x.weight(s) for s in basis2)
    assert max(block_dimensions.values()) <= 100
    exact_x1, definitions, gram = exact_complement(basis1)
    rational_x1 = [{s: rational_coefficient(c) for s, c in v.items()} for v in exact_x1]
    del exact_x1
    # install_prime verifies primality and the two square roots. Its F(Q)
    # constructor rejects every rational denominator divisible by PRIME.
    square_roots = g3.install_prime(PRIME)
    assert square_roots == [231543, 1000]
    x1 = [{s: x.A(c) for s, c in v.items()} for v in rational_x1]
    del rational_x1
    check = x.Span()
    for v in x1:
        check.reduce(v, True)
    assert check.dimension == 80
    # Clear any rational-mode cache entries; all primitive cache values are
    # rational scalars independent of A, but avoiding mixed liveness is easy.
    x.vertex.cache_clear()
    x.basis_mode.cache_clear()
    field_source = sources[-1]
    assert field_source.stat().st_size <= 8*1024**2
    data = json.loads(field_source.read_text())
    ops = s2_operators(data)
    # Actual three-vertex generator, exactly the frozen grade4 recipe.
    # The last JSON field is a stress vector and must not be called u.
    u = {((0, 0, 0, 0, 0, -1, 1, 1), ()): x.ONE,
         ((0, 0, 0, 1, 1, -1, 0, 0), ()): x.A((0, Q(1, 20), Q(3, 20), 0)),
         ((1, 1, 0, 0, 0, -1, 0, 0), ()): x.A((0, Q(1, 20), -Q(3, 20), 0))}
    s2_check = x.Span()
    for v, _ in ops:
        s2_check.reduce(v, True)
    assert not s2_check.reduce(u)
    del s2_check
    span, queue, accepted, history = x.Span(), deque(), [], []
    records_hash = hashlib.sha256()
    records = records_path.open('x')
    candidate_count = 0

    def encode(v):
        return [[state_ids[s], int(c)] for s, c in sorted(v.items(), key=lambda item: state_ids[item[0]])]

    def consume(v, word):
        nonlocal candidate_count
        candidate_count += 1
        assert all(x.grade(s) == 2 and s in state_ids for s in v)
        reduced = span.reduce(v, True)
        if reduced:
            idx = len(accepted)
            accepted.append(v)
            queue.append(idx)
            row = {'id': idx, 'word': word, 'Cartan_weight': list(x.weight(next(iter(v)))),
                   'vector': encode(v), 'echelon_row_sha256': digest(encode(reduced)),
                   'pivot_state_id': state_ids[min(reduced)]}
            line = json.dumps(row, sort_keys=True, separators=(',', ':'))+'\n'
            records.write(line)
            records.flush()
            records_hash.update(line.encode())
            assert len(accepted) == span.dimension <= 1370
            if span.dimension > 1250:
                raise StopIteration('rank exceeds1250: properness contradicted')
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 512*1024:
            raise MemoryError('0.5 GiB RSS review budget reached')

    def close():
        # Cartans act diagonally on every retained vector. The four raising
        # and lowering currents, plus actual u_1, give a bounded tested closure.
        for_current = (1, 2, 4, 5)
        while queue:
            idx = queue.popleft()
            v = accepted[idx]
            for j in for_current:
                consume(x.mode((x.LEFT+x.RIGHT)[j], 0, v),
                        {'kind': 'accepted_mode', 'operator': ['current', j],
                         'mode': 0, 'source': idx})
            consume(x.mode(u, 1, v),
                    {'kind': 'accepted_mode', 'operator': ['u'], 'mode': 1, 'source': idx})

    def checkpoint(stage, status='running'):
        records.flush()
        history.append({'stage': stage, 'rank': span.dimension,
                        'candidates': candidate_count, 'seconds': monotonic()-started})
        if span.dimension > 1250:
            consequence = 'The known U-mode words contradict U proper; hence U=B under the established fork.'
        elif span.dimension == 1250:
            consequence = 'If U is proper, then dimX2=1250 and U2=S2 has dimension120.'
        else:
            consequence = 'Only a conditional lower bound on dimX2; no properness conclusion.'
        result = {'status': status, 'prime': PRIME, 'square_roots_mod_prime': square_roots,
                  'arithmetic': 'exact finite field; characteristic-zero lower bound only',
                  'rank_lower_bound': span.dimension, 'ambient_B2_dimension': 1370,
                  'certified_S2_dimension': 120, 'threshold': 1250,
                  'logical_consequence': consequence,
                  'properness_assumed_by_calculation': False,
                  'X1_definition': 'Exact rational orthogonal projection onto K1-perp using (a,b)=a_1 b; K1 is PCT-stable, so this is also its Hermitian orthogonal complement.',
                  'X1_Gram_current_order': ['Lh', 'Le', 'Lf', 'Rh', 'Re', 'Rf'],
                  'X1_Gram_matrix': [list(map(str, row)) for row in gram],
                  'X1_exact_projection_words': definitions,
                  'good_denominators': 'Every exact X1/field coefficient and every rational mode scalar is converted by F(Q), which asserts its denominator is nonzero modulo p; elimination divides only nonzero pivots.',
                  'S2_operators': [{'id': i, 'word': word, 'vector_sha256': digest(encode(v))}
                                   for i, (v, word) in enumerate(ops)],
                  'actual_u': {'source': 'next_grade4_exact.Database.evaluate: op=u',
                               'vector': encode(u)},
                  'B2_basis': [[list(a), list(o)] for a, o in basis2],
                  'Cartan_block_dimensions': {str(w): n for w, n in sorted(block_dimensions.items())},
                  'Cartan_block_ranks': {str(w): len(b) for w, b in sorted(span.blocks.items()) if b},
                  'independent_vectors_file': str(records_path),
                  'independent_vectors_sha256': records_hash.hexdigest(),
                  'independent_vectors': len(accepted), 'candidates': candidate_count,
                  'history': history, 'seconds': monotonic()-started,
                  'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  'source_sha256': source_hashes,
                  'replay': 'Run this frozen producer with a fresh --output. Compare source hashes, exact X1 definitions, operator hashes, basis order and independent-vector JSONL hashes. Each record is an explicit U-mode word on an exact X1 vector, and records include all finite-field independent vectors and normalized-echelon hashes.'}
        temporary = output.with_suffix(output.suffix+'.tmp')
        temporary.write_text(json.dumps(result, indent=2)+'\n')
        temporary.replace(output)
        print(history[-1] | {'status': status}, flush=True)

    try:
        checkpoint('initialized')
        for i, c in enumerate(x.LEFT+x.RIGHT):
            for j, v in enumerate(x1):
                consume(x.mode(c, -1, v),
                        {'kind': 'X1_mode', 'operator': ['current', i], 'mode': -1, 'X1': j})
        close()
        checkpoint('K_negative_one_and_zero_modes_and_u1')
        for i in sorted(range(len(ops)), key=lambda j: (len(ops[j][0]), j)):
            for j, v in enumerate(x1):
                consume(x.mode(ops[i][0], 0, v),
                        {'kind': 'X1_mode', 'operator': ['S2', i], 'mode': 0, 'X1': j})
            close()
            checkpoint('S2_operator_'+str(i))
        checkpoint('all_requested_words_and_tested_closure', 'complete')
    except StopIteration as error:
        checkpoint(str(error), 'properness_contradicted')
    except (TimeoutError, MemoryError) as error:
        signal.alarm(0)
        # An asynchronous alarm can interrupt an insertion or JSONL write.
        # Preserve the last complete certified prefix, rather than claiming
        # that the interrupted in-memory row is a committed certificate.
        if output.exists():
            saved = json.loads(output.read_text())
            saved['status'] = 'bounded_stop'
            saved['stop_reason'] = str(error)
            saved['seconds_at_stop'] = monotonic()-started
            temporary = output.with_suffix(output.suffix+'.tmp')
            temporary.write_text(json.dumps(saved, indent=2)+'\n')
            temporary.replace(output)
            print({'status': 'bounded_stop', 'certified_rank': saved['rank_lower_bound'],
                   'reason': str(error)}, flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        records.close()


if __name__ == '__main__':
    main()
