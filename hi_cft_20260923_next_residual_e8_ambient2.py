"""Bounded exact grade-two commutant of the c=22/5 core in E8.

ROOT-ONLY numerical job through hi_cft_safe_run.py --limit-mib 2048.
No numerical work is done on import. New output is checkpointed atomically
after each of the three E6+A2 charge sectors. See the companion resource
review before launching. Existing exact producers are not modified.
"""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement
from math import isqrt
from pathlib import Path
import hashlib
import json
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3
import hi_cft_20260923_next_81top_exact as top
from hi_cft_20260923_next_structure_core_extension import read


MAX_BLOCK = 256
MAX_SAVED_TERMS = 160000
MAX_VECTOR_TERMS = 6000
MAX_BITS = 2048
MAX_SERIALIZED_TERMS = 12000


class BudgetStop(Exception):
    pass


def check_vector(v):
    if len(v) > MAX_VECTOR_TERMS:
        raise BudgetStop('individual sparse vector term cap')
    for c in v.values():
        if isinstance(c, x.A):
            parts = c
        else:
            parts = (Q(c),)
        if any(max(abs(a.numerator).bit_length(), a.denominator.bit_length())
               > MAX_BITS for a in parts):
            raise BudgetStop('coefficient bit cap')
    return v


def bounded_cache(function, size, term_cap):
    """Bound cached result length as well as the number of cache entries."""
    @lru_cache(maxsize=size)
    def wrapped(*args):
        result = function(*args)
        if len(result) > term_cap:
            raise BudgetStop('individual mode-cache result term cap')
        return result
    return wrapped


def install_engine(epsilon):
    # No original-mode cache may survive the change of cocycle.
    for f in (x.vertex, x.basis_mode, x.creation, g3.vertex,
              g3.basis_mode, g3.creation, x.cocycle):
        if hasattr(f, 'cache_clear'):
            f.cache_clear()
    g3.creation = bounded_cache(g3.creation.__wrapped__, 128, 256)
    g3.vertex = bounded_cache(g3.vertex.__wrapped__, 512, 512)
    g3.basis_mode = bounded_cache(g3.basis_mode.__wrapped__, 512, 512)
    x.creation, x.vertex, x.basis_mode = g3.creation, g3.vertex, g3.basis_mode
    x.cocycle = epsilon


def clear_engine():
    for f in (g3.creation, g3.vertex, g3.basis_mode, g3.OLD_CREATION, x.dot):
        f.cache_clear()


def mode(u, n, v):
    return check_vector(x.mode(u, n, v))


def lattice_ball(gram, bound):
    """Complete rational LDL sphere enumeration in the integral E8 basis."""
    lower = [[Q(int(i == j)) for j in range(8)] for i in range(8)]
    diagonal = []
    for j in range(8):
        diagonal.append(Q(gram[j][j])-sum(lower[j][k]**2*diagonal[k]
                                         for k in range(j)))
        assert diagonal[j] > 0
        for i in range(j+1, 8):
            lower[i][j] = (Q(gram[i][j])-sum(lower[i][k]*lower[j][k]*diagonal[k]
                                           for k in range(j)))/diagonal[j]
    for i in range(8):
        for j in range(8):
            assert sum(lower[i][k]*diagonal[k]*lower[j][k]
                       for k in range(8)) == gram[i][j]
    result, a = set(), [0]*8
    def visit(i, remaining):
        if i < 0:
            result.add(tuple(a))
            if len(result) > 2500:
                raise BudgetStop('momentum-ball size cap')
            return
        offset = sum(lower[j][i]*a[j] for j in range(i+1, 8))
        squared = remaining/diagonal[i]
        radius = isqrt(squared.numerator//squared.denominator)+2
        center = (-offset).numerator//(-offset).denominator
        for value in range(center-radius, center+radius+1):
            cost = diagonal[i]*(value+offset)**2
            if cost <= remaining:
                a[i] = value
                visit(i-1, remaining-cost)
    visit(7, Q(bound))
    return result


def kernel(vectors, image):
    """Exact sparse elimination, retaining lifts and bounding their liveness."""
    pivots, answers = {}, []
    saved_terms = 0
    for vector in vectors:
        pre, out = vector.copy(), image(vector)
        while out:
            pivot = min(out)
            if pivot not in pivots:
                scale = out[pivot].inv()
                row = check_vector({s: c*scale for s, c in out.items()})
                lift = check_vector({s: c*scale for s, c in pre.items()})
                saved_terms += len(row)+len(lift)
                if saved_terms > MAX_SAVED_TERMS:
                    raise BudgetStop('kernel saved coefficient term cap')
                pivots[pivot] = row, lift
                break
            row, lift = pivots[pivot]
            factor = out[pivot]
            out = check_vector(x.vadd((1, out), (-factor, row)))
            pre = check_vector(x.vadd((1, pre), (-factor, lift)))
        else:
            assert pre, 'independent input basis required'
            saved_terms += len(pre)
            if saved_terms > MAX_SAVED_TERMS:
                raise BudgetStop('kernel saved coefficient term cap')
            answers.append(pre)
    return answers, saved_terms


def pack(v):
    return [{'momentum': list(map(str, a)), 'oscillators': list(o),
             'coefficient': list(map(str, c))}
            for (a, o), c in sorted(v.items())]


def atomic_write(path, data):
    temporary = path.with_name(path.name+'.tmp')
    with temporary.open('w') as f:
        json.dump(data, f, indent=2)
        f.write('\n')
    temporary.replace(path)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', required=True)
    ap.add_argument('--seconds', type=int, default=280)
    ap.add_argument('--glue-sign', type=int, choices=(-1, 1), default=1)
    args = ap.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    assert 1 <= args.seconds <= 290
    output = Path(args.output)
    assert not output.exists(), 'refusing to overwrite a certificate'
    started = monotonic()
    def stop(*_):
        raise BudgetStop('time or external stop')
    signal.signal(signal.SIGALRM, stop)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    signal.alarm(args.seconds)
    sources = [Path('hi_cft_20260923_proof_potts_exact.json'),
               Path('hi_cft_20260923_proof_pf13_exact.json'),
               Path('hi_cft_20260923_proof_remaining_axes.json'),
               Path('hi_cft_20260923_next_residual_ambient2.json')]
    assert all(p.stat().st_size <= 2*1024**2 for p in sources)
    potts, pf, axes, old_certificate = [json.loads(p.read_text()) for p in sources]
    p, z = read(potts['potts_stress']), read(pf['stress'])
    q, r = read(axes['first_stress']), read(axes['second_stress'])
    old_basis = [read(v) for v in old_certificate['basis']]
    assert old_certificate['exact_residual_commutant_grade2_dimension'] == 5
    del potts, pf, axes, old_certificate

    # The old lattice embeds in a chosen E8 gluing. The sector_setup
    # gauge was independently audited against the old lattice cocycle.
    plus_roots, _, gauge, epsilon = top.sector_setup(args.glue_sign, 1)
    inverse = x.inverse(x.G)
    lam = tuple(inverse[i][0]+args.glue_sign*inverse[i][6] for i in range(8))
    m = [[Q(i == j) for j in range(8)] for i in range(8)]
    m[7] = list(lam)
    gram = top.integers(top.multiply(top.multiply(m, x.G), top.transpose(m)))
    def old_coordinates(a):
        return tuple(sum(a[i]*m[i][j] for i in range(8)) for j in range(8))
    def sector(a):
        residues = []
        for k in range(3):
            if all((a[i]-k*lam[i]).denominator == 1 for i in range(8)):
                residues.append(k)
        assert len(residues) == 1
        return residues[0]
    def gauged(v):
        return {s: c*gauge(s[0]) for s, c in v.items()}
    p, z, q, r = map(gauged, (p, z, q, r))
    old_basis = [gauged(v) for v in old_basis]
    currents = tuple(gauged(v) for v in x.LEFT+(x.RIGHT[0],))
    install_engine(epsilon)
    omega_a = x.vadd((Q(1, 4), mode(currents[0], -1, currents[0])),
                     (Q(1, 156), mode(currents[-1], -1, currents[-1])),
                     (1, p), (1, z))
    residual = x.vadd((1, x.omega()), (-1, omega_a))
    assert not x.vadd((1, residual), (-1, q), (-1, r))
    assert mode(omega_a, 3, omega_a) == {(x.ZERO, ()): x.A(Q(11, 5))}
    assert not x.vadd((1, mode(omega_a, 1, omega_a)), (-2, omega_a))

    momenta = {old_coordinates(a) for a in lattice_ball(gram, 4)}
    roots = sorted(a for a in momenta if x.norm(a) == 2)
    norm4 = sorted(a for a in momenta if x.norm(a) == 4)
    assert len(momenta) == 2401 and len(roots) == 240 and len(norm4) == 2160
    assert {a for a in roots if sector(a) == 1} == set(plus_roots)
    assert {a for a in roots if sector(a) == 2} == {tuple(-b for b in a) for a in plus_roots}
    assert sum(sector(a) == 0 for a in roots) == 78
    assert sum(sector(a) == 0 for a in norm4) == 702
    zero_blocks = {k: [] for k in range(3)}
    ambient_sizes = [0, 0, 0]
    def retain(state):
        k = sector(state[0])
        assert x.grade(state) == 2
        ambient_sizes[k] += 1
        if x.weight(state) == (0, 0):
            zero_blocks[k].append({state: x.ONE})
            if len(zero_blocks[k]) > MAX_BLOCK:
                raise BudgetStop('Cartan-zero block size cap')
    for i in range(8):
        retain((tuple(map(Q, x.ZERO)), (8+i,)))
    for i, j in combinations_with_replacement(range(8), 2):
        retain((tuple(map(Q, x.ZERO)), (i, j)))
    for a in roots:
        for i in range(8):
            retain((a, (i,)))
    for a in norm4:
        retain((a, ()))
    assert ambient_sizes == [1370, 1377, 1377]
    assert len(zero_blocks[0]) == 86
    del momenta, roots, norm4, plus_roots
    metadata_sources = [Path(__file__), Path(x.__file__), Path(g3.__file__),
                        Path(top.__file__),
                        Path('hi_cft_20260923_next_structure_core_extension.py'), *sources]
    result = {
        'complete': False, 'arithmetic': 'Q(sqrt(13),sqrt(-3))',
        'glue_sign': args.glue_sign,
        'coordinate_convention': 'momenta are rational old E6+A2 coordinates; '
                                 'E8 ungauged cocycle, B coefficients gauge transformed',
        'ambient_grade2_dimension': sum(ambient_sizes),
        'ambient_grade2_sector_dimensions': ambient_sizes,
        'Cartan_zero_sector_dimensions': [len(zero_blocks[k]) for k in range(3)],
        'complete_momentum_ball_verified_by_rational_LDL': True,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in metadata_sources},
        'sectors': [],
        'scope': 'Full E8 grade-two zero-energy space for the actual c=22/5 '
                 'unitary rational core. Positivity identifies this kernel '
                 'with its commutant; no rationality or identification of '
                 'the commutant is asserted.'}
    atomic_write(output, result)
    print(json.dumps({k: result[k] for k in ('ambient_grade2_sector_dimensions',
                                            'Cartan_zero_sector_dimensions')}), flush=True)
    serialized_terms = 0
    try:
        for k in range(3):
            clear_engine()
            vectors, saved_terms = kernel(zero_blocks.pop(k),
                                         lambda v: mode(omega_a, 1, v))
            span = x.Span()
            for v in vectors:
                assert not mode(omega_a, 1, v)
                assert not mode(omega_a, 0, v)
                for stress in (p, z):
                    for n in (0, 1, 2, 3):
                        assert not mode(stress, n, v)
                for current in currents:
                    for n in (0, 1, 2):
                        assert not mode(current, n, v)
                span.reduce(v, True)
            assert span.dimension == len(vectors)
            if k == 0:
                assert len(vectors) == 5
                assert all(not span.reduce(v) for v in old_basis)
                assert not span.reduce(q) and not span.reduce(r)
                del old_basis
            serialized_terms += sum(map(len, vectors))
            if serialized_terms > MAX_SERIALIZED_TERMS:
                raise BudgetStop('cumulative serialized kernel term cap')
            record = {'sector': k, 'dimension': len(vectors),
                      'kernel_saved_terms': saved_terms,
                      'stress_zero_and_current_nonnegative_modes_passed': True,
                      'all_basis_vectors_quasiprimary': all(
                          not mode(x.omega(), 2, v) for v in vectors),
                      'basis': [pack(v) for v in vectors],
                      'seconds': monotonic()-started,
                      'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
            if k == 0:
                record['saved_B_kernel_span_reproduced'] = True
            result['sectors'].append(record)
            atomic_write(output, result)
            print(json.dumps({key: value for key, value in record.items()
                              if key != 'basis'}), flush=True)
            del vectors, span, record
        result['complete'] = True
        result['exact_commutant_grade2_dimension'] = sum(r['dimension'] for r in result['sectors'])
        result['seconds'] = monotonic()-started
        result['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        atomic_write(output, result)
        signal.alarm(0)
        print(json.dumps({k: result[k] for k in ('complete', 'exact_commutant_grade2_dimension',
                                               'seconds', 'peak_rss_KiB')}), flush=True)
    except BudgetStop as exc:
        result['stop_reason'] = str(exc)
        result['seconds'] = monotonic()-started
        atomic_write(output, result)
        raise


if __name__ == '__main__':
    main()
