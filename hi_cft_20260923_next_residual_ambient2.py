"""Exact grade-two ambient commutant of the c=22/5 rational core.

Root-only safe_run job. At most 1370 sparse ambient basis states are
enumerated, then only the joint Cartan-zero block is retained (hard cap
256). A small sparse kernel is computed without NumPy/SymPy or dense
ambient matrices. Conservative estimate <0.5 GiB RSS; 2 GiB AS and
300-second internal alarm. No higher-grade basis or worker is created.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import isqrt
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3
from hi_cft_20260923_next_structure_core_extension import read, serialize, kernel


def lattice_ball(bound):
    """Complete exact sphere enumeration using rational LDL factors."""
    lower = [[Q(int(i == j)) for j in range(8)] for i in range(8)]
    diagonal = []
    for j in range(8):
        diagonal.append(Q(x.G[j][j])-sum(lower[j][k]**2*diagonal[k]
                                         for k in range(j)))
        assert diagonal[j] > 0
        for i in range(j+1, 8):
            lower[i][j] = (Q(x.G[i][j])-sum(lower[i][k]*lower[j][k]*diagonal[k]
                                           for k in range(j)))/diagonal[j]
    for i in range(8):
        for j in range(8):
            assert sum(lower[i][k]*diagonal[k]*lower[j][k]
                       for k in range(8)) == x.G[i][j]
    result, a = set(), [0]*8
    def visit(i, remaining):
        if i < 0:
            result.add(tuple(a))
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
    assert len(result) <= 1000
    return result


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(300)
    started = monotonic()
    # The explicit commutant check includes stress mode zero, whose
    # output has grade three. Install the audited grade-three engine.
    x.creation, x.vertex, x.basis_mode = g3.creation, g3.vertex, g3.basis_mode
    sources = [Path('hi_cft_20260923_proof_potts_exact.json'),
               Path('hi_cft_20260923_proof_pf13_exact.json'),
               Path('hi_cft_20260923_proof_remaining_axes.json')]
    potts, pf, axes = [json.loads(p.read_text()) for p in sources]
    p, z = read(potts['potts_stress']), read(pf['stress'])
    q, r = read(axes['first_stress']), read(axes['second_stress'])
    omega_a = x.vadd((Q(1, 4), x.mode(x.LEFT[0], -1, x.LEFT[0])),
                     (Q(1, 156), x.mode(x.RIGHT[0], -1, x.RIGHT[0])),
                     (1, p), (1, z))
    residual = x.vadd((1, x.omega()), (-1, omega_a))
    assert not x.vadd((1, residual), (-1, q), (-1, r))
    assert x.mode(omega_a, 3, omega_a) == {(x.ZERO, ()): x.A(Q(11, 5))}

    simple = [tuple(int(i == j) for i in range(8)) for j in range(8)]
    roots = set(simple)
    todo = list(simple)
    while todo:
        a = todo.pop()
        for i in range(8):
            b = list(a)
            b[i] -= x.dot(a, simple[i])
            b = tuple(b)
            if b not in roots:
                roots.add(b)
                todo.append(b)
    assert len(roots) == 78 and all(x.norm(a) == 2 for a in roots)
    norm4 = {x.plus(a, b) for a in roots for b in roots if x.dot(a, b) == 0}
    assert len(norm4) == 702
    ball = lattice_ball(4)
    assert ball == {x.ZERO} | roots | norm4
    basis = ([(x.ZERO, (8+i,)) for i in range(8)]
             + [(x.ZERO, (i, j)) for i, j in combinations_with_replacement(range(8), 2)]
             + [(a, (i,)) for a in sorted(roots) for i in range(8)]
             + [(a, ()) for a in sorted(norm4)])
    assert len(basis) == len(set(basis)) == 1370
    zero = [{state: x.ONE} for state in basis if x.weight(state) == (0, 0)]
    assert len(zero) <= 256
    print({'ambient_Cartan_zero_dimension': len(zero),
           'seconds': monotonic()-started}, flush=True)
    vectors = kernel(zero, lambda v: x.mode(omega_a, 1, v))
    C = x.Span()
    for v in vectors:
        assert not x.mode(omega_a, 1, v)
        assert not x.mode(omega_a, 0, v)
        for stress in (p, z):
            for n in (0, 1, 2, 3):
                assert not x.mode(stress, n, v)
        for current in x.LEFT+(x.RIGHT[0],):
            for n in (0, 1, 2):
                assert not x.mode(current, n, v)
        C.reduce(v, True)
    assert C.dimension == len(vectors)
    assert not C.reduce(q) and not C.reduce(r)
    known = x.Span()
    known.reduce(q, True)
    known.reduce(r, True)
    new = [v for v in vectors if known.reduce(v)]
    result = {
        'ambient_grade2_dimension': len(basis),
        'ambient_Cartan_zero_dimension': len(zero),
        'exact_residual_commutant_grade2_dimension': len(vectors),
        'known_q_r_dimension': known.dimension,
        'all_vectors_in_q_r_span': not new,
        'all_basis_vectors_quasiprimary': all(not x.mode(x.omega(), 2, v) for v in vectors),
        'complete_momentum_ball_verified_by_rational_LDL': True,
        'basis': [serialize(v) for v in vectors],
        'basis_vectors_outside_q_r_span': [serialize(v) for v in new],
        'scope': 'Full grade-two kernel of the c=22/5 core stress in B, '
                 'not merely the generated S2. Positivity of the unitary '
                 'core identifies its zero-energy subspace with its '
                 'commutant. No rationality of this commutant is asserted.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in [Path(__file__), Path(x.__file__),
                              Path(g3.__file__),
                              Path('hi_cft_20260923_next_structure_core_extension.py'), *sources]}}
    path = Path('hi_cft_20260923_next_residual_ambient2.json')
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print({k: v for k, v in result.items()
           if k not in ('basis', 'basis_vectors_outside_q_r_span', 'source_sha256')}, flush=True)


if __name__ == '__main__':
    main()
