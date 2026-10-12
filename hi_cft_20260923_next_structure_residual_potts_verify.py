"""Ambient verification of the unique residual c=4/5 axis.

Root-only safe_run job, <=2 GiB AS, <=300 seconds; estimated <0.5 GiB.
Only five saved residual fields, the certified 120-vector S2, bounded
grade-three mode caches, and tiny exact kernels are used. No workers,
dense ambient matrices, numerical recognition, or Groebner work.
"""

from fractions import Fraction as Q
import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3
from hi_cft_20260923_next_81top_exact import pct
from hi_cft_20260923_next_structure_core_extension import (
    kernel, read, reconstruct_s2, serialize)
from hi_cft_20260923_next_structure_residual_tensor import (
    coordinate_map, encode, pairing)


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(300)
    started = monotonic()
    sources = [Path('hi_cft_20260923_next_structure_residual_tensor.json'),
               Path('hi_cft_20260923_next_structure_residual_potts.json'),
               Path('hi_cft_20260923_c8_exact_fields.json')]
    tensor, solve, fields = [json.loads(p.read_text()) for p in sources]
    assert tensor['exact_dimension'] == 5
    assert solve['target_central_charge'] == '4/5'
    assert solve['Groebner_basis_size'] == 4 and solve['Groebner_total_terms'] == 8
    basis = list(map(read, tensor['basis']))
    coordinates = [x.A(Q(1, 24)), x.A(Q(8, 21)),
                   x.A((Q(7, 120), 0, Q(7, 120), 0)),
                   x.A((Q(19, 400), Q(1, 400), Q(7, 400), Q(1, 400))),
                   x.A((Q(19, 400), Q(-1, 400), Q(-7, 400), Q(1, 400)))]
    e = x.vadd(*zip(coordinates, basis))
    total = x.vadd((1, basis[0]), (1, basis[1]))
    complement = x.vadd((1, total), (-1, e))
    core = x.vadd((1, x.omega()), (-1, total))
    assert pct(e) == e and pct(complement) == complement
    S2 = reconstruct_s2(fields)
    membership = not S2.reduce(e)
    # Explicit positive-mode and translation tests reach at most grade3.
    x.creation, x.vertex, x.basis_mode = g3.creation, g3.vertex, g3.basis_mode
    for stress, central in ((e, Q(4, 5)), (complement, Q(14, 5))):
        assert not x.vadd((1, x.mode(stress, 1, stress)), (-2, stress))
        assert not x.mode(stress, 2, stress)
        assert pairing(stress, stress) == x.A(central/2)
        assert not x.vadd((1, x.mode(stress, 0, stress)),
                          (-1, x.mode(x.omega(), 0, stress)))
        assert not x.mode(x.omega(), 2, stress)
        for n in (0, 1, 2, 3):
            assert not x.mode(core, n, stress)
    for n in (0, 1, 2, 3):
        assert not x.mode(e, n, complement)
    coords = coordinate_map(basis)
    action = [coords(x.mode(e, 1, v)) for v in basis]
    # All Virasoro M(5,6) sectors, including sectors excluded by the
    # weight-three Potts extension (which has not yet been proved here).
    kac_weights = {Q((6*r-5*s)**2-1, 120)
                   for r in range(1, 5) for s in range(1, 6)}
    eigenvalues = sorted({h+n for h in kac_weights for n in range(3)
                          if 0 <= h+n <= 2})
    eigenrecords = []
    total_dimension = 0
    for weight in eigenvalues:
        vectors = kernel(basis, lambda v: x.vadd((1, x.mode(e, 1, v)), (-weight, v)))
        if vectors:
            total_dimension += len(vectors)
            eigenrecords.append({'weight': str(weight), 'dimension': len(vectors),
                                 'basis': list(map(serialize, vectors))})
    assert total_dimension == 5, 'Unexpected c=4/5 unitary weight in residual grade2'

    # A standard sqrt(2)A2 Potts realization is a sufficient extra
    # identification, not a necessary form of a c=4/5 Virasoro vector.
    momenta = {a for a, osc in e if a != x.ZERO}
    lattice_planes = []
    if len(momenta) == 6 and all(x.norm(a) == 4 for a in momenta):
        for alpha, beta in combinations(sorted(momenta), 2):
            if x.dot(alpha, beta) != -2:
                continue
            gamma = x.plus(alpha, beta)
            target = {alpha, beta, gamma, *[tuple(-a for a in v)
                                          for v in (alpha, beta, gamma)]}
            if target != momenta:
                continue
            h, k = x.cartan(alpha), x.cartan(beta)
            standard = x.vadd((Q(1, 15), x.mode(h, -1, h)),
                              (Q(1, 15), x.mode(k, -1, k)),
                              (Q(1, 15), x.mode(h, -1, k)))
            oscillator = {s: c for s, c in e.items() if s[0] == x.ZERO}
            if oscillator == standard:
                lattice_planes.append([alpha, beta])
    result = {
        'central_charge': '4/5', 'complement_central_charge': '14/5',
        'exact_PCT': True, 'exact_ambient_Virasoro_OPE': True,
        'exact_mutual_commutation': True, 'exact_core_commutation': True,
        'membership_in_certified_S2': membership,
        'scope_of_membership': 'Failure of S2 membership does not prove absence from all U2.',
        'axis_coordinates': list(map(encode, coordinates)),
        'axis': serialize(e), 'complement': serialize(complement),
        'axis_momentum_count': len(momenta),
        'standard_sqrt2_A2_planes': lattice_planes,
        'residual_eigenvalues': eigenrecords,
        'axis_action_columns': [[encode(c) for c in column] for column in action],
        'rational_subVOA_proved': 'Unitary Vir(4/5)=L(4/5,0). A weight3 Potts extension is not asserted unless separately verified.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), Path(x.__file__), Path(g3.__file__),
                                    Path('hi_cft_20260923_next_81top_exact.py'),
                                    Path('hi_cft_20260923_next_structure_core_extension.py'),
                                    Path('hi_cft_20260923_next_structure_residual_tensor.py'),
                                    *sources)}}
    path = Path('hi_cft_20260923_next_structure_residual_potts_verify.json')
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    summary = {k: v for k, v in result.items() if k not in
               ('axis', 'complement', 'axis_action_columns', 'source_sha256',
                'residual_eigenvalues')}
    summary['residual_eigenvalues'] = [{k: v for k, v in row.items() if k != 'basis'}
                                      for row in eigenrecords]
    print(summary, flush=True)


if __name__ == '__main__':
    main()
