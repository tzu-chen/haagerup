"""Exact target-charge idempotents in the full 5D residual algebra.

Root-only job through safe_run, <=2 GiB AS, <=300 seconds. This consumes
only a 5x5x5 tensor: five quadratics in four variables over a quartic
number field after eliminating the central-charge linear equation.
Estimated ordinary usage <1 GiB; Groebner intermediate growth is not
predictable, so the AS cap and alarm are mandatory. No ambient lattice
basis, numerical optimizer, multiprocessing, or detached work.

A unit Groebner basis proves absence of all complex idempotents at the
target charge. A non-unit basis records exact constraints, not a claim
of a unitary Virasoro frame or rational commutant.
"""

import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--central', default='4/5')
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--output', default=
                        'hi_cft_20260923_next_structure_residual_potts.json')
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    assert 0 < args.seconds <= 300
    path = Path(args.output)
    assert not path.exists()
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    started = monotonic()
    import sympy as sp

    source = Path('hi_cft_20260923_next_structure_residual_tensor.json')
    data = json.loads(source.read_text())
    assert data['exact_dimension'] == 5 and data['exact_closure_verified']
    roots = (sp.Integer(1), sp.sqrt(13), sp.sqrt(-3), sp.sqrt(-39))
    decode = lambda c: sum(sp.Rational(a)*b for a, b in zip(c, roots))
    tensor = [[[decode(c) for c in row] for row in plane]
              for plane in data['product']]
    central_half = list(map(decode, data['central_linear_half']))
    assert central_half == [sp.Rational(16, 19), sp.Rational(91, 95), 0, 0, 0]
    assert list(map(decode, data['total'])) == [1, 1, 0, 0, 0]
    central = sp.Rational(args.central)
    assert 0 < central < sp.Rational(18, 5)
    a, t0, t1, t2 = sp.symbols('a t0 t1 t2')
    variables = (a, t0, t1, t2)
    b = (95*central/2-80*a)/91
    coordinates = (a, b, t0, t1, t2)
    assert sp.expand(2*sum(c*v for c, v in zip(central_half, coordinates))-central) == 0
    field = sp.QQ.algebraic_field(sp.sqrt(13), sp.sqrt(-3))
    equations = [sp.Poly(sum(tensor[k][i][j]*coordinates[i]*coordinates[j]
                              for i in range(5) for j in range(5))-2*coordinates[k],
                         *variables, domain=field) for k in range(5)]
    assert all(p.total_degree() <= 2 and len(p.terms()) <= 15 for p in equations)
    print({'target_central_charge': str(central),
           'variables': len(variables), 'quadratics': len(equations),
           'field_degree': field.mod.degree(),
           'seconds_before_Groebner': monotonic()-started}, flush=True)
    basis = sp.groebner(equations, *variables, domain=field,
                        order='grevlex', method='buchberger')
    excluded = len(basis.polys) == 1 and basis.polys[0].total_degree() == 0
    assert all(basis.reduce(p.as_expr())[1] == 0 for p in equations)
    result = {
        'target_central_charge': str(central),
        'sympy_version': sp.__version__,
        'coefficient_field': 'Q(sqrt(13),sqrt(-3))',
        'eliminated_coordinate_b': str(b),
        'variables': list(map(str, variables)),
        'input_equations': [str(p.as_expr()) for p in equations],
        'Groebner_order': 'grevlex', 'Groebner_method': 'buchberger',
        'Groebner_basis': [str(p.as_expr()) for p in basis.polys],
        'Groebner_basis_size': len(basis.polys),
        'Groebner_total_terms': sum(len(p.terms()) for p in basis.polys),
        'exact_complex_axis_exclusion': excluded,
        'zero_dimensional_nonempty_ideal': not excluded and basis.is_zero_dimensional,
        'scope': 'Exact target-charge idempotent ideal in the full residual Griess algebra. '
                 'A non-unit ideal alone does not assert unitary axes or a rational VOA frame.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), source)}}
    path.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print({k: v for k, v in result.items() if k not in
           ('input_equations', 'Groebner_basis', 'source_sha256')}, flush=True)


if __name__ == '__main__':
    main()
