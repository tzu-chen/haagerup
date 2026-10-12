"""Bounded exact central-charge elimination for residual idempotents.

Root-only safe_run job, <=2 GiB AS, <=300 s. Five quadratic equations
in five variables over a quartic number field; when zero dimensional,
Bezout bounds the quotient length by32. Use multiplication by c on the
standard-monomial quotient; no FGLM inversion. Expected ordinary RSS <1 GiB, but growth
requires the hard cap and alarm. No workers or numerical optimizers.
"""

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    assert 0 < args.seconds <= 300
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    started = monotonic()
    import sympy as sp

    source = Path('hi_cft_20260923_next_structure_residual_tensor.json')
    data = json.loads(source.read_text())
    assert data['exact_dimension'] == 5 and data['exact_closure_verified']
    roots = (sp.Integer(1), sp.sqrt(13), sp.sqrt(-3), sp.sqrt(-39))
    decode = lambda row: sum(sp.Rational(a)*b for a, b in zip(row, roots))
    tensor = [[[decode(v) for v in row] for row in plane] for plane in data['product']]
    assert list(map(decode, data['central_linear_half'])) == [sp.Rational(16, 19), sp.Rational(91, 95), 0, 0, 0]
    a, t0, t1, t2, c = sp.symbols('a t0 t1 t2 c')
    variables = (a, t0, t1, t2, c)
    coords = (a, (95*c/2-80*a)/91, t0, t1, t2)
    field = sp.QQ.algebraic_field(sp.sqrt(13), sp.sqrt(-3))
    equations = [sp.Poly(sum(tensor[k][i][j]*coords[i]*coords[j]
                              for i in range(5) for j in range(5))-2*coords[k],
                         *variables, domain=field) for k in range(5)]
    assert all(p.total_degree() == 2 and len(p.terms()) <= 21 for p in equations)
    print({'stage': 'input_ready', 'seconds': monotonic()-started}, flush=True)
    basis = sp.groebner(equations, *variables, domain=field,
                        order='grevlex', method='buchberger')
    zero_dimensional = basis.is_zero_dimensional
    print({'stage': 'grevlex_complete', 'basis_size': len(basis.polys),
           'zero_dimensional': zero_dimensional,
           'seconds': monotonic()-started}, flush=True)
    standard, central_polynomials, factorizations, rational_roots = [], [], [], set()
    multiplication_rows = None
    if zero_dimensional:
        leading = [p.LM(order=basis.order).exponents for p in basis.polys]
        pending, visited = deque([(0,)*5]), {(0,)*5}
        while pending:
            monomial = pending.popleft()
            if any(all(a >= b for a, b in zip(monomial, lead)) for lead in leading):
                continue
            standard.append(monomial)
            assert len(standard) <= 32, 'Unexpected quotient length beyond quadratic Bezout bound'
            for i in range(5):
                nxt = tuple(v+int(j == i) for j, v in enumerate(monomial))
                if nxt not in visited:
                    visited.add(nxt)
                    pending.append(nxt)
        from sympy.polys.matrices import DomainMatrix
        index = {monomial: i for i, monomial in enumerate(standard)}
        rows = [[field.zero]*len(standard) for _ in standard]
        for j, monomial in enumerate(standard):
            expression = c*sp.prod(v**n for v, n in zip(variables, monomial))
            remainder = sp.Poly(basis.reduce(expression)[1], *variables, domain=field)
            for powers, coefficient in remainder.rep.to_dict().items():
                assert powers in index
                rows[index[powers]][j] = coefficient
        matrix = DomainMatrix(rows, (len(standard), len(standard)), field)
        print({'stage': 'multiplication_matrix_ready', 'dimension': len(standard),
               'seconds': monotonic()-started}, flush=True)
        coefficients = matrix.charpoly()
        characteristic = sp.Poly.from_list(coefficients, c, domain=field)
        assert basis.reduce(characteristic.as_expr())[1] == 0
        central_polynomials = [characteristic]
        multiplication_rows = [[str(field.to_sympy(v)) for v in row] for row in rows]
        for p in central_polynomials:
            scalar, factors = sp.factor_list(p)
            factorizations.append({'scalar': str(scalar),
                                   'factors': [{'polynomial': str(f.as_expr()), 'multiplicity': m}
                                               for f, m in factors]})
            for f, _ in factors:
                if f.degree() == 1:
                    root = sp.simplify(-f.nth(0)/f.nth(1))
                    if root.is_Rational:
                        rational_roots.add(root)
    result = {
        'sympy_version': sp.__version__,
        'coefficient_field': 'Q(sqrt(13),sqrt(-3))',
        'variables': list(map(str, variables)),
        'input_equations': [str(p.as_expr()) for p in equations],
        'grevlex_basis': [str(p.as_expr()) for p in basis.polys],
        'zero_dimensional': zero_dimensional,
        'quotient_length': len(standard) if zero_dimensional else None,
        'standard_monomials': standard,
        'central_multiplication_matrix': multiplication_rows,
        'central_polynomials': [str(p.as_expr()) for p in central_polynomials],
        'central_factorizations': factorizations,
        'rational_central_roots': list(map(str, sorted(rational_roots))),
        'scope': 'The multiplication characteristic polynomial has exactly all complex idempotent central charges as roots when zero dimensional, with scheme multiplicity. '
                 'A real central root does not by itself establish a PCT-fixed axis or a rational frame.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), source)}}
    path = Path('hi_cft_20260923_next_structure_residual_all_charges_v2.json')
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print({k: v for k, v in result.items() if k not in
           ('input_equations', 'grevlex_basis', 'central_multiplication_matrix', 'standard_monomials', 'source_sha256')}, flush=True)


if __name__ == '__main__':
    main()
