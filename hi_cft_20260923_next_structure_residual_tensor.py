"""Exact five-dimensional ambient residual Griess algebra.

Root-only safe_run job: <=2 GiB AS, 300 seconds, no workers. Estimated
peak <0.5 GiB: five sparse fields, 15 product images, bounded 12000-entry
mode caches, and elimination in dimensions at most five. No NumPy,
SymPy, floating arithmetic, higher-grade basis, or Groebner work.

Besides the complete tensor, test every norm-four rank-one lattice
Ising vector whose momentum can occur in the residual space. Arbitrary
coefficients u,v are allowed, with uv=1/16; this avoids a gauge choice.
An underdetermined family is recorded without claiming an exclusion.
"""

from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
from hi_cft_20260923_next_structure_core_extension import read, serialize


def encode(a):
    return list(map(str, x.A(a)))


def pairing(a, b):
    value = x.mode(a, 3, b)
    assert not set(value)-{(x.ZERO, ())}
    return value.get((x.ZERO, ()), x.ZERO_A)


def coordinate_map(basis):
    pivots = {}
    for i, vector in enumerate(basis):
        out = vector.copy()
        lift = [x.A(i == j) for j in range(len(basis))]
        while out:
            p = min(out)
            if p not in pivots:
                scale = out[p].inv()
                pivots[p] = ({s: c*scale for s, c in out.items()},
                             [c*scale for c in lift])
                break
            row, old = pivots[p]
            factor = out[p]
            out = x.vadd((1, out), (-factor, row))
            lift = [a-factor*b for a, b in zip(lift, old)]
        else:
            raise AssertionError('Dependent tensor basis')

    def coordinates(vector):
        out = vector.copy()
        result = [x.ZERO_A]*len(basis)
        while out:
            p = min(out)
            assert p in pivots, 'Product outside residual space'
            row, lift = pivots[p]
            factor = out[p]
            out = x.vadd((1, out), (-factor, row))
            result = [a+factor*b for a, b in zip(result, lift)]
        assert not x.vadd((1, vector), *[(-c, v) for c, v in zip(result, basis)])
        return result
    return coordinates


def solve_two(columns, target):
    """Solve two scalar unknowns against sparse ambient equations."""
    rows = []
    for state in sorted(set(target).union(*map(set, columns))):
        rows.append([v.get(state, x.ZERO_A) for v in columns]
                    + [target.get(state, x.ZERO_A)])
    rank, pivots = 0, []
    for j in range(2):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][j].inv()
        rows[rank] = [a*scale for a in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][j]:
                factor = rows[i][j]
                rows[i] = [a-factor*b for a, b in zip(rows[i], rows[rank])]
        pivots.append(j)
        rank += 1
    if any(not row[0] and not row[1] and row[2] for row in rows):
        return None
    solution = [x.ZERO_A, x.ZERO_A]
    for i, j in enumerate(pivots):
        solution[j] = rows[i][2]
    return rank, solution


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(300)
    started = monotonic()
    source = Path('hi_cft_20260923_next_residual_ambient2.json')
    axes_source = Path('hi_cft_20260923_proof_remaining_axes.json')
    data, axes = json.loads(source.read_text()), json.loads(axes_source.read_text())
    assert data['exact_residual_commutant_grade2_dimension'] == 5
    assert data['all_basis_vectors_quasiprimary']
    q, r = read(axes['first_stress']), read(axes['second_stress'])
    total = x.vadd((1, q), (1, r))
    assert not pairing(q, r)
    basis, span = [q, r], x.Span()
    for v in basis:
        span.reduce(v, True)
    for raw in map(read, data['basis']):
        if not span.reduce(raw):
            continue
        v = x.vadd((1, raw), (-pairing(raw, q)/pairing(q, q), q),
                   (-pairing(raw, r)/pairing(r, r), r))
        basis.append(v)
        span.reduce(v, True)
    assert len(basis) == span.dimension == 5
    coords = coordinate_map(basis)
    metric = [[pairing(a, b) for b in basis] for a in basis]
    product = [[[x.ZERO_A for _ in basis] for _ in basis] for _ in basis]
    for i, a in enumerate(basis):
        assert not x.mode(x.omega(), 2, a)
        assert not x.vadd((1, x.mode(total, 1, a)), (-2, a))
        for j in range(i, 5):
            b = basis[j]
            assert not x.mode(a, 2, b), 'Residual weight-one product is nonzero'
            image = x.mode(a, 1, b)
            assert image == x.mode(b, 1, a)
            for k, c in enumerate(coords(image)):
                product[k][i][j] = product[k][j][i] = c
    for i in range(5):
        for j in range(5):
            for k in range(5):
                assert sum((product[l][i][j]*metric[l][k] for l in range(5)), x.ZERO_A) == sum(
                    (product[l][j][k]*metric[i][l] for l in range(5)), x.ZERO_A)

    # Orthogonality and invariant pairing make the last three coordinates
    # stable under multiplication by q. Compute its cubic characteristic.
    assert all(not product[k][0][j] for k in (0, 1) for j in range(2, 5))
    matrix = [[product[i][0][j] for j in range(2, 5)] for i in range(2, 5)]
    multiply = lambda a, b: [[sum((a[i][k]*b[k][j] for k in range(3)), x.ZERO_A)
                              for j in range(3)] for i in range(3)]
    square = multiply(matrix, matrix)
    cube = multiply(square, matrix)
    t1, t2, t3 = [sum((m[i][i] for i in range(3)), x.ZERO_A)
                  for m in (matrix, square, cube)]
    cubic = [-(t1*t1*t1-3*t1*t2+2*t3)/6, (t1*t1-t2)/2, -t1, x.ONE]

    core = x.vadd((1, x.omega()), (-1, total))
    momenta = {a for v in basis for a, osc in v if x.norm(a) == 4}
    positive = sorted(a for a in momenta if a < tuple(-n for n in a))
    ising, undetermined = [], []
    for alpha in positive:
        neg = tuple(-a for a in alpha)
        assert neg in momenta
        heis = x.cartan(alpha)
        quad = x.vadd((Q(1, 16), x.mode(heis, -1, heis)))
        ep, em = x.root(alpha), x.root(neg)
        solved = solve_two([x.mode(core, 1, ep), x.mode(core, 1, em)],
                           x.vadd((-1, x.mode(core, 1, quad))))
        if solved is None:
            continue
        rank, (u, v) = solved
        if rank < 2:
            undetermined.append({'momentum': alpha, 'linear_rank': rank})
            continue
        if u*v != x.A(Q(1, 16)):
            continue
        e = x.vadd((1, quad), (u, ep), (v, em))
        assert not x.vadd((1, x.mode(e, 1, e)), (-2, e))
        assert pairing(e, e) == x.A(Q(1, 4))
        ising.append({'momentum': alpha, 'coordinates': list(map(encode, coords(e))),
                      'field': serialize(e)})

    result = {
        'exact_dimension': 5, 'exact_closure_verified': True,
        'basis_description': 'q,r, then three vectors orthogonal to q and r',
        'basis': list(map(serialize, basis)),
        'product': [[[encode(c) for c in row] for row in plane] for plane in product],
        'metric': [[encode(c) for c in row] for row in metric],
        'total': list(map(encode, coords(total))),
        'central_linear_half': [encode(pairing(v, total)) for v in basis],
        'q_peirce_matrix': [[encode(c) for c in row] for row in matrix],
        'q_peirce_cubic_ascending': list(map(encode, cubic)),
        'rank_one_Ising_momentum_pairs_checked': len(positive),
        'rank_one_Ising_axes': ising,
        'rank_one_Ising_underdetermined_cases': undetermined,
        'rank_one_Ising_search_complete': not undetermined,
        'scope': 'Full residual Griess tensor. Rank-one lattice Ising search does not classify all Ising or Potts axes.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), Path(x.__file__), source, axes_source,
                                    Path('hi_cft_20260923_next_structure_core_extension.py'))}}
    path = Path('hi_cft_20260923_next_structure_residual_tensor.json')
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print({k: v for k, v in result.items() if k not in
           ('basis', 'product', 'metric', 'source_sha256', 'rank_one_Ising_axes')}, flush=True)


if __name__ == '__main__':
    main()
