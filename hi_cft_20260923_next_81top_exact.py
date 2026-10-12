"""Exact 81-dimensional mixed-sector top irreducibility certificates.

Run ONLY through hi_cft_safe_run.py, with --limit-mib 2048 and a 300 s
outer timeout. No ambient oscillator basis or dense commutant is built.
This finite certificate becomes a full restriction result only after an
independent theorem excludes simple U tops of weight >=2.
"""
import argparse
from collections import Counter, deque
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x


SOURCE = Path('hi_cft_20260923_c8_exact_fields.json')
PCT_CERT = Path('hi_cft_20260923_c8_exact_unitary_certificate.json')
TORUS = (5, 8, 9, 8, 5, 1, 2, 2)


class BudgetStop(Exception):
    pass


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    bt = transpose(b)
    return [[sum(u * v for u, v in zip(row, col)) for col in bt]
            for row in a]


def integers(a):
    assert all(Q(v).denominator == 1 for row in a for v in row)
    return [[int(v) for v in row] for row in a]


def sector_setup(glue_sign, sector_sign):
    """Both isotropic lines in D(E6+A2), in a gauge extending old fields."""
    inverse = x.inverse(x.G)
    lam = tuple(inverse[i][0] + glue_sign * inverse[i][6] for i in range(8))
    assert x.norm(lam) == 2
    m = [[Q(i == j) for j in range(8)] for i in range(8)]
    m[7] = list(lam)
    n = integers(x.inverse(m))
    gram = integers(multiply(multiply(m, x.G), transpose(m)))
    lower = [[gram[i][j] if i > j else gram[i][i] // 2 if i == j else 0
              for j in range(8)] for i in range(8)]
    old = [[x.G[i][j] if i > j else int(i == j) for j in range(8)]
           for i in range(8)]
    defect0 = multiply(multiply(n, lower), transpose(n))
    defect = [[defect0[i][j] - old[i][j] for j in range(8)] for i in range(8)]
    assert all((defect[i][j] - defect[j][i]) % 2 == 0
               for i in range(8) for j in range(8))

    @lru_cache(maxsize=2048)
    def coordinates(a):
        z = tuple(sum(a[i] * n[i][j] for i in range(8)) for j in range(8))
        assert all(Q(v).denominator == 1 for v in z)
        return tuple(int(v) for v in z)

    @lru_cache(maxsize=2048)
    def gauge(a):
        assert all(Q(v).denominator == 1 for v in a)
        a = tuple(int(v) for v in a)
        p = sum(defect[i][i] * a[i] * (a[i] - 1) // 2 for i in range(8))
        p += sum(defect[i][j] * a[i] * a[j]
                 for i in range(8) for j in range(i + 1, 8))
        return -1 if p % 2 else 1

    def epsilon(a, b):
        aa, bb = coordinates(a), coordinates(b)
        p = sum(aa[i] * lower[i][j] * bb[j]
                for i in range(8) for j in range(i + 1))
        return -1 if p % 2 else 1

    # Gauge identity on lattice generators implies it on the whole old
    # lattice: both cocycles are bimultiplicative and gauge is quadratic.
    for a in x.SIMPLE:
        for b in x.SIMPLE:
            assert gauge(a) * gauge(b) * epsilon(a, b) == x.cocycle(a, b) * gauge(x.plus(a, b))
    initial = tuple(sector_sign * v for v in lam)
    roots, todo = {initial}, [initial]
    while todo:
        a = todo.pop()
        for i in range(8):
            b = list(a)
            b[i] -= x.dot(a, x.SIMPLE[i])
            b = tuple(b)
            if b not in roots:
                roots.add(b)
                todo.append(b)
                assert len(roots) <= 81
    roots = sorted(roots)
    assert len(roots) == 81 and all(x.norm(a) == 2 for a in roots)
    metric = []
    for a in roots:
        exponents = tuple(a[i] - initial[i] for i in range(8))
        assert all(v.denominator == 1 for v in exponents)
        d = Q(1)
        for c, exponent in zip(TORUS, exponents):
            d *= Q(c) ** int(exponent)
        assert d > 0
        metric.append(d)
    return roots, metric, gauge, epsilon


def pct(v):
    out = {}
    for (alpha, osc), c in v.items():
        factor = Q((-1) ** len(osc))
        for t, exponent in zip(TORUS, alpha):
            factor *= Q(t) ** exponent
        out[(tuple(-a for a in alpha), osc)] = c.conj(2) * factor
    return out


def matrix(field, roots, gauge, epsilon):
    """Sparse columns of o(field), on root states with no oscillators.

    Direct normal-order formulas: h_i(-1)h_j(-1) -> beta_i beta_j;
    h_i(-2) -> -beta_i; h_i(-1)e^alpha -> beta_i e^alpha.
    Nonzero momentum terms can contribute only if alpha+beta is a
    root in this same coset. All other modes leave ambient grade one.
    """
    lookup = {a: i for i, a in enumerate(roots)}
    weights = {x.grade(s) for s in field}
    assert len(weights) == 1 and next(iter(weights)) in (1, 2)
    result = []
    for j, beta in enumerate(roots):
        beta_pairings = tuple(x.dot(s, beta) for s in x.SIMPLE)
        col = {}
        for (alpha, osc), c in field.items():
            if alpha == x.ZERO:
                dest = j
                if len(osc) == 2:
                    assert all(i < 8 for i in osc)
                    factor = beta_pairings[osc[0]] * beta_pairings[osc[1]]
                else:
                    assert len(osc) == 1 and osc[0] < 16
                    factor = (-1 if osc[0] >= 8 else 1) * beta_pairings[osc[0] % 8]
            else:
                dest = lookup.get(x.plus(alpha, beta))
                if dest is None:
                    continue
                assert len(osc) <= 1 and (not osc or osc[0] < 8)
                factor = gauge(alpha) * epsilon(alpha, beta)
                if osc:
                    factor *= beta_pairings[osc[0]]
            x.add(col, dest, c * factor)
        if any(coefficient_bits(c) > 2048 for c in col.values()):
            raise BudgetStop('operator coefficient bit cap 2048')
        result.append(col)
    return result


def check_adjoint(a, b, metric):
    support_a = {(i, j) for j, col in enumerate(a) for i in col}
    support_b = {(j, i) for j, col in enumerate(b) for i in col}
    assert support_a == support_b, 'adjoint support'
    for j, col in enumerate(a):
        for i, c in col.items():
            assert b[i][j] == c.conj(2) * (metric[i] / metric[j]), 'weighted adjoint'


def apply(a, v):
    out = {}
    for j, c in v.items():
        for i, b in a[j].items():
            x.add(out, i, b * c)
    return out


def pack_coefficient(c):
    return [str(v) for v in c]


def coefficient_bits(c):
    return max(max(abs(v.numerator).bit_length(), v.denominator.bit_length()) for v in c)


class Span:
    def __init__(self, weights):
        self.weights, self.blocks, self.rows, self.recipes = weights, {}, [], []

    def add(self, vector, recipe):
        if not vector:
            return None
        w = {self.weights[i] for i in vector}
        assert len(w) == 1, 'operator is not Cartan homogeneous'
        w = next(iter(w))
        block = self.blocks.setdefault(w, {})
        out, reductions = vector.copy(), []
        for p, row_id in sorted(block.items()):
            if p in out:
                c = out[p]
                reductions.append([row_id, pack_coefficient(c)])
                for i, a in self.rows[row_id].items():
                    x.add(out, i, -c * a)
        if not out:
            return None
        p = min(out)
        scale = out[p].inv()
        out = {i: c * scale for i, c in out.items()}
        if max(coefficient_bits(c) for c in out.values()) > 2048:
            raise BudgetStop('coefficient bit cap 2048')
        row_id = len(self.rows)
        assert row_id < 81
        self.rows.append(out)
        self.recipes.append({'input': recipe, 'reductions': reductions,
                             'scale': pack_coefficient(scale), 'weight': list(w)})
        block[p] = row_id
        return row_id


def matrix_digest(a):
    h = hashlib.sha256()
    for j, col in enumerate(a):
        for i, c in sorted(col.items()):
            h.update(json.dumps([i, j, pack_coefficient(c)], separators=(',', ':')).encode())
            h.update(b'\n')
    return h.hexdigest()


def atomic_write(path, data):
    temp = path.with_name(path.name + '.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True)
    ap.add_argument('--seconds', type=int, default=280)
    ap.add_argument('--sector', choices=('++', '+-', '-+', '--', 'all'), default='++')
    args = ap.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2 * 1024**3
    assert 1 <= args.seconds <= 290
    path = Path(args.output)
    assert not path.exists(), 'output must be new'
    started = monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(BudgetStop('time cap')))
    signal.alarm(args.seconds)
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, lambda *_: (_ for _ in ()).throw(BudgetStop('external stop')))
    sources = {str(p): sha(p) for p in (Path(__file__), Path(x.__file__), SOURCE, PCT_CERT)}
    out = {'format': 'exact-mixed-top-v1', 'sources': sources, 'sectors': [],
           'status': 'running', 'arithmetic': 'Q(sqrt(13),sqrt(-3))',
           'scope': 'Exact finite top-space irreducibility only. Full module restriction requires independently proved h<2.'}
    atomic_write(path, out)
    try:
        certificate = json.loads(PCT_CERT.read_text())
        assert certificate['exact_PCT_preservation']
        assert certificate['source_sha256'][str(SOURCE)] == sources[str(SOURCE)]
        assert certificate['source_sha256'][str(Path(x.__file__))] == sources[str(Path(x.__file__))]
        data = json.loads(SOURCE.read_text())
        fields = [('K%d' % i, f) for i, f in enumerate(x.LEFT + x.RIGHT)]
        fields += [('field%d' % i, x.read_field(row)) for i, row in enumerate(data['fields'])]
        cases = [(g, s) for g in (1, -1) for s in (1, -1)] if args.sector == 'all' else [
            (1 if args.sector[0] == '+' else -1, 1 if args.sector[1] == '+' else -1)]
        for glue, sector in cases:
            roots, metric, gauge, epsilon = sector_setup(glue, sector)
            weights = [tuple(int(v) for v in x.weight((a, ()))) for a in roots]
            assert all(tuple(x.weight((a, ()))) == w for a, w in zip(roots, weights))
            counts = Counter(weights)
            operators, op_records = [], []
            for name, field in fields:
                weight = next(iter({x.grade(s) for s in field}))
                a = matrix(field, roots, gauge, epsilon)
                adjoint_field = x.vadd(((-1) ** weight, pct(field)))
                b = matrix(adjoint_field, roots, gauge, epsilon)
                check_adjoint(a, b, metric)
                for label, mat in ((name, a), ('adjoint:' + name, b)):
                    operators.append(mat)
                    op_records.append({'name': label, 'sha256': matrix_digest(mat),
                                       'nnz': sum(map(len, mat))})
                    if sum(r['nnz'] for r in op_records) > 100000:
                        raise BudgetStop('saved operator sparse-term cap 100000')
            unique = [i for i, w in enumerate(weights) if counts[w] == 1]
            assert unique, 'no unique joint Cartan eigenline; different certificate needed'
            seed = max(unique, key=lambda i: (sum(weights[i]), weights[i]))
            span, todo = Span(weights), deque()
            todo.append(span.add({seed: x.ONE}, {'seed_index': seed}))
            while todo and len(span.rows) < 81:
                parent = todo.popleft()
                for op_id, operator in enumerate(operators):
                    row_id = span.add(apply(operator, span.rows[parent]),
                                      {'parent': parent, 'operator': op_id})
                    if row_id is not None:
                        todo.append(row_id)
                    if len(span.rows) == 81:
                        break
            record = {'glue_sign': glue, 'sector_sign': sector,
                      'roots': [[str(v) for v in a] for a in roots],
                      'metric': list(map(str, metric)),
                      'weight_multiplicities': [[list(w), count] for w, count in sorted(counts.items())],
                      'seed_index': seed, 'seed_weight': list(weights[seed]),
                      'seed_eigenspace_dimension': counts[weights[seed]],
                      'exact_weighted_adjoint_checks': True,
                      'operator_matrices': op_records, 'cyclic_dimension': len(span.rows),
                      'irreducible': len(span.rows) == 81,
                      'rows': [[[i, pack_coefficient(c)] for i, c in sorted(row.items())]
                               for row in span.rows], 'recipes': span.recipes}
            out['sectors'].append(record)
            out['seconds'] = monotonic() - started
            out['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            atomic_write(path, out)
            print(json.dumps({k: record[k] for k in ('glue_sign', 'sector_sign', 'cyclic_dimension', 'irreducible')}), flush=True)
            x.dot.cache_clear()
        out['status'] = 'complete'
    except BudgetStop as exc:
        out['status'], out['stop_reason'] = 'bounded_stop', str(exc)
    finally:
        signal.alarm(0)
        out['seconds'] = monotonic() - started
        out['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        atomic_write(path, out)
    print(json.dumps({'status': out['status'], 'seconds': out['seconds'], 'peak_rss_KiB': out['peak_rss_KiB']}), flush=True)


if __name__ == '__main__':
    main()
