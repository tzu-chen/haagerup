"""Exact normalized three-point seeds for all113 weight-two Virasoro primaries.

Run serially through hi_cft_safe_run.py --limit-mib 1024. Reviewed memory:
113 fields (<24000 sparse terms), one grade-two product at a time, reduced
mode caches; expected <0.3GiB, RSS refusal512MiB, internal timeout900s.
This exports the highest-first slice: all13 highest fields against
all113 components, with every charge-compatible primary target. It does
not claim to supply nonvacuum full-CFT sewing constants.
"""
import argparse
import csv
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
from time import monotonic

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'c8_reviewability_20260927'))
import hi_cft_20260923_c8_exact as x
import check_readable_inputs as independent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def boundary():
    need(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 512 * 1024,
         '512MiB internal RSS boundary')


def inner(a, b):
    return x.A(independent.inner(
        {s: independent.K(c) for s, c in a.items()},
        {s: independent.K(c) for s, c in b.items()}))


def positive_real(a):
    need(a[2:] == (0, 0), 'not real in specified embedding')
    r, s = a[:2]
    if s == 0:
        return r > 0
    if r >= 0 and s > 0:
        return True
    if r <= 0 and s < 0:
        return False
    return (13*s*s > r*r) if s > 0 else (r*r > 13*s*s)


def pack(v):
    need(len(v) <= 2000, 'individual vector support cap')
    return [{'momentum': list(a), 'oscillators': list(o),
             'coefficient': list(map(str, c))} for (a, o), c in sorted(v.items())]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'c8_physics_20260927/full_weight_two')
    args = parser.parse_args()
    need(0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3, 'use guarded1GiB run')
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('900s cap')))
    signal.alarm(900)
    started = monotonic()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    names = ['low_weight_couplings.json', 'low_weight_couplings.tsv',
             'low_weight_basis.json', 'low_weight_products.jsonl', 'stress_couplings.tsv']
    need(all(not (args.output_dir / n).exists() for n in names), 'fresh outputs required')
    for name, cap in [('dot', 6000), ('cocycle', 6000), ('vertex', 4000),
                      ('basis_mode', 6000), ('creation', 512)]:
        function = getattr(x, name)
        setattr(x, name, lru_cache(maxsize=cap)(function.__wrapped__))
    source = ROOT / 'hi_cft_20260923_c8_exact_fields.json'
    need(source.stat().st_size < 1024**2, 'source size cap')
    doc = json.loads(source.read_text())
    primaries = doc['fields'][:8]
    omega = x.omega()
    e = x.read_field(doc['fields'][8])
    wl, wr = x.sugawara(x.LEFT, 1), x.sugawara(x.RIGHT, 39)
    f = x.vadd((1, omega), (-1, wl), (-1, wr), (-1, e))
    central = [Q(1), Q(117,41), Q(2400,1271), Q(70,31)]
    cl, cr, ce, cf = central
    current_highs = [([1,5], x.mode(x.RIGHT[1],-1,x.RIGHT[1])),
                     ([3,3], x.mode(x.LEFT[1],-1,x.RIGHT[1]))]
    stress_highs = [([1,1],x.vadd((cr,wl),(-cl,wr))),
                    ([1,1],x.vadd((ce,wl),(ce,wr),(-cl-cr,e))),
                    ([1,1],x.vadd((cf,wl),(cf,wr),(cf,e),(-cl-cr-ce,f)))]
    all_highs = [(r['dimensions'],x.read_field(r)) for r in primaries]+current_highs+stress_highs
    fields, descriptors, highest_indices = [], [], []
    for multiplet, (dimensions, high) in enumerate(all_highs):
        n, m = dimensions
        highest_indices.append(len(fields))
        components = x.descendants(high, n, m)
        need(len(components) == n*m, 'component count')
        for j, v in enumerate(components):
            weight = (n-1-2*(j//m), m-1-2*(j % m))
            need(all(x.weight(state) == weight and x.grade(state) == 2 for state in v),
                 'current charge or conformal weight')
            need(not x.mode(omega, 2, v) and not x.mode(omega, 3, v), 'Virasoro primary')
            norm = inner(v, v)
            need(positive_real(norm), 'nonpositive exact norm')
            fields.append(v)
            descriptors.append({'index': len(fields)-1, 'name': f'v{multiplet}_{j//m}_{j % m}',
                'multiplet': multiplet, 'current_dimensions': [n, m],
                'lowering_powers': [j//m, j % m], 'Cartan_weight': list(weight),
                'norm_squared': list(map(str, norm)), 'field': pack(v)})
        boundary()
    need(len(fields) == 113 and sum(map(len, fields)) < 24000, 'basis size cap')
    # Distinct e-eigenvalues distinguish the two copies of (1,9).
    # We verify their orthogonality directly instead of inferring it.
    by_weight = {}
    for i, row in enumerate(descriptors):
        by_weight.setdefault(tuple(row['Cartan_weight']), []).append(i)
    gram_checks = 0
    for group in by_weight.values():
        for j, i in enumerate(group):
            for k in group[j+1:]:
                need(not inner(fields[i], fields[k]), 'off-diagonal Gram entry')
                gram_checks += 1
    basis_doc = {'format': 'complete-weight-two-primary-basis-v1',
        'convention': 'F_L^p F_R^q applied to saved highest fields; no factorial division',
        'hermitian_pairing': 'antilinear first slot; transported lattice gauge',
        'normalization': 'v_hat=v/sqrt(norm_squared), positive square root',
        'additional_highest_fields': ['E_R(-1)E_R','E_L(-1)E_R',
             'c_R omega_L-c_L omega_R','c_e(omega_L+omega_R)-(c_L+c_R)e',
             'c_f(omega_L+omega_R+e)-(c_L+c_R+c_e)f'],
        'completeness': '113 orthogonal positive-norm Virasoro primaries in U_2, whose primary dimension is120-6-1=113',
        'fields': descriptors}
    with (args.output_dir / names[2]).open('x') as f:
        json.dump(basis_doc, f, indent=2)
        f.write('\n')
    records, products, nonzero = [], 0, 0
    with (args.output_dir / names[3]).open('x') as vectors, \
         (args.output_dir / names[1]).open('x', newline='') as table:
        writer = csv.writer(table, delimiter='\t')
        writer.writerow(['highest', 'second', 'target', 'numerator_q0', 'numerator_qs',
                         'numerator_qt', 'numerator_qst', 'norm_product',
                         'abs_C_squared_q0', 'abs_C_squared_qs',
                         'abs_C_squared_qt', 'abs_C_squared_qst'])
        for highest in highest_indices:
            for second, v in enumerate(fields):
                charge = tuple(a+b for a, b in zip(descriptors[highest]['Cartan_weight'],
                                                   descriptors[second]['Cartan_weight']))
                candidates = by_weight.get(charge, [])
                if not candidates:
                    continue
                product = x.mode(fields[highest], 1, v)
                need(len(product) <= 2000, 'product cap')
                products += 1
                vectors.write(json.dumps({'highest': highest, 'second': second,
                                           'mode': 1, 'vector': pack(product)}) + '\n')
                n1 = x.A(descriptors[highest]['norm_squared'])
                n2 = x.A(descriptors[second]['norm_squared'])
                for target in candidates:
                    value = inner(fields[target], product)
                    nt = x.A(descriptors[target]['norm_squared'])
                    denominator = n1*n2*nt
                    square = value.conj(2)*value/denominator
                    need(not square or positive_real(square), 'negative squared coupling')
                    record = {'highest': highest, 'second': second, 'target': target,
                        'numerator': list(map(str, value)),
                        'norm_product': list(map(str, denominator)),
                        'abs_C_squared': list(map(str, square))}
                    records.append(record)
                    writer.writerow([descriptors[highest]['name'], descriptors[second]['name'],
                                     descriptors[target]['name'], *map(str, value),
                                     json.dumps(record['norm_product']), *map(str, square)])
                    nonzero += bool(value)
                boundary()
            print(json.dumps({'completed_highest': highest, 'products': products,
                              'couplings': len(records), 'nonzero': nonzero}), flush=True)
    # Independently check exact four-stress Ward coefficients on highest fields.
    e = x.read_field(doc['fields'][8])
    wl, wr = x.sugawara(x.LEFT, 1), x.sugawara(x.RIGHT, 39)
    f = x.vadd((1, omega), (-1, wl), (-1, wr), (-1, e))
    axes = [wl, wr, e, f]
    central = [Q(1), Q(117, 41), Q(2400, 1271), Q(70, 31)]
    ward = []
    with (args.output_dir / names[4]).open('x', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['multiplet', 'axis', 'central_charge', 'weight', 'normalized_C_squared'])
        for index, row in enumerate(primaries):
            n, m = row['dimensions']
            weights = [Q(n*n-1, 12), Q(m*m-1, 164), Q(row['e_weight'])]
            weights.append(2-sum(weights))
            high = fields[highest_indices[index]]
            for label, axis, c, h in zip(['affine1', 'affine39', 'coset_e', 'coset_f'],
                                        axes, central, weights):
                need(x.mode(axis, 1, high) == {s: coef*h for s, coef in high.items()} if h else
                     not x.mode(axis, 1, high), 'stress eigenvalue mismatch')
                item = {'multiplet': index, 'axis': label, 'central_charge': str(c),
                        'weight': str(h), 'normalized_C_squared': str(2*h*h/c)}
                ward.append(item)
                writer.writerow(item.values())
    output = {'format': 'highest-first-weight-two-three-point-couplings-v1', 'status': 'pass',
        'arithmetic': 'Q(sqrt13,sqrt-3) with exact Fraction entries',
        'coefficient_convention': 'C_ij^k=<v_k,(v_i)_1 v_j>/sqrt(N_i N_j N_k)',
        'field_basis': '1,s,t,st with s^2=13,t^2=-3; s positive, t=i sqrt3',
        'basis_dimension': 113, 'highest_fields': 13, 'computed_mode_products': products,
        'charge_compatible_couplings': len(records), 'nonzero_couplings': nonzero,
        'off_diagonal_Gram_checks': gram_checks,
        'all_basis_vectors_Virasoro_primary_and_positive_norm': True,
        'all_forbidden_charge_couplings_zero': 'deduced from exact Cartan eigenvalues',
        'normalized_couplings': records, 'stress_Ward_couplings': ward,
        'source_sha256': {str(p.relative_to(ROOT)): sha(p) for p in [source,
            ROOT / 'hi_cft_20260923_c8_exact.py',
            ROOT / 'c8_reviewability_20260927/check_readable_inputs.py', Path(__file__)]},
        'basis_sha256': sha(args.output_dir / names[2]),
        'products_sha256': sha(args.output_dir / names[3]),
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': 'Actual chiral vacuum-module weight-two products and Fock contractions for a complete113-dimensional Virasoro-primary basis. Highest-first slice forWardcompletion; not generic nonvacuum bulk OPE coefficients.'}
    with (args.output_dir / names[0]).open('x') as stream:
        json.dump(output, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: output[k] for k in ('status', 'basis_dimension', 'computed_mode_products',
                     'charge_compatible_couplings', 'nonzero_couplings', 'seconds', 'peak_rss_KiB')}), flush=True)


if __name__ == '__main__':
    main()
