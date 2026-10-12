"""Small exact correlator dataset; root alone runs this through the guard.

Example:
 python hi_cft_safe_run.py --limit-mib 1024 -- python \
   c8_physics_20260927/correlators.py \
   --output c8_physics_20260927/correlators.json

No research engine, array package, mode cache, or ambient basis is imported.
The calculation enumerates six charge orderings of 3^4 vertex choices,
uses rational polynomials of degree at most12, and extracts at most48
global conformal-block coefficients. It reads two bounded frozen JSON
inputs. Expected RSS <80 MiB; internal RSS boundary192 MiB, AS <=1 GiB,
time boundary120 s. No workers or subprocesses. Root must retain the
permanent shared-desktop launcher, reserve, CPU, and serial-job policy.

The output concerns chiral vacuum correlators, plus selected fractional
B-lattice intertwiner blocks. It is not the lightest diagonal-U bulk
four-point function. Potts/PF13 four-point functions use the authenticated
canonical self-OPE and W4 norm, not a new high-grade mode calculation.
"""

import argparse
import csv
from fractions import Fraction as Q
import hashlib
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import resource
import signal
from time import monotonic


ROOT = Path(__file__).resolve().parents[1]
G = [[2 * int(i == j) for j in range(8)] for i in range(8)]
for i, j in ((0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (6, 7)):
    G[i][j] = G[j][i] = -1
GAUGE = (5, 8, 9, 8, 5, 1, 2, 2)
MOMENTA = (
    (0, 0, 0, 0, 0, -1, 1, 1),
    (0, 0, 0, 1, 1, -1, 0, 0),
    (1, 1, 0, 0, 0, -1, 0, 0),
)
SOURCES = (
    'hi_cft_20260923_c8_exact.py',
    'hi_cft_20260923_c8_exact_fields.json',
    'hi_cft_20260923_proof_pf13_ope.json',
    'hi_cft_20260923_proof_pf13_upper_poles.py',
    'hi_cft_20260923_proof_pf13_upper_poles.json',
    'c8_physics_20260927/correlators.py',
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def boundary():
    need(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 192 * 1024,
         '192 MiB internal RSS boundary')


class K(tuple):
    """Exact Q(s,t), s^2=13, t^2=-3, ordered basis [1,s,t,st]."""
    def __new__(cls, value=0):
        if isinstance(value, (tuple, list)):
            need(len(value) == 4, 'four field coordinates')
            return tuple.__new__(cls, map(Q, value))
        return tuple.__new__(cls, (Q(value), Q(0), Q(0), Q(0)))

    def __bool__(self):
        return any(self)

    def __add__(self, other):
        return K([a + b for a, b in zip(self, K(other))])
    __radd__ = __add__

    def __neg__(self):
        return K([-a for a in self])

    def __mul__(self, other):
        a, b, c, d = self
        e, f, g, h = K(other)
        return K([a*e + 13*b*f - 3*c*g - 39*d*h,
                  a*f + b*e - 3*c*h - 3*d*g,
                  a*g + c*e + 13*b*h + 13*d*f,
                  a*h + d*e + b*g + c*f])
    __rmul__ = __mul__

    def conjugate(self):
        a, b, c, d = self
        return K([a, b, -c, -d])


COEFFICIENTS = (K(1), K([0, Q(1, 20), Q(3, 20), 0]),
                K([0, Q(1, 20), Q(-3, 20), 0]))


def rational(value):
    value = K(value)
    need(value[1:] == (0, 0, 0), 'rational scalar expected')
    return value[0]


def dot(a, b):
    return sum(a[i] * G[i][j] * b[j] for i in range(8) for j in range(8))


def add_momenta(*momenta):
    return tuple(sum(p[i] for p in momenta) for i in range(8))


def cocycle(a, b):
    exponent = sum(a[i] * b[i] for i in range(8))
    exponent += sum(a[i] * b[j] * G[i][j] for i in range(8) for j in range(i))
    need(type(exponent) is int, 'integer-lattice cocycle only')
    return -1 if exponent % 2 else 1


def gauge_weight(a):
    answer = Q(1)
    for c, exponent in zip(GAUGE, a):
        answer *= Q(c) ** exponent
    return answer


def trim(p):
    p = list(map(Q, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def plus(*polynomials):
    out = [Q(0)] * max(map(len, polynomials), default=1)
    for p in polynomials:
        for i, value in enumerate(p):
            out[i] += value
    return trim(out)


def multiply(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def one_minus_power(n):
    need(0 <= n <= 16, 'small polynomial degree')
    return [Q((-1)**j * comb(n, j)) for j in range(n+1)]


def monomial_term(coefficient, x_power, one_minus_exponent):
    need(0 <= x_power <= 16, 'small nonnegative monomial exponent')
    return [Q(0)] * x_power + [coefficient * a for a in one_minus_power(one_minus_exponent)]


def substitute_one_minus(p):
    return plus(*[[a * b for b in one_minus_power(i)] for i, a in enumerate(p)])


def reverse_width(p, width):
    need(len(p) <= width+1, 'reciprocal substitution degree')
    return trim(list(reversed(p + [Q(0)] * (width+1-len(p)))))


def value(p, x):
    answer = Q(0)
    for a in reversed(p):
        answer = answer*x + a
    return answer


def series(p, denominator_power, order):
    return [sum(p[j] * comb(denominator_power+n-j-1, denominator_power-1)
                for j in range(min(n, len(p)-1)+1)) for n in range(order+1)]


def global_descendant(h, k):
    """Coefficient of x^k in 2F1(h,h;2h;x), exactly."""
    answer = Q(1)
    for j in range(k):
        answer *= Q((h+j)**2, (2*h+j)*(j+1))
    return answer


def global_blocks(p, denominator_power, order, positive=False, even=False):
    expansion = series(p, denominator_power, order)
    coefficients = [expansion[0]]
    for n in range(1, order+1):
        coefficient = expansion[n] - sum(coefficients[h] * global_descendant(h, n-h)
                                         for h in range(1, n))
        coefficients.append(coefficient)
    for n in range(order+1):
        reconstructed = coefficients[0] if n == 0 else sum(
            coefficients[h] * global_descendant(h, n-h) for h in range(1, n+1))
        need(reconstructed == expansion[n], 'global-block reconstruction')
    if positive:
        need(all(a >= 0 for a in coefficients), 'reflection-positive channel coefficients')
    if even:
        need(all(a == 0 for n, a in enumerate(coefficients) if n % 2),
             'identical bosons have no odd-weight global primary exchange')
    return {'convention': 'x^(2h_external) G(x)=A0+sum_n>=1 A_n*x^n*2F1(n,n;2n;x)',
            'order': order, 'reduced_series': list(map(str, expansion)),
            'global_primary_squared_coupling_sums': list(map(str, coefficients)),
            'positivity_checked_through_order': order if positive else None,
            'odd_weights_vanish_checked': even}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024**2), b''):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(name):
    path = ROOT / name
    need(path.stat().st_size <= 4 * 1024**2, '4 MiB source JSON cap')
    result = json.loads(path.read_text())
    boundary()
    return result


def u_correlators(order):
    source = read_json('hi_cft_20260923_c8_exact_fields.json')
    saved = source['fields'][-2]['coefficients']
    reconstructed = {(tuple(row['momentum']), tuple(row['oscillators'])):
                     K(row['Qsqrt13_sqrtminus3'][0] + row['Qsqrt13_sqrtminus3'][1])
                     for row in saved}
    need(reconstructed == {(a, ()): c for a, c in zip(MOMENTA, COEFFICIENTS)},
         'displayed u agrees with frozen exact field')
    gram = [[dot(a, b) for b in MOMENTA] for a in MOMENTA]
    need(gram == [[4 if i == j else 2 for j in range(3)] for i in range(3)],
         'three-momentum Gram matrix')
    contributions = [rational(c.conjugate()*c*gauge_weight(a))
                     for a, c in zip(MOMENTA, COEFFICIENTS)]
    norm = sum(contributions)
    need(contributions == [4, 4, 4] and norm == 12, 'transported u norm')
    all_terms, channels = [], {}
    for positive_positions in combinations(range(4), 2):
        signs = [1 if i in positive_positions else -1 for i in range(4)]
        name = ''.join('p' if s == 1 else 'm' for s in signs)
        p, surviving = [Q(0)], 0
        for choice in product(range(3), repeat=4):
            momenta = [tuple(signs[j]*a for a in MOMENTA[choice[j]]) for j in range(4)]
            coefficient = K(1)
            phase, cumulative = 1, (0,)*8
            for j, i in enumerate(choice):
                c = COEFFICIENTS[i]
                if signs[j] == -1:
                    c = c.conjugate() * gauge_weight(MOMENTA[i])
                coefficient *= c
                phase *= cocycle(cumulative, momenta[j])
                cumulative = add_momenta(cumulative, momenta[j])
            coefficient *= Q(phase, norm*norm)
            balanced = cumulative == (0,)*8
            xp, yp = dot(momenta[2], momenta[3]), dot(momenta[1], momenta[2])
            term = {'ordering': name, 'vertex_choices': list(choice),
                    'total_momentum': list(cumulative), 'charge_conserving': balanced,
                    'cocycle_phase': phase, 'coefficient_before_charge_delta': list(map(str, coefficient)),
                    'x_power': xp, 'one_minus_x_power': yp}
            all_terms.append(term)
            if balanced:
                surviving += 1
                scalar = rational(coefficient)
                need(scalar == Q(1, 9), 'surviving phase/gauge cancellation')
                p = plus(p, monomial_term(scalar, xp+4, yp+4))
        need(surviving == 15, 'fifteen neutral choices out of81')
        channels[name] = {'signs_at_infinity_1_x_0': signs,
                          'evaluated_terms': 81, 'surviving_terms': surviving,
                          'numerator': list(map(str, p)),
                          'denominator': 'x^4*(1-x)^4'}
    neutral = list(map(Q, channels['mpmp']['numerator']))
    charged = list(map(Q, channels['mmpp']['numerator']))
    need(neutral == [Q(1), Q(-4, 3), Q(4, 3)], 'closed neutral four-point function')
    need(charged == [Q(0)]*6 + [Q(4, 3), Q(-4, 3), Q(1)],
         'closed equal-charge four-point function')
    need(substitute_one_minus(neutral) == neutral, 'neutral x<->1-x crossing')
    need(reverse_width(neutral, 8) == charged, 'charged/neutral x<->1/x crossing')
    need(substitute_one_minus(charged) == list(map(Q, channels['mppm']['numerator'])),
         'third ordering by crossing')
    for name, channel in channels.items():
        conjugate_name = ''.join('m' if c == 'p' else 'p' for c in name)
        need(channel['numerator'] == channels[conjugate_name]['numerator'], 'PCT conjugate ordering')
    channels['mpmp']['global_blocks'] = global_blocks(neutral, 4, order, positive=True)
    channels['mmpp']['global_blocks'] = global_blocks(charged, 4, order, positive=True, even=True)
    aa = list(map(Q, channels['mpmp']['global_blocks']['global_primary_squared_coupling_sums']))
    need(aa[:5] == [1, Q(8, 3), Q(14, 3), Q(58, 9), Q(107, 15)],
         'first neutral global coefficients')
    bb = list(map(Q, channels['mmpp']['global_blocks']['global_primary_squared_coupling_sums']))
    need(bb[6] == Q(4, 3) and bb[8] == Q(19, 13), 'first charged global coefficients')
    leading = {}
    for i, j in product(range(3), repeat=2):
        if i == j:
            continue
        momentum = add_momenta(MOMENTA[i], MOMENTA[j])
        coefficient = COEFFICIENTS[i]*COEFFICIENTS[j]*Q(cocycle(MOMENTA[i], MOMENTA[j]), norm)
        leading[momentum] = leading.get(momentum, K(0)) + coefficient
    leading_norm = sum(rational(c.conjugate()*c*gauge_weight(a)) for a, c in leading.items())
    need(len(leading) == 3 and all(dot(a, a) == 12 for a in leading), 'weight-six charged primary')
    need(leading_norm == Q(4, 3), 'leading charged OPE vector norm')
    stresses = [
        ('affine_left', Q(1), Q(1, 4)),
        ('affine_right', Q(117, 41), Q(195, 164)),
        ('e', Q(2400, 1271), Q(180, 1271)),
        ('f', Q(70, 31), Q(13, 31)),
    ]
    need(sum(c for _, c, _ in stresses) == 8 and sum(h for _, _, h in stresses) == 2,
         'orthogonal stress and weight sums')
    stress_sum = sum(2*h*h/c for _, c, h in stresses)
    need(stress_sum >= 1 and aa[2] >= stress_sum, 'positive orthogonal stress projections')
    return {
        'external_field': 'u_hat=u/sqrt(12), weight2; m=theta_g(u_hat), p=u_hat',
        'momenta': list(map(list, MOMENTA)), 'momentum_gram': gram,
        'gauge_weights': list(map(lambda a: str(gauge_weight(a)), MOMENTA)),
        'unnormalized_coefficients': [list(map(str, c)) for c in COEFFICIENTS],
        'norm_contributions': list(map(str, contributions)), 'norm_squared': str(norm),
        'channels': channels, 'terms': all_terms,
        'neutral_closed_form': '(3-4*x+4*x^2)/(3*x^4*(1-x)^4)',
        'charged_closed_form': 'x^2*(4-4*x+3*x^2)/(3*(1-x)^4)',
        'current_exchange': {'charges_HL_HR': [1, 13], 'current_norms_squared': [2, 78],
                             'normalized_current_squared_couplings': ['1/2', '13/6'],
                             'sum': '8/3'},
        'global_weight2': {'total': '14/3', 'normalized_total_stress': '1',
                           'other_Virasoro_primary_total': '11/3',
                           'four_orthogonal_stress_total': str(stress_sum),
                           'orthogonal_to_four_stresses_total': str(aa[2]-stress_sum)},
        'stress_three_point_squared_couplings': [
            {'stress': name, 'central_charge': str(c), 'u_weight': str(h),
             'squared_coupling_to_unit_stress': str(2*h*h/c)} for name, c, h in stresses],
        'charged_leading_primary': {'weight': 6, 'norm_squared': str(leading_norm),
            'normalized_OPE_squared_coefficient': str(leading_norm),
            'vector': [{'momentum': list(a), 'coefficient': list(map(str, c))}
                       for a, c in sorted(leading.items())]},
        'scope': 'Chiral vacuum correlators in U; not correlators of its h=1/3 module.'}


def w3_correlator(name, c, lam, source, order):
    norm = c/3
    a0 = 31-16*lam*(2+c)
    bnorm = norm*a0
    need(rational(source['a0']) == a0 and rational(source['lambda']) == lam,
         name + ' authenticated first-row invariants')
    need(rational(source['W4_norm']) == bnorm, name + ' authenticated W4 norm')
    # Principal part at x=0, followed by the identical part at1-x and the
    # constant at infinity. Coefficients are already divided by norm^2.
    poles = {6: Q(1), 4: 2*c/norm**2, 3: 2*c/norm**2,
             2: bnorm/norm**2, 1: (2*bnorm-2*c)/norm**2}
    p = monomial_term(Q(1), 6, 6)
    for pole, coefficient in poles.items():
        p = plus(p, monomial_term(coefficient, 6-pole, 6),
                 monomial_term(coefficient, 6, 6-pole))
    need(substitute_one_minus(p) == p and reverse_width(p, 12) == p,
         name + ' both generators of identical-field crossing')
    blocks = global_blocks(p, 6, order, positive=True, even=True)
    aa = list(map(Q, blocks['global_primary_squared_coupling_sums']))
    stress = 18/c
    lambda_norm = c*(5*c+22)/10
    lambda_coupling_sq = Q(4608)/(5*c*(5*c+22))
    primary4_sq = aa[4]-lambda_coupling_sq
    need(aa[2] == stress and primary4_sq >= 0, name + ' positive low-channel decomposition')
    need(primary4_sq == 48*(c+2)*(8-lam*(5*c+22))/(c*(5*c+22)),
         name + ' primary4 invariant in(c,lambda)')
    return {'central_charge': str(c), 'lambda': str(lam),
            'canonical_a_two_point_coefficient': str(norm), 'a3_b_coefficient': str(a0),
            'b_norm_squared': str(bnorm), 'external_field': 'a_hat=a/sqrt(c/3), weight3',
            'numerator': list(map(str, p)), 'denominator': 'x^6*(1-x)^6',
            'normalized_principal_part_at0': {str(k): str(v) for k, v in poles.items()},
            'global_blocks': blocks,
            'three_point': {'a_hat_self_cubic': '0', 'unit_stress_squared_coupling': str(stress),
                            'Lambda_definition': ':TT:-(3/10)*d2T',
                            'Lambda_norm_squared': str(lambda_norm),
                            'unit_Lambda_squared_coupling': str(lambda_coupling_sq),
                            'primary4_definition': 'b-(32/(5c+22))*Lambda-(3/10)*d2T',
                            'unit_primary4_squared_coupling': str(primary4_sq),
                            'primary4_norm_squared': str(primary4_sq*norm**2)},
            'scope': 'Canonical chiral spin3 four-point function reconstructed from saved OPE invariants; no new mode replay.'}


def lightest_blocks():
    weights = [(Q(2, 3), Q(1, 3)), (Q(-1, 3), Q(1, 3)), (Q(-1, 3), Q(-2, 3))]
    full = [(Q(0),)*6 + w for w in weights]
    right = (5, 8, 9, 8, 5, 0, 2, 2)
    gram = [[dot(a, b) for b in full] for a in full]
    charges = [dot(a, right) for a in full]
    need(charges == [2, 0, -2], 'A2 triplet principal-current charges')
    need(gram == [[Q(2, 3) if i == j else Q(-1, 3) for j in range(3)] for i in range(3)],
         'A2 fundamental-weight Gram matrix')
    current = [[Q(a*b, 78) for b in charges] for a in charges]
    complement = [[gram[i][j]-current[i][j] for j in range(3)] for i in range(3)]
    for vector, eigenvalue in (([1, 1, 1], Q(0)), ([1, -2, 1], Q(1)), ([1, 0, -1], Q(35, 39))):
        need([sum(complement[i][j]*vector[j] for j in range(3)) for i in range(3)]
             == [eigenvalue*x for x in vector], 'positive complementary-top Gram eigenvalues')
    blocks = []
    for i, j in product(range(3), repeat=2):
        blocks.append({'outer_triplet_index': i, 'inner_triplet_index': j,
                       'ordering': '<V_-beta_i(infty) V_beta_i(1) V_-beta_j(x) V_beta_j(0)>',
                       'x_power': '-2/3', 'one_minus_x_power': str(-gram[i][j]),
                       'leading_x_channel_coefficient': '1',
                       'relative_weight1_coefficient': str(gram[i][j]),
                       'U_vacuum_current_part': str(current[i][j]),
                       'X_equals_b_top_part': str(complement[i][j])})
    triples = []
    for choice in product(range(3), repeat=3):
        if add_momenta(*(full[i] for i in choice)) == (0,)*8:
            need(len(set(choice)) == 3, 'three distinct weights for charge-neutral triple')
            triples.append({'triplet_indices': list(choice), 'normalized_coefficient_absolute_squared': '1',
                            'coordinate_factor': '(z12*z13*z23)^(-1/3)',
                            'phase': 'depends on the chosen lattice-intertwiner cocycle/bases'})
    need(len(triples) == 6, 'six nonzero ordered fundamental triples')
    return {'B_lattice_cosets': '(0,+1) and(0,-1), both restrict to the U module c1',
            'conformal_weight': '1/3', 'top_dimension': 3,
            'A2_weights': [list(map(str, w)) for w in weights],
            'Cartan_HR_charges': list(map(str, charges)),
            'weight_Gram_matrix': [list(map(str, row)) for row in gram],
            'blocks': blocks, 'three_point_absolute_data': triples,
            'X_top_Gram_matrix': [list(map(str, row)) for row in complement],
            'X_top_Gram_eigenvalues': ['0', '1', '35/39'],
            'branch_convention': '0<x<1 positive real powers; analytic continuation along a chosen path',
            'normalization': 'paired lattice intertwiners have unit leading vacuum coefficient',
            'scope': 'Selected B-lattice chiral intertwiner blocks restricted to U. They do not constitute a sewn diagonal-U bulk correlator or a complete U-channel basis.'}


def ward_four_points(order):
    """Unit Cartan and c=8 unit stress fields, by their Ward identities."""
    result = {}
    for name, power, poles in (
            ('unit_Cartan', 2, {2: Q(1)}),
            ('unit_total_stress', 4, {4: Q(1), 2: Q(1), 1: Q(1)})):
        p = monomial_term(Q(1), power, power)
        for pole, coefficient in poles.items():
            p = plus(p, monomial_term(coefficient, power-pole, power),
                     monomial_term(coefficient, power, power-pole))
        need(substitute_one_minus(p) == p and reverse_width(p, 2*power) == p,
             name + ' identical-field crossing')
        result[name] = {
            'external_weight': power//2,
            'numerator': list(map(str, p)),
            'denominator': f'x^{power}*(1-x)^{power}',
            'global_blocks': global_blocks(p, power, order, positive=True, even=True),
            'scope': 'Vacuum Ward identity, with unit two-point coefficient.'}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--order', type=int, default=32)
    args = parser.parse_args()
    need(0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3,
         'use guarded launcher with AS at most1GiB')
    need(8 <= args.order <= 48, 'global-series order between8and48')
    paths = [args.output] + [args.output.with_suffix(s) for s in ('.terms.tsv', '.global_blocks.tsv', '.samples.tsv')]
    need(args.output.parent.is_dir() and all(not p.exists() for p in paths), 'fresh outputs in an existing directory required')
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('120-second exact-data cap')))
    signal.alarm(120)
    started = monotonic()
    hashes = {name: sha(ROOT/name) for name in SOURCES}
    uu = u_correlators(args.order)
    frozen = read_json('hi_cft_20260923_proof_pf13_ope.json')
    w3 = {'Potts': w3_correlator('Potts', Q(4, 5), Q(4, 13), frozen['control_Potts'], args.order),
          'PF13': w3_correlator('PF13', Q(8, 5), Q(14, 473), frozen, args.order)}
    need(w3['Potts']['three_point']['unit_primary4_squared_coupling'] == '0', 'Potts weight4 null')
    need(w3['PF13']['three_point']['unit_primary4_squared_coupling'] == '60552/2365', 'PF13 genuine weight4 coupling')
    light = lightest_blocks()
    ward = ward_four_points(args.order)
    all_rational = {name: (list(map(Q, data['numerator'])), 4)
                    for name, data in uu['channels'].items()}
    all_rational.update({name: (list(map(Q, data['numerator'])), 6) for name, data in w3.items()})
    all_rational.update({name: (list(map(Q, data['numerator'])), 2*data['external_weight'])
                         for name, data in ward.items()})
    samples = []
    for name, (p, power) in all_rational.items():
        for x in (Q(1, 10), Q(1, 4), Q(1, 2), Q(3, 4), Q(9, 10)):
            samples.append({'correlator': name, 'x': str(x),
                            'value': str(value(p, x)/(x**power*(1-x)**power))})
    need(all(sha(ROOT/name) == digest for name, digest in hashes.items()), 'unchanged source hashes')
    output = {'format': 'haagerup-c8-exact-correlators-v1', 'source_sha256': hashes,
              'u_four_point': uu, 'spin3_four_point': w3, 'lightest_chiral_blocks': light,
              'Ward_four_point': ward,
              'current_Ward_data': {'current_norms': [2, 78], 'u_charges': [1, 13],
                  'H_H_u_udag_formula': 'z34^-4 * [K_ab/z12^2 + q_a*q_b*(1/z13-1/z14)*(1/z23-1/z24)]',
                  'T_u_udag_formula': '2/(z12^2*z13^2*z23^2)',
                  'normalized_T_T_T_coefficient_c8': '1'},
              'samples': samples,
              'checks': {'integer_charge_assignments': len(uu['terms']),
                         'u_orderings': 6, 'surviving_terms_per_ordering': 15,
                         'u_crossing_polynomial_identities': True,
                         'spin3_crossing_polynomial_identities': True,
                         'global_block_reconstruction': True,
                         'reflection_positive_series_checked_through_weight': args.order,
                         'lightest_X_Gram_positive_semidefinite': True,
                         'scope': 'Finite exact checks, not a formal proof of all-order positivity or of bulk sewing.'},
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    with args.output.open('x') as stream:
        json.dump(output, stream, indent=2)
        stream.write('\n')
    with paths[1].open('x', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['ordering', 'vertex_choices', 'charge_conserving', 'total_momentum',
                         'cocycle_phase', 'q0', 'qs', 'qt', 'qst', 'x_power', 'one_minus_x_power'])
        for term in uu['terms']:
            writer.writerow([term['ordering'], json.dumps(term['vertex_choices']), term['charge_conserving'],
                             json.dumps(term['total_momentum']), term['cocycle_phase'],
                             *term['coefficient_before_charge_delta'], term['x_power'], term['one_minus_x_power']])
    with paths[2].open('x', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['correlator', 'global_weight', 'squared_coupling_sum', 'reduced_series_coefficient'])
        for name, data in [('u_neutral', uu['channels']['mpmp']),
                           ('u_equal_charge', uu['channels']['mmpp']), *w3.items(), *ward.items()]:
            block = data['global_blocks']
            for n, (a, b) in enumerate(zip(block['global_primary_squared_coupling_sums'], block['reduced_series'])):
                writer.writerow([name, n, a, b])
    with paths[3].open('x', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['correlator', 'x', 'exact_value'])
        for sample in samples:
            writer.writerow([sample['correlator'], sample['x'], sample['value']])
    boundary()
    print(json.dumps({'output': str(args.output), 'checks': output['checks'],
                      'seconds': output['seconds'], 'peak_rss_KiB': output['peak_rss_KiB']}), flush=True)


if __name__ == '__main__':
    main()
