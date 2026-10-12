#!/usr/bin/env python3
"""Exact Haagerup-center defect and Cardy-boundary data, gamma=0, c=8.

Run ONLY through the project resource launcher.  Fixed rank 12; stdlib only.
Estimated peak <150 MiB, reviewed address cap 1 GiB, expected <300 seconds.
No old data are mutated or imported.  Q(zeta_13) arithmetic is exact; decimal
columns are explicitly for plotting.  The auxiliary omega extension is used
only to check the modular relation, not to infer fusion by rounding.
"""
from __future__ import annotations

import argparse
import cmath
import csv
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import time

N = 12
LABELS = ['0', 'b', 'a', 'c0', 'c1', 'c2'] + [f'd{i}' for i in range(1, 7)]
PAPER_LABELS = ['1', 'pi1', 'pi2', 'sigma1', 'sigma2', 'sigma3', 'mu5', 'mu2', 'mu1', 'mu3', 'mu6', 'mu4']
WEIGHTS = list(map(F, ['0', '1', '1', '1', '1/3', '2/3', '6/13', '11/13', '15/13', '5/13', '7/13', '8/13']))
TOPS = [1, 80, 81, 81, 3, 27, 7, 42, 119, 5, 13, 14]
H3_LABELS = ['1', 'alpha', 'alpha2', 'rho', 'alpha_rho', 'alpha2_rho']


def k(value=0):
    if isinstance(value, tuple):
        if len(value) != 12:
            raise ValueError('field vector length')
        return value
    return (F(value),) + (F(0),) * 11


ZERO, ONE = k(), k(1)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def scale(a, q):
    return tuple(x * q for x in a)


def mul(a, b):
    # zeta^13=1, followed by zeta^12=-(1+...+zeta^11).
    if a == ZERO or b == ZERO:
        return ZERO
    if not any(a[1:]):
        return scale(b, a[0])
    if not any(b[1:]):
        return scale(a, b[0])
    out = [F(0)] * 13
    aa = [(i, x) for i, x in enumerate(a) if x]
    bb = [(j, y) for j, y in enumerate(b) if y]
    for i, x in aa:
        for j, y in bb:
            out[(i + j) % 13] += x * y
    return tuple(out[i] - out[12] for i in range(12))


def zeta(exponent):
    j = exponent % 13
    if j == 12:
        return (F(-1),) * 12
    return tuple(F(i == j) for i in range(12))


def conj(a):
    out = ZERO
    for i, x in enumerate(a):
        if x:
            out = add(out, scale(zeta(-i), x))
    return out


def total(values):
    ans = ZERO
    for a in values:
        ans = add(ans, a)
    return ans


def approximate(a):
    zz = cmath.exp(2j * cmath.pi / 13)
    ans = sum(float(x) * zz**i for i, x in enumerate(a))
    if abs(ans.imag) > 1e-9:
        raise AssertionError('expected real number in plotting column')
    return ans.real


def encode(a):
    return [str(x) for x in a]


def integer(a):
    if any(a[1:]) or a[0].denominator != 1:
        raise AssertionError(f'non-integral Verlinde coefficient: {a}')
    return int(a[0])


def mm(A, B):
    return [[total(mul(A[i][r], B[r][j]) for r in range(N)) for j in range(N)] for i in range(N)]


def pmul(x, y):
    # (a+b*omega)(c+d*omega), omega^2+omega+1=0.
    a, b = x
    c, d = y
    bd = mul(b, d)
    return add(mul(a, c), neg(bd)), add(add(mul(a, d), mul(b, c)), neg(bd))


def padd(x, y):
    return add(x[0], y[0]), add(x[1], y[1])


def theta_pair(h):
    h %= 1
    if h.denominator in (1, 13):
        return zeta(int(13 * h)), ZERO
    if h == F(1, 3):
        return ZERO, ONE
    if h == F(2, 3):
        return neg(ONE), neg(ONE)
    raise ValueError('unexpected twist')


def construct():
    ahkz_mu_twists = dict(zip([f'mu{i}' for i in range(1, 7)], map(lambda a: F(a, 13), [2, 11, 5, 8, 6, 7])))
    assert all(WEIGHTS[i] % 1 == ahkz_mu_twists[PAPER_LABELS[i]] for i in range(6, 12))
    residues = {1, 3, 4, 9, 10, 12}
    r = total(scale(zeta(j), 1 if j in residues else -1) for j in range(1, 13))
    assert mul(r, r) == k(13) and conj(r) == r
    assert approximate(r) > 0
    invr = scale(r, F(1, 13))
    alpha = scale(add(k(F(1, 3)), neg(invr)), F(1, 2))
    beta = scale(add(k(F(1, 3)), invr), F(1, 2))
    S = [[ZERO for _ in range(N)] for _ in range(N)]
    S[0][0] = S[1][1] = alpha
    S[0][1] = S[1][0] = beta
    for i in (0, 1):
        for j in range(2, 6):
            S[i][j] = S[j][i] = k(F(1, 3))
    block = [[2, -1, -1, -1], [-1, 2, -1, -1], [-1, -1, -1, 2], [-1, -1, 2, -1]]
    for i in range(4):
        for j in range(4):
            S[2+i][2+j] = k(F(block[i][j], 3))
    for i in range(6):
        S[0][6+i] = S[6+i][0] = invr
        S[1][6+i] = S[6+i][1] = neg(invr)
        for j in range(6):
            S[6+i][6+j] = neg(mul(invr, add(zeta((i+1)*(j+1)), zeta(-(i+1)*(j+1)))))
    invvac = [scale(add(k(13), scale(r, 3)), F(3, 2)), scale(add(k(13), scale(r, -3)), F(3, 2))] + [k(3)] * 4 + [r] * 6
    for i in range(N):
        assert mul(S[0][i], invvac[i]) == ONE
    return r, S, invvac


def exact_checks_and_fusion(r, S, invvac):
    identity = [[k(i == j) for j in range(N)] for i in range(N)]
    assert all(S[i][j] == S[j][i] == conj(S[i][j]) for i in range(N) for j in range(N))
    assert mm(S, S) == identity
    theta = [theta_pair(h) for h in WEIGHTS]
    invtheta = [theta_pair(-h) for h in WEIGHTS]
    # STS=T^{-1}ST^{-1}, equivalently (ST)^3=S^2=1.
    for i in range(N):
        for j in range(N):
            lhs = (ZERO, ZERO)
            for ell in range(N):
                lhs = padd(lhs, pmul((mul(S[i][ell], S[ell][j]), ZERO), theta[ell]))
            rhs = pmul(pmul(invtheta[i], (S[i][j], ZERO)), invtheta[j])
            assert lhs == rhs, ('modular', i, j)
    dims = [mul(S[0][i], invvac[0]) for i in range(N)]
    fusion = [[[0] * N for _ in range(N)] for _ in range(N)]
    for i in range(N):
        for j in range(i, N):
            pair = [mul(mul(S[i][ell], S[j][ell]), invvac[ell]) for ell in range(N)]
            for m in range(N):
                val = integer(total(mul(pair[ell], S[m][ell]) for ell in range(N)))
                assert val >= 0
                fusion[i][j][m] = fusion[j][i][m] = val
            assert total(scale(dims[m], fusion[i][j][m]) for m in range(N)) == mul(dims[i], dims[j])
    assert all(fusion[0][i][j] == (i == j) for i in range(N) for j in range(N))
    assert all(fusion[i][j][0] == (i == j) for i in range(N) for j in range(N))
    # A completely integer associativity check, independent of rounding.
    for a in range(N):
        for b in range(N):
            for c in range(N):
                for d in range(N):
                    assert sum(fusion[a][b][x] * fusion[x][c][d] for x in range(N)) == sum(fusion[b][c][x] * fusion[a][x][d] for x in range(N))
    return dims, fusion


def tsv(path, header, rows):
    with path.open('w', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(header)
        writer.writerows(rows)


def leading_at(i, weight):
    if weight == WEIGHTS[i]:
        return TOPS[i]
    if i == 0 and weight == 1:
        return 6
    raise ValueError(('additional character coefficient needed', i, weight))


def twisted_gap(matrix):
    entries = [(i, j, matrix[i][j]) for i in range(N) for j in range(N) if matrix[i][j]]
    ground = min(WEIGHTS[i] + WEIGHTS[j] for i, j, _ in entries)
    ground_dim = sum(n * TOPS[i] * TOPS[j] for i, j, n in entries if WEIGHTS[i] + WEIGHTS[j] == ground)
    scalar = []
    for i, j, n in entries:
        if (WEIGHTS[i] - WEIGHTS[j]).denominator != 1:
            continue
        weight = max(WEIGHTS[i], WEIGHTS[j])
        if weight == 0:
            weight = F(1)  # Exclude the identity; U has six weight-one currents.
        scalar.append((2 * weight, n * leading_at(i, weight) * leading_at(j, weight)))
    if scalar:
        delta = min(x for x, _ in scalar)
        degeneracy = sum(n for x, n in scalar if x == delta)
    else:
        delta, degeneracy = None, 0
    return ground, ground_dim, delta, degeneracy


def h3_fusion():
    out = [[[0]*6 for _ in range(6)] for _ in range(6)]
    for a in range(6):
        for b in range(6):
            i, j, left_rho, right_rho = a % 3, b % 3, a >= 3, b >= 3
            if not left_rho:
                out[a][b][(i+j) % 3 + (3 if right_rho else 0)] = 1
            elif not right_rho:
                out[a][b][(i-j) % 3 + 3] = 1
            else:
                out[a][b][(i-j) % 3] = 1
                out[a][b][3:] = [1, 1, 1]
    return out


def export(out):
    start = time.monotonic()
    out.mkdir(parents=True, exist_ok=True)
    r, S, invvac = construct()
    dims, fusion = exact_checks_and_fusion(r, S, invvac)
    print('exact modular and Verlinde checks passed', flush=True)
    Sdec = [[approximate(x) for x in row] for row in S]
    eigen = [[mul(S[a][i], invvac[i]) for i in range(N)] for a in range(N)]
    g2 = [mul(mul(S[0][i], S[0][i]), invvac[0]) for i in range(N)]
    global_dim = total(mul(x, x) for x in dims)
    assert global_dim == mul(invvac[0], invvac[0])
    data = {'schema': 'haagerup-c8-defects-v1', 'central_charge_left_right': [8, 8],
            'status': 'exact consequences of the supplied positive Haagerup modular data and gamma=0 character tops',
            'field': {'name': 'Q(zeta13)', 'embedding': 'zeta13=exp(2*pi*i/13)', 'basis': ['1'] + [f'zeta13^{i}' for i in range(1, 12)], 'encoding': '12 rational strings in ascending powers; Phi13=0'},
            'labels': LABELS, 'AHKZ_labels': PAPER_LABELS,
            'lowest_weights': list(map(str, WEIGHTS)), 'top_dimensions': TOPS,
            'twist_exponents_mod1': [str(h % 1) for h in WEIGHTS],
            'character_T_exponents_mod1': [str((h-F(1,3)) % 1) for h in WEIGHTS],
            'S_exact': [[encode(x) for x in row] for row in S], 'S_decimal_for_plotting': Sdec,
            'dimensions_exact': list(map(encode, dims)), 'global_dimension_exact': encode(global_dim),
            'fusion_N_ab_c': fusion, 'line_eigenvalues_exact': [[encode(x) for x in row] for row in eigen],
            'Cardy_boundary_g_squared_exact': list(map(encode, g2)),
            'checks': {'S_real_symmetric': True, 'S_squared_identity': True, 'S_theta_cubed_identity': True,
                       'Verlinde_integral_nonnegative': True, 'fusion_associative': True, 'dimensions_multiplicative': True,
                       'all_center_simples_self_dual': True},
            'sources': ['https://arxiv.org/abs/1006.1326', 'https://arxiv.org/abs/2512.08225v2', 'https://arxiv.org/abs/2302.13900'],
            'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    tsv(out/'modular_S.tsv', ['row', 'column', 'exact_zeta13_coefficients', 'decimal'], ((LABELS[i], LABELS[j], json.dumps(encode(S[i][j])), f'{Sdec[i][j]:.16g}') for i in range(N) for j in range(N)))
    tsv(out/'fusion.tsv', ['a', 'b', 'c', 'N_ab_c'], ((LABELS[a], LABELS[b], LABELS[c], fusion[a][b][c]) for a in range(N) for b in range(N) for c in range(N)))
    tsv(out/'line_eigenvalues.tsv', ['line', 'bulk_chiral_label', 'exact_zeta13_coefficients', 'decimal'], ((LABELS[a], LABELS[i], json.dumps(encode(eigen[a][i])), f'{approximate(eigen[a][i]):.16g}') for a in range(N) for i in range(N)))
    tsv(out/'defect_sectors.tsv', ['label', 'AHKZ_label', 'h', 'top_dimension', 'twist_exponent_mod1', 'T_character_exponent_mod1', 'qdim', 'Cardy_g', 'Cardy_g_squared_exact'], ((LABELS[i], PAPER_LABELS[i], str(WEIGHTS[i]), TOPS[i], str(WEIGHTS[i] % 1), str((WEIGHTS[i]-F(1,3)) % 1), f'{approximate(dims[i]):.16g}', f'{approximate(g2[i])**0.5:.16g}', json.dumps(encode(g2[i]))) for i in range(N)))
    twisted, twisted_rows = [], []
    for a in range(N):
        matrix = [[fusion[a][i][j] for j in range(N)] for i in range(N)]
        ground, gd, scalar, sd = twisted_gap(matrix)
        entry = {'line': LABELS[a], 'character_bilinear_matrix': matrix, 'ground_dimension': str(ground), 'ground_degeneracy': gd, 'first_nonidentity_scalar_dimension': str(scalar) if scalar is not None else None, 'scalar_degeneracy': sd}
        twisted.append(entry)
        twisted_rows.append((LABELS[a], str(ground), gd, str(scalar) if scalar is not None else 'none', sd, json.dumps(matrix)))
    data['diagonal_U_twisted_sectors'] = twisted
    tsv(out/'twisted_gaps.tsv', ['line', 'ground_Delta', 'ground_degeneracy', 'first_nonidentity_scalar_Delta', 'scalar_degeneracy', 'N_ai_j_matrix'], twisted_rows)
    annuli = []
    for a in range(N):
        for b in range(N):
            row = fusion[a][b]
            lowest = min(WEIGHTS[i] for i in range(N) if row[i])
            candidates = [(WEIGHTS[i] if i else F(1), row[i] * (TOPS[i] if i else 6)) for i in range(N) if row[i]]
            nonidentity = min(h for h, _ in candidates)
            multiplicity = sum(n for h, n in candidates if h == nonidentity)
            annuli.append((LABELS[a], LABELS[b], str(lowest), row[0], str(nonidentity), multiplicity, json.dumps(row)))
    tsv(out/'Cardy_annuli.tsv', ['boundary_a', 'boundary_b', 'lowest_h', 'identity_multiplicity', 'first_nonidentity_h_including_currents', 'multiplicity', 'character_coefficients'], annuli)
    # Canonical center forgetful functor for the selected H3 boundary.
    forgetful = [[1, 1, 2, 0, 0, 0] + [0]*6,
                 [0, 0, 0, 1, 1, 1] + [0]*6,
                 [0, 0, 0, 1, 1, 1] + [0]*6] + [[0, 1, 1, 1, 1, 1] + [1]*6 for _ in range(3)]
    h3 = h3_fusion()
    d = scale(add(k(3), r), F(1, 2))
    h3dims = [ONE]*3 + [d]*3
    for mu in range(N):
        assert total(scale(h3dims[x], forgetful[x][mu]) for x in range(6)) == dims[mu]
    # Check that the printed forgetful table really is a based-ring map.
    for mu in range(N):
        for nu in range(N):
            for x in range(6):
                lhs = sum(fusion[mu][nu][lam] * forgetful[x][lam] for lam in range(N))
                rhs = sum(forgetful[a][mu] * forgetful[b][nu] * h3[a][b][x] for a in range(6) for b in range(6))
                assert lhs == rhs, ('forgetful ring map', mu, nu, x)
    extension = forgetful[0]
    assert all(total(scale(S[i][j], extension[j]) for j in range(N)) == k(extension[i]) for i in range(N))
    assert all(not extension[i] or WEIGHTS[i].denominator == 1 for i in range(N))
    tube = []
    for i in range(N):
        scalar = WEIGHTS[i].denominator == 1
        w = max(F(1), WEIGHTS[i]) if scalar else None
        tube.append({'label': LABELS[i], 'partition_function': f'chi_{LABELS[i]} * conjugate(chi_E8)',
                     'lowest_Delta': str(WEIGHTS[i]), 'lowest_degeneracy': TOPS[i],
                     'scalar_gap_excluding_identity': str(2*w) if scalar else None,
                     'scalar_gap_degeneracy': leading_at(i, w)*248 if scalar else 0,
                     'multiplicity_convention': 'V_mu in LS Eq4.1; tube-irrep W_x^mu is not included'})
    data['E8_H3'] = {'scope': 'canonical holomorphic extension and standard rational-CFT boundary construction; first chiral H3 factor only',
                     'labels': H3_LABELS, 'fusion_N_ab_c': h3, 'forgetful_n_x_mu': forgetful,
                     'untwisted_branching': extension, 'tube_multiplicity_spaces': tube,
                     'H3_invariant_scalar_gap': '2', 'H3_invariant_scalar_multiplicity': 6*248,
                     'charged_union_pi2_sigma1_scalar_gap': '2',
                     'untwisted_Z3_charged_scalar_multiplicity': 2*81*248,
                     'forgetful_ring_map_checked': True}
    # Elementary U-preserving boundaries of the full holomorphic E8 theory.
    # Their open channel is restriction of x^* tensor_A y in C=D_A.
    h3dual = [0, 2, 1, 3, 4, 5]
    e8annuli, e8annulus_json = [], []
    for x in range(6):
        for y in range(6):
            row = [sum(h3[h3dual[x]][y][z] * forgetful[z][mu] for z in range(6)) for mu in range(N)]
            assert row[0] == (x == y)
            # Closed-channel vacuum coefficient = g_x g_y, so g_x=qdim_C x.
            assert total(scale(S[0][mu], row[mu]) for mu in range(N)) == mul(h3dims[x], h3dims[y])
            lowest = min(WEIGHTS[mu] for mu in range(N) if row[mu])
            candidates = [(WEIGHTS[mu] if mu else F(1), row[mu]*(TOPS[mu] if mu else 6)) for mu in range(N) if row[mu]]
            positive = min(h for h, _ in candidates)
            degeneracy = sum(n for h, n in candidates if h == positive)
            e8annuli.append((H3_LABELS[x], H3_LABELS[y], str(lowest), row[0], str(positive), degeneracy, json.dumps(row)))
            e8annulus_json.append({'x': H3_LABELS[x], 'y': H3_LABELS[y], 'character_coefficients': row,
                                  'lowest_h': str(lowest), 'identity_multiplicity': row[0],
                                  'first_nonidentity_h': str(positive), 'multiplicity': degeneracy})
    data['E8_H3']['U_preserving_boundary_annuli'] = e8annulus_json
    data['E8_H3']['U_preserving_boundary_g_exact'] = list(map(encode, h3dims))
    data['E8_H3']['boundary_g_normalization'] = 'g_unit=1; g_x=qdim_C(x); vacuum closed-channel coefficients checked exactly'
    tsv(out/'E8_U_preserving_annuli.tsv', ['boundary_x', 'boundary_y', 'lowest_h', 'identity_multiplicity', 'first_nonidentity_h', 'multiplicity', 'U_character_coefficients'], e8annuli)
    tsv(out/'E8_U_preserving_boundaries.tsv', ['boundary_x', 'g_exact_zeta13_coefficients', 'g_decimal'], ((H3_LABELS[x], json.dumps(encode(h3dims[x])), f'{approximate(h3dims[x]):.16g}') for x in range(6)))
    tsv(out/'H3_forgetful.tsv', ['defect'] + LABELS, ((H3_LABELS[x], *forgetful[x]) for x in range(6)))
    tsv(out/'H3_fusion.tsv', ['a', 'b', 'c', 'N_ab_c'], ((H3_LABELS[a], H3_LABELS[b], H3_LABELS[c], h3[a][b][c]) for a in range(6) for b in range(6) for c in range(6)))
    tsv(out/'E8_H3_tube_sectors.tsv', ['mu', 'lowest_Delta', 'lowest_degeneracy', 'first_nonidentity_scalar_Delta', 'scalar_degeneracy', 'partition_function'], ((x['label'], x['lowest_Delta'], x['lowest_degeneracy'], x['scalar_gap_excluding_identity'] or 'none', x['scalar_gap_degeneracy'], x['partition_function']) for x in tube))
    h3twisted = []
    for x, row in enumerate(forgetful):
        ground = min(WEIGHTS[i] for i in range(N) if row[i])
        gd = sum(row[i]*TOPS[i] for i in range(N) if WEIGHTS[i] == ground)
        sd = sum(row[i]*leading_at(i, F(1))*248 for i in range(N) if row[i] and WEIGHTS[i].denominator == 1)
        h3twisted.append((H3_LABELS[x], str(ground), gd, '2', sd, json.dumps(row)))
    tsv(out/'E8_H3_twisted.tsv', ['defect_x', 'lowest_Delta', 'lowest_degeneracy', 'first_nonidentity_scalar_Delta', 'scalar_degeneracy', 'left_character_coefficients_right_E8'], h3twisted)
    data['seconds'] = time.monotonic() - start
    (out/'defect_data.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'seconds': data['seconds'], 'rank': N, 'fusion_entries': N**3, 'diagonal_U_annuli': N**2, 'E8_annuli': 36, 'output': str(out/'defect_data.json')}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    export(args.output_dir)
