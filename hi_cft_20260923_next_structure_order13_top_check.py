"""Independent exact check of the order-13 core top table and h<2 bound.

Run only through hi_cft_safe_run.py with <=2 GiB address space.
Expected runtime <1 second and peak RSS <32 MiB: fractions and tiny
tables only. No lattice-mode engine, NumPy, SymPy, workers or floats.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


def potts(epsilon, m):
    if epsilon == 0:
        return Q(0) if m % 3 == 0 else Q(2, 3)
    return Q(2, 5) if m % 3 == 0 else Q(1, 15)


def t_top(epsilon, j):
    candidates = []
    for m in range(-12, 13):
        if (m-j) % 13:
            continue
        left = Q(1, 4) if m % 2 else Q(0)
        hp = potts(epsilon, m)
        h = Q(m*m, 156)+left+hp
        candidates.append((h, m, 2 if m % 2 else 1, left, hp))
    h = min(row[0] for row in candidates)
    return h, [row[1:] for row in candidates if row[0] == h]


def pf_top(a, k):
    return Q(a*(a+1), 15)-Q(k*k, 13)+max(0, abs(k)-a)


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default=
                        'hi_cft_20260923_next_structure_order13_top_check.json')
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(10)
    started = monotonic()
    outpath = Path(args.output)
    assert not outpath.exists()
    expected_h = [Q(0), Q(2, 15), Q(2, 5), Q(4, 5), Q(1, 3), Q(1), Q(4, 5),
                  Q(2, 5), Q(8, 15), Q(4, 5), Q(1, 5), Q(11, 15), Q(2, 5), Q(1, 5)]
    expected_d = [1, 1, 5, 9, 2, 14, 6, 1, 7, 15, 2, 14, 6, 2]
    expected_n = [0, 600, 10440, 56640, 5520, 148560, 54240,
                  7800, 36960, 110880, 4080, 81480, 18240, 4920]
    records = []
    for epsilon in range(2):
        for a in range(7):
            candidates = []
            for j in range(13):
                k = (-5*j+6) % 13-6
                ht, states = t_top(epsilon, j)
                hz = pf_top(a, k)
                candidates.append((ht+hz, j, k, hz, states))
            h = min(row[0] for row in candidates)
            minima = [row for row in candidates if row[0] == h]
            d = 0
            L = Q(0); h_square = Q(0); P = Q(0); Z = Q(0)
            charge_multiplicities = {}
            for _, j, k, hz, states in minima:
                for m, multiplicity, left, hp in states:
                    d += multiplicity
                    L += multiplicity*left
                    h_square += multiplicity*m*m
                    P += multiplicity*hp
                    Z += multiplicity*hz
                    charge_multiplicities[m] = charge_multiplicities.get(m, 0)+multiplicity
            assert L+h_square/156+P+Z == h*d
            W = L+Q(83, 6084)*h_square+Q(25, 6)*P+Q(25, 26)*Z
            W2 = L/26+Q(7, 936)*h_square+Q(125, 39)*P+Q(25, 26)*h*d
            assert W == W2
            index = 7*epsilon+a
            assert (h, d, 4680*W) == (expected_h[index], expected_d[index], expected_n[index])
            label = ('x' if epsilon == 0 else 'y')+str(a)
            records.append({'label': label, 'lowest_weight': h,
                            'absolute_j_minima': sorted({min(j, 13-j) for _, j, _, _, _ in minima}),
                            'dimension': d, 'L': L, 'H_squared': h_square,
                            'P': P, 'Z': Z, '4680W': 4680*W,
                            'H_charge_multiplicities': charge_multiplicities})

    # Necessary right-sl2 conditions: multiplicity at10 >= that at12;
    # multiplicity at7 >= that at9 (divide common left-doublet factor2).
    inequality1 = [r['H_charge_multiplicities'].get(10, 0)-r['H_charge_multiplicities'].get(12, 0)
                   for r in records]
    inequality2 = [Q(r['H_charge_multiplicities'].get(7, 0)-r['H_charge_multiplicities'].get(9, 0), 2)
                   for r in records]
    assert inequality1 == [0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0]
    assert inequality2 == [0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 1, 0, 0]
    residual = [7956, 7356, 29340, 14964, 10392, 0, 22212,
                156, 18732, 0, 11832, 1188, 29496, 10992]
    for i, r in enumerate(records):
        deficit = 4680*Q(17, 10)*r['dimension']-r['4680W']
        assert deficit == 8460*inequality1[i]+28716*inequality2[i]+residual[i]
        assert residual[i] >= 0
    result = {'exact_table_verified': True, 'exact_dual_verified': True,
              'universal_U_lowest_weight_bound': '17/10',
              'records': records, 'dual_nonnegative_residual': residual,
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              'scope': 'Exact arithmetic check of formulas and all dual coefficients; '
                       'the actual A_L embedding and VOA top-space arguments are '
                       'proved in the associated notes, not inferred by this script.',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    outpath.write_text(json.dumps(encode(result), indent=2)+'\n')
    print(json.dumps(encode({k: v for k, v in result.items() if k != 'records'})), flush=True)


if __name__ == '__main__':
    main()
