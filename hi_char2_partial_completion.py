"""Verify the origin-patched inflation identity and its false partial solutions.

Section 66 proves the identities uniformly. The inputs are saved complete
HI certificates at 9 and 27. Their inflations satisfy selected local Q
equations but deliberately fail another Q equation, so the outputs of
this program are NOT HI existence certificates at larger orders.
Requires only Python's standard library.
"""

import json
from pathlib import Path


def load_phases(path):
    data = json.loads(path.read_text())
    n, characteristic = data[:2]
    assert characteristic == 2
    encode = lambda v: sum(c << i for i, c in enumerate(v))
    degree, modulus, omega = len(data[2])-1, encode(data[2]), encode(data[3])

    def multiply(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a >> degree:
                a ^= modulus
        return result

    def power(a, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = multiply(result, a)
            a = multiply(a, a)
            exponent >>= 1
        return result

    row = list(map(encode, data[4]))
    assert row[:2] == [1, 1]
    phases = [1, power(power(row[2], (1 << degree)-2), 1 << (degree-1))]
    for a in range(2, n):
        phases.append(multiply(multiply(phases[1], phases[-1]),
                               power(row[a], (1 << degree)-2)))
    assert all(multiply(phases[a], phases[-a]) == omega
               and phases[2*a % n] == power(phases[a], 4) for a in range(1, n))
    return phases, omega, multiply, power


def residual(phases, multiply, g, h):
    n, result = len(phases), 0
    for a in range(n):
        first = multiply(phases[a], phases[(h-a) % n])
        second = multiply(phases[(-a-g) % n], phases[(a+g-h) % n])
        result ^= multiply(first, second)
    return result


def verify_inflations():
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    for m, branches in [(9, 2), (27, 3)]:
        for branch in range(branches):
            seed, omega, multiply, power = load_phases(
                directory / f'hi_finite_field_{m}_char2_{branch}.json')
            assert all(residual(seed, multiply, g, h) == 0
                       for g in range(1, m) for h in range(1, m))
            for factor in [3, 5, 9]:
                n = m*factor
                phases = [1]+[seed[a % m] if a % m else omega ^ 1
                              for a in range(1, n)]
                assert all(multiply(phases[a], phases[-a]) == omega
                           and phases[2*a % n] == power(phases[a], 4)
                           for a in range(1, n))
                local = 0
                for g in range(1, (m+1)//2):
                    for h in range(1, (m+1)//2):
                        assert residual(phases, multiply, g, h) == 0
                        local += 1
                assert residual(phases, multiply, 1, 1) == 0
                assert residual(phases, multiply, 2, 1) == 0
                # The newly separated origin positions produce exactly 1.
                assert residual(phases, multiply, m-1, 1) == 1
                if factor % 3 == 0:
                    assert residual(phases, multiply, n//3, 1) == omega ^ 1
                print(f'seed={m}, branch={branch}, inflated order={n}: '
                      f'{local} local Q passed; F({m-1},1)=1; '
                      'full Q deliberately fails', flush=True)


if __name__ == '__main__':
    verify_inflations()
    print('ALL EXACT INFLATION IDENTITIES PASSED; these are counterexamples to partial sufficiency.')
