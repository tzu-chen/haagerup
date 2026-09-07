"""Verify the branch-permuting finite-field norm laws of Section 63.

The phases are recovered from the saved, completely verified row data;
the search's primitive elements and exponent representatives are not used.
These checks establish the norm laws at orders 9 and 27, not at all orders.
"""

import json
from pathlib import Path


def verify_order(n, k):
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    data = [json.loads((directory / f'hi_finite_field_{n}_char2_{j}.json').read_text())
            for j in range(k)]
    assert all(v[:4] == data[0][:4] for v in data)
    assert data[0][0:2] == [n, 2]
    encode = lambda coefficients: sum(c << i for i, c in enumerate(coefficients))
    degree = len(data[0][2]) - 1
    modulus, d = encode(data[0][2]), encode(data[0][3])

    def mul(a, b):
        value = 0
        while b:
            if b & 1:
                value ^= a
            b >>= 1
            a <<= 1
            if a >> degree:
                a ^= modulus
        return value

    def power(a, b):
        value = 1
        while b:
            if b & 1:
                value = mul(value, a)
            a = mul(a, a)
            b >>= 1
        return value

    inverse = lambda a: power(a, (1 << degree) - 2)
    assert mul(d, d) == d ^ 1
    phases = []
    for entry in data:
        row = list(map(encode, entry[4]))
        assert row[:2] == [1, 1]
        # R_2 = W_1^2/W_2 = W_1^(-2) in the Frobenius gauge.
        first = power(inverse(row[2]), 1 << (degree-1))
        w = [1, first]
        for a in range(2, n):
            w.append(mul(mul(first, w[-1]), inverse(row[a])))
        assert all(mul(w[a], w[-a]) == d and w[2*a % n] == power(w[a], 4)
                   for a in range(1, n))
        phases.append(w)

    checked = naive_failures = no_twist_failures = 0
    for j in range(k):
        for a in range(1, n):
            if 3*a % n == 0:
                continue
            s, unit = 0, a
            while unit % 3 == 0:
                s, unit = s+1, unit//3
            r = 2 * 3**(k-s-1)
            norm_exponent = (4**r - 1) // (4**(r//3) - 1)
            normalized = mul(d ^ 1, power(phases[(j-1) % k][a], norm_exponent))
            twisted = power(normalized, 4) if j == 0 else normalized
            target = phases[j][3*a % n]
            assert twisted == target, (n, j, a)
            checked += 1
            no_twist_failures += normalized != target
            naive_failures += mul(d ^ 1, power(phases[j][a], norm_exponent)) != target
    assert checked == k * (n-3)
    assert naive_failures == checked
    assert no_twist_failures == (0 if n == 9 else 24)
    print(f'n={n}: all {checked} twisted cross-branch norms passed; '
          f'naive same-branch failures={naive_failures}; '
          f'failures after omitting the wrap-around Frobenius={no_twist_failures}')


if __name__ == '__main__':
    verify_order(9, 2)
    verify_order(27, 3)
    print('SAVED FINITE CERTIFICATES SATISFY THE BRANCH-PERMUTING NORM LAWS')
