"""Independent exact checks of the symbolic first-Q-lift generators."""

from itertools import islice
import json
from pathlib import Path
import resource
import time

from hi_convolution_balanced_witt import balanced_lift_error, pair_sums
from hi_convolution_hensel import UnramifiedRing
from hi_convolution_norm_obstruction import all_phases
from hi_frobenius_q_batch import PhaseRing
from hi_laurent_q_certificate import MUL, add_term
from hi_lift_q_polynomials import derivative_parts, lift_polynomial


def symbolic(n):
    ring = PhaseRing(n)
    r = (n-1)//2
    count = 0
    for g in range(1, r+1):
        for h in range(g, r+1):
            original = lift_polynomial(n, g, h)
            carry, parts = derivative_parts(n, g, h)
            weight = lambda e: sum((a+1)*v for a, v in enumerate(e)) % n
            combined = dict(carry)
            assert all(weight(e) == 0 for e in carry)
            for a, part in enumerate(parts):
                assert all(weight(e) == a for e in part)
                for e, v in part.items():
                    add_term(combined, e, v)
            assert combined == original
            substituted = {}
            for word, value in original.items():
                exponent, scalar = ring.word(word)
                add_term(substituted, exponent, MUL[value][scalar])
            assert substituted == ring.lift_error(g, h)
            for a, b in ((-g % n, h), (g, -h % n), (h, g)):
                assert original == lift_polynomial(n, a, b)
            count += 1
    print(f'EXACT symbolic n={n}; lift_generators={count}; '
          'quotient expansion, derivative decomposition, character weights and symmetries agree', flush=True)


def numeric(n):
    data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
    modulus, omega = data['modulus'], data['delta']
    field = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], 2)
    mul = field.ff_mul
    order = 2**field.degree-1

    def power(a, e):
        value = 1
        while e:
            if e & 1:
                value = mul(value, a)
            a = mul(a, a)
            e >>= 1
        return value

    count = 0
    polynomials = {(g, h): lift_polynomial(n, g, h)
                   for g in range(1, n) for h in range(1, n)}
    for phases in islice(all_phases(n, field, omega), 4):
        U = pair_sums(field, phases)
        powers = {}
        for (g, h), poly in polynomials.items():
            value = 0
            for word, coefficient in poly.items():
                term = (0, 1, omega, omega ^ 1)[coefficient]
                for a, e in enumerate(word, 1):
                    key = (a, e)
                    if key not in powers:
                        powers[key] = power(phases[a], e % order)
                    term = mul(term, powers[key])
                value ^= term
            assert value == balanced_lift_error(field, phases, U, g, h)[1]
            count += 1
    print(f'EXACT numeric n={n}; coordinates={count}; '
          'Laurent evaluation agrees with the independently checked Witt formula', flush=True)


def twist_example():
    # GF(16)=GF(4)[z]/(z^2+omega^2*z+1); a+4*b encodes a+b*z.
    class Field:
        @staticmethod
        def ff_mul(x, y):
            a, b, c, d = x & 3, x >> 2, y & 3, y >> 2
            bd = MUL[b][d]
            return (MUL[a][c] ^ bd) + 4*(MUL[a][d] ^ MUL[b][c] ^ MUL[3][bd])

    field = Field()
    mul = field.ff_mul

    def power(a, e):
        result = 1
        for _ in range(e):
            result = mul(result, a)
        return result

    z, omega = 4, 2
    assert power(z, 5) == 1 and z != 1
    w = [1, mul(3, z), mul(3, power(z, 4))]
    assert mul(w[1], w[2]) == omega and power(w[1], 4) == w[2]

    def evaluate(poly):
        result = 0
        for (e,), coefficient in poly.items():
            result ^= mul(coefficient, power(w[1], e % 15))
        return result

    carry, parts = derivative_parts(3, 1, 1)
    assert (evaluate(carry) ^ evaluate(parts[0]), evaluate(parts[1]), evaluate(parts[2])) == (0, 3, 3)

    def matrix(phases):
        return [[3 if g == h == 0 else 2 if not g or not h or g == h else
                 mul(2, mul(mul(phases[g], phases[(h-g) % 3]), power(phases[h], 14)))
                 for h in range(3)] for g in range(3)]

    A = matrix(w)
    for g in range(3):
        for h in range(3):
            for k in range(3):
                for ell in range(3):
                    residual = (3 if g == h == 0 else 0) ^ mul(A[(g+ell) % 3][k], A[(h+k) % 3][ell])
                    for m in range(3):
                        residual ^= mul(A[m][(g+h) % 3], mul(A[g][(m+k) % 3], A[h][(m+ell) % 3]))
                    assert residual == 0
    for chi in (1, 2, 3):
        twisted = [mul(value, power(chi, a)) for a, value in enumerate(w)]
        assert matrix(twisted) == A
        f, lifted = balanced_lift_error(field, twisted, pair_sums(field, twisted), 1, 1)
        assert f == 0 and lifted == (0 if chi == 1 else 3)
        assert lifted == mul(3, chi ^ power(chi, 2))
        print(f'EXACT n=3 character twist chi={chi}; Q={f}; L={lifted}; '
              'same matrix; all 81 cubics hold', flush=True)


def main():
    start = time.monotonic()
    for n in (3, 5, 7, 9, 11, 13):
        symbolic(n)
    for n in (3, 5, 7, 9):
        numeric(n)
    twist_example()
    print(f'elapsed_seconds={time.monotonic()-start:.3f}; '
          f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}')


if __name__ == '__main__':
    main()
