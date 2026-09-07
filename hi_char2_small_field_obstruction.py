"""Exact checks for the uniform small-field obstruction in Section 64.

The proof in the notes excludes every Frobenius-covariant phase solution
over F_4, and every inflation constant on nonzero cosets of a proper
nontrivial subgroup, in characteristic two. The finite tests below check
the off-solution identities used in that proof. They do not replace it.

An independent exhaustive F_16 search at 3, 11 and 43 records the limits
of the next-smallest-field ansatz. Only quadratics are searched; complete
cubic certificates for 3 and 11 already exist elsewhere in the workspace.
Requires only the Python standard library.
"""

from itertools import product
from random import Random


def field_table(degree, modulus):
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
    return [[multiply(a, b) for b in range(1 << degree)]
            for a in range(1 << degree)]


def power(table, a, exponent):
    result = 1
    while exponent:
        if exponent & 1:
            result = table[result][a]
        a = table[a][a]
        exponent >>= 1
    return result


def quadratic(table, phases, g, h):
    n, result = len(phases), 0
    for m in range(n):
        first = table[phases[m]][phases[(h-m) % n]]
        second = table[phases[(-m-g) % n]][phases[(m+g-h) % n]]
        result ^= table[first][second]
    return result


def doubled_orbits(n):
    orbits, seen = [], {0}
    for a in range(1, n):
        if a in seen:
            continue
        orbit, b = set(), a
        while b not in orbit:
            orbit.add(b)
            b = 2*b % n
        negative = {-b % n for b in orbit}
        seen |= orbit | negative
        orbits.append((orbit, negative, orbit == negative))
    return orbits


def check_f4_identities():
    table = field_table(2, 0b111)
    delta, c = 2, 3
    square = lambda a: table[a][a]
    trace = lambda a: a ^ square(a)
    rng = Random(634)

    for n in [3, 7, 9, 11, 15, 23, 31, 47, 71, 79, 103, 127]:
        orbits = doubled_orbits(n)

        def make(digits):
            phases = [1]*n
            for (orbit, negative, fixed), value in zip(orbits, digits):
                value = c if fixed else value
                for a in orbit:
                    phases[a] = value
                for a in negative:
                    phases[a] = table[delta][square(value)]
            assert all(phases[2*a % n] == phases[a]
                       and table[phases[a]][phases[-a]] == delta
                       for a in range(1, n))
            return phases

        diagonal_checks = trace_checks = witnesses = 0
        assignments = (product([1, delta, c], repeat=len(orbits))
                       if len(orbits) < 5 else
                       [tuple(rng.choice([1, delta, c]) for _ in orbits)
                        for _ in range(32)])
        for digits in assignments:
            phases = make(digits)
            for g in range(1, n):
                triple = 0
                for m in range(n):
                    triple ^= table[table[phases[m]][phases[(m-g) % n]]][phases[(m+g) % n]]
                pair = phases[g] ^ phases[-g]
                q = quadratic(table, phases, g, g)
                assert q == table[c][square(triple)] ^ pair
                assert triple ^ delta ^ square(pair) in [0, 1]
                if phases[g] == c:
                    assert q != 0
                    diagonal_checks += 1

        assignments = (product([1, delta], repeat=len(orbits))
                       if len(orbits) < 7 else
                       [tuple(rng.choice([1, delta]) for _ in orbits)
                        for _ in range(32)])
        for digits in assignments:
            phases = make(digits)
            if c in phases:
                continue
            f = [int(value == delta) for value in phases]
            parity = ((n-1)//2) % 2
            assert all(sum(f[t]*f[(t+a) % n] for t in range(n)) % 2 == parity
                       for a in range(n))
            pairs = (product(range(1, n), repeat=2) if n < 32 else
                     [(rng.randrange(1, n), rng.randrange(1, n)) for _ in range(64)])
            for g, h in pairs:
                if (g-h) % n == 0 or (g+h) % n == 0:
                    continue
                x, y, z, v = f[g], f[h], f[(h-g) % n], f[(h+g) % n]
                expected = y ^ ((x ^ y) & z) ^ ((x ^ y ^ 1) & v)
                q = quadratic(table, phases, g, h)
                assert trace(table[delta][q]) == expected
                trace_checks += 1

            # A failed addition inside the phase class gives a specific
            # nonzero quadratic, without evaluating every quadratic.
            a = next(a for a in range(1, n) if f[a])
            k = 2
            while f[k*a % n]:
                k += 1
            g, h = (k-1)*a % n, a
            assert f[g] == f[h] == 1 and f[(g+h) % n] == 0
            assert g != h and (g+h) % n != 0
            assert trace(table[delta][quadratic(table, phases, g, h)]) == 1
            witnesses += 1
        print(f'F4 n={n}: diagonal exclusions={diagonal_checks}; '
              f'off-solution trace identities={trace_checks}; '
              f'explicit failed-Q witnesses={witnesses}', flush=True)


def check_f16_search():
    table = field_table(4, 0b10011)
    delta, xi = power(table, 2, 5), power(table, 2, 3)
    c = delta ^ 1
    assert power(table, delta, 3) == power(table, xi, 5) == 1
    values = [table[c][power(table, xi, i)] for i in range(5)]
    for n, expected in [(3, 2), (11, 2), (43, 0)]:
        orbits = doubled_orbits(n)
        assert all(fixed and len(orbit) % 4 == 2
                   for orbit, _, fixed in orbits)
        # Here -a occurs after an odd number of doublings. Consequently
        # W_a W_-a = W_a^5 = delta, so these five values are exhaustive.
        winners = []
        for digits in product(range(5), repeat=len(orbits)):
            phases = [1]*n
            for (orbit, _, _), digit in zip(orbits, digits):
                a, value = min(orbit), values[digit]
                for _ in orbit:
                    phases[a] = value
                    a, value = 2*a % n, power(table, value, 4)
            assert all(table[phases[a]][phases[-a]] == delta
                       and phases[2*a % n] == power(table, phases[a], 4)
                       for a in range(1, n))
            if all(quadratic(table, phases, g, h) == 0
                   for h in range(1, n) for g in range(1, n)):
                winners.append(digits)
        assert len(winners) == expected
        print(f'F16 n={n}: exhaustive candidates={5**len(orbits)}; '
              f'all-Q winners={winners}', flush=True)


def check_inflation_identities():
    table = field_table(4, 0b10011)
    delta, rng = power(table, 2, 5), Random(641)

    def norm_phases(length):
        phases = [1]*length
        for a in range(1, (length+1)//2):
            phases[a] = rng.randrange(1, 16)
            phases[-a] = table[delta][power(table, phases[a], 14)]
        return phases

    for quotient, kernel in [(3, 3), (3, 5), (3, 7), (3, 9), (5, 7), (7, 9)]:
        n, comparisons = quotient*kernel, 0
        for _ in range(4):
            outer, inner = norm_phases(quotient), norm_phases(kernel)
            phases = [inner[a//quotient] if a % quotient == 0
                      else outer[a % quotient] for a in range(n)]
            for a in range(1, kernel):
                g = quotient*a
                half = a*((kernel+1)//2) % kernel
                pair = power(table, inner[half], 2) ^ power(table, inner[-half], 2)
                mixed = table[delta][pair] ^ table[delta][delta]
                for h in range(1, n):
                    expected = (quadratic(table, inner, a, h//quotient)
                                if h % quotient == 0 else mixed)
                    assert quadratic(table, phases, g, h) == expected
                    comparisons += 1
        print(f'Inflation |G|={n}, |K|={kernel}: '
              f'all {comparisons} off-solution identities passed', flush=True)


if __name__ == '__main__':
    check_f4_identities()
    check_inflation_identities()
    check_f16_search()
    print('ALL EXACT CHECKS PASSED; the uniform obstruction is proved in Section 64.')
