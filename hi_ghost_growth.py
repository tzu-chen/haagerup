"""Uniform ghost-amplitude growth and fusion-gauge invariants.

The proofs are in Section 91. Exact finite multiset checks and independent
double-sine integral regressions below do not assert HI infinitude.
"""

from collections import Counter
from itertools import product
import resource

import mpmath as mp
import sympy as sp

from hi_shintani_ghost import log_double_sine


def lobachevsky(x):
    if x == 0 or x == 1:
        return mp.mpf(0)
    return mp.im(mp.polylog(2, mp.exp(2j * mp.pi * x))) / (2 * mp.pi)


def log_sample(n, a):
    d = (n + mp.sqrt(n * n + 4)) / 2
    return log_double_sine(1 + a * d / (d + 1), d)


def exact_checks():
    d, theta = sp.symbols("d theta", positive=True)
    n = d - 1 / d
    shifted = n * theta / (d + 1) + 1 / (2 * d)
    assert sp.cancel(shifted - theta - (sp.Rational(1, 2) - theta) / d) == 0
    # The gauge action is a ratio of four trivalent-basis changes.
    # For each fixed core position all four multisets are the entire
    # noninvertible trivalent vertex set, each with multiplicity n.
    for order in (3, 5, 7):
        expected = Counter({vertex: order for vertex in product(range(order), repeat=3)})
        for g, h in product(range(order), repeat=2):
            counts = [Counter() for _ in range(4)]
            for a, b, c, x in product(range(order), repeat=4):
                o = (g - b + a + c) % order
                y = (h - x + a + c) % order
                for counter, vertex in zip(counts, ((a, b, x), (x, c, o), (b, c, y), (a, y, o))):
                    counter[vertex] += 1
            assert all(counter == expected for counter in counts)
        print("EXACT_GAUGE_MULTISET", order, "all core positions; invariant product degree", order**4, flush=True)
    # Coefficient majorant behind 1-v/sinh(v) <= v^2/6.
    factorial = 1
    for k in range(1, 30):
        factorial = int(sp.factorial(2 * k + 1))
        assert factorial >= 6**k
    print("EXACT: centered sampling identity and elementary hyperbolic-kernel majorant")


def run():
    exact_checks()
    mp.mp.dps = 45
    fthird = lobachevsky(mp.mpf(1) / 3)
    kappa = 3 * fthird
    print("kappa=3*f(1/3)=", mp.nstr(kappa, 35), flush=True)
    for n in (3, 7, 11, 31, 101, 301, 1001):
        d = (n + mp.sqrt(n * n + 4)) / 2
        balanced = (n // 3, (n + 1) // 3, (n + 2) // 3)
        assert sum(balanced) == n
        labels = set(balanced) | {1, max(1, n // 6), (n - 1) // 2}
        if n <= 31:
            labels |= set(range(1, (n + 1) // 2))
        values = {a: log_sample(n, mp.mpf(a)) for a in labels}
        worst = mp.mpf(0)
        for a in labels:
            theta = mp.mpf(a) / n
            x = theta + (mp.mpf('0.5') - theta) / d
            remainder = values[a] - d * lobachevsky(x)
            upper = min(mp.log(2) / 2, mp.pi * abs(mp.cot(mp.pi * x)) / (24 * d))
            assert -mp.mpf('1e-38') <= remainder <= upper + mp.mpf('1e-38')
            assert remainder <= mp.mpf(1) / 12
            uniform = mp.log(n) / 2 + mp.pi / (12 * d) + mp.mpf(1) / 12
            assert abs(values[a] - n * lobachevsky(theta)) <= uniform
            worst = max(worst, remainder)
        log_gamma = sum(values[a] for a in balanced) - mp.log(d) / 2 - mp.log(1 + 1 / d)
        uniform = mp.log(n) / 2 + mp.pi / (12 * d) + mp.mpf(1) / 12
        prefactor = mp.log(d) / 2 + mp.log(1 + 1 / d)
        assert kappa*n - 3*uniform - mp.mpf(5)/(3*n) - prefactor <= log_gamma
        assert log_gamma <= kappa*n + 3*uniform - prefactor
        assert log_gamma <= kappa*n + mp.log(2) - mp.log(n)/2
        if n <= 31:
            values[0] = mp.log(d) / 2
            values[n] = -values[0]
            for a in range((n + 1) // 2, n):
                values[a] = -values[n - a]
            sums = [values[a] + values[b] + values[n - a - b]
                    for a in range(n + 1) for b in range(n - a + 1)]
            assert abs(max(sums) - sum(values[a] for a in balanced)) < mp.mpf('1e-35')
            assert abs(min(sums) - mp.log(d) / 2) < mp.mpf('1e-35')
        normalized = mp.exp(log_gamma + mp.log(n) / 2 - kappa * n)
        print("GHOST_GROWTH_REGRESSION", n, "log_Gamma", mp.nstr(log_gamma, 16),
              "log_Gamma_over_n", mp.nstr(log_gamma / n, 14),
              "scaled_Gamma", mp.nstr(normalized, 14),
              "limit", mp.nstr(3 ** (-mp.mpf(1) / 4), 14),
              "max_centered_remainder", mp.nstr(worst, 8), flush=True)
    for value in ('0.0001', '0.1', '1', '2', '3', '10', '100'):
        v = mp.mpf(value)
        assert 0 <= 1 - v / mp.sinh(v) <= min(1, v*v/6)
    print(f"Peak RSS: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.1f} MiB")
    print("COMPLETE: uniform growth and gauge obstruction checks; NO INFINITUDE CLAIM")


if __name__ == "__main__":
    run()
