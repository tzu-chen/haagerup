"""Full transparent pentagon residuals, including deliberately false trials.

The exact index identities support Section 90's uniform proof. Numerical
checks use both dimension roots and arbitrary order-three symmetric cores;
they do not impose Q or C and do not assert new HI existence.
"""

from functools import cache
from itertools import product
from fractions import Fraction
from pathlib import Path
import re
import resource

import numpy as np
import sympy as sp

from hi_reduced_affine_associator import BalancedExtension


class TransparentTrial(BalancedExtension):
    def __init__(self, n, delta, core):
        super().__init__(n)
        self.delta = complex(delta)
        self.t = 1 / self.delta
        self.s = 1 / np.sqrt(self.delta)
        self.A = np.asarray(core, dtype=complex)

    @cache
    def column(self, a, b, c, out, x):
        _, right = self.channels(a, b, c, out)
        if not all(z[0] for z in (a, b, c, out)):
            return ((right[0], 1.0),)
        g = (out[1] + b[1] - a[1] - c[1]) % self.n
        return tuple((y, self.t if x[0] == y[0] == 0 else
                      self.s if x[0] * y[0] == 0 else
                      self.A[g, (x[1] + y[1] - a[1] - c[1]) % self.n])
                     for y in right)

    def basic(self, a, b, c, out):
        left, right = self.channels(a, b, c, out)
        f = np.zeros((len(right), len(left)), dtype=complex)
        for j, x in enumerate(left):
            for y, value in self.column(a, b, c, out, x):
                f[right.index(y), j] = value
        return left, right, f

    def residuals(self):
        n, A, t = self.n, self.A, self.t
        Q = np.empty((n, n), dtype=complex)
        C = np.empty((n,) * 4, dtype=complex)
        for g, h in product(range(n), repeat=2):
            Q[g, h] = sum(A[(g + m) % n, h] * A[h, m] for m in range(n)) - (g == 0) + t * (h == 0)
        for g, h, k, l in product(range(n), repeat=4):
            C[g, h, k, l] = sum(A[m, (g + h) % n] * A[g, (m + k) % n] * A[h, (m + l) % n] for m in range(n)) - A[(g + l) % n, k] * A[(h + k) % n, l] + t * (g == h == 0)
        return Q, C

    def predicted_entry(self, inputs, output, left, right, Q, C):
        if not all(a[0] for a in inputs):
            return 0j
        a, b, c, d = (a[1] for a in inputs)
        x, y = left
        z, w = right
        n, o = self.n, output[1]
        if output[0] == 0:
            if x[0] == z[0] == 1:
                return Q[(z[1] - x[1] + o) % n, (o + d + b - a - c) % n]
            return 0j
        if y[0] == 0 or w[0] == 0 or x[0] == z[0] == 0:
            return 0j
        g, h = (y[1] + b - a - c) % n, (w[1] + c - b - d) % n
        if x[0] == 0:
            l = (z[1] - o + a - b) % n
            return self.s * Q[-l % n, h]
        if z[0] == 0:
            k = (x[1] - o + d - c) % n
            return self.s * Q[-k % n, g]
        k, l = (x[1] - o + d - c) % n, (z[1] - o + a - b) % n
        return C[g, h, k, l]


def exact_indices():
    a, b, c, d, o, x, y, z, w, u = sp.symbols("a b c d o x y z w u")
    g, h = y + b - a - c, w + c - b - d
    k, l, m = x - o + d - c, z - o + a - b, o + u - a - d
    equal = lambda p, q: sp.expand(p - q) == 0
    assert equal(g + h, y + w - a - d)
    assert equal(m + k, x + u - a - c)
    assert equal(m + l, u + z - b - d)
    # Apply A(r,s)=A(-s,r-s) to the two short-path factors.
    assert equal(-k, o + c - x - d)
    assert equal(g + l - k, y + z - x - d)
    assert equal(-l, o + b - a - z)
    assert equal(h + k - l, x + w - a - z)
    # Unit-channel specializations and the invertible-output convolution.
    assert equal(g.subs(y, a - b + c), 0)
    assert equal(h.subs(w, b - c + d), 0)
    assert equal(k.subs(x, o - d + c), 0)
    assert equal(l.subs(z, b - a + o), 0)
    gout = o + d + b - a - c
    assert equal(z - x + a + c - b - d + gout, z - x + o)
    delta, n = sp.symbols("delta n")
    t, axis = 1 / delta, -1 / (delta - 1)
    reduction = {n: (delta * delta - 1) / delta}
    assert sp.cancel((1 + n * axis + t).subs(reduction)) == 0
    assert sp.cancel((n * t + t * t - 1).subs(reduction)) == 0
    print("EXACT: generic C indices, unit-channel specializations, inverse Q indices, and exceptional-row cancellations")


def random_core(n, delta, rng):
    core = np.zeros((n, n), dtype=complex)
    visited = set()
    for g, h in product(range(n), repeat=2):
        if (g, h) in visited:
            continue
        orbit = ((g, h), (-h % n, (g - h) % n), ((h - g) % n, -g % n))
        value = ((delta - 2) / (delta - 1) if g == h == 0 else
                 -1 / (delta - 1) if g == 0 or h == 0 or g == h else
                 rng.normal() + 1j * rng.normal())
        for p in orbit:
            core[p] = value
            visited.add(p)
    return core


def run():
    exact_indices()
    rng = np.random.default_rng(9001)
    for n, root in ((3, "negative"), (3, "positive"), (5, "negative"), (7, "negative")):
        d = (n + np.sqrt(n * n + 4)) / 2
        delta = -1 / d if root == "negative" else d
        trial = TransparentTrial(n, delta, random_core(n, delta, rng))
        Q, C = trial.residuals()
        assert np.max(np.abs(Q)) > 0.1 and np.max(np.abs(C)) > 0.1
        objects = tuple(product((0, 1), range(n)))
        if n == 3 and root == "negative":
            tuples = product(objects, repeat=5)
        else:
            tuples = [tuple(objects[i] for i in rng.integers(0, 2 * n, size=5)) for _ in range(100)]
            tuples += [((1, 0),) * 4 + (o,) for o in objects]
            tuples += [tuple((1, int(i)) for i in rng.integers(0, n, size=4)) + (o,)
                       for o in objects for _ in range(3)]
        count, entries, worst = 0, 0, 0.0
        for labels in tuples:
            inputs, out = labels[:4], labels[4]
            bases, long, short = trial.paths(*inputs, out)
            actual = (long - short).toarray()
            predicted = np.array([[trial.predicted_entry(inputs, out, left, right, Q, C)
                                   for left in bases[0]] for right in bases[3]], dtype=complex).reshape(actual.shape)
            error = float(np.max(np.abs(actual - predicted))) if actual.size else 0.0
            assert error < 2e-10
            worst = max(worst, error)
            count += 1
            entries += actual.size
        rho = (1, 0)
        for g in range(n):
            _, _, f = trial.basic(rho, rho, rho, (1, g))
            if g == 0:
                assert np.linalg.norm(f @ f - np.eye(n + 1), 2) < 3e-13
                if root == "negative":
                    assert abs(np.linalg.norm(f, 2) - (d + np.sqrt(n * d))) < 2e-13
            else:
                fourier_norm = np.max(np.abs(np.fft.fft(trial.A[g])))
                assert abs(np.linalg.norm(f, 2) - fourier_norm) < 3e-13
                candidate = np.array([[trial.A[-g % n, (i + j - g) % n]
                                       for j in range(n)] for i in range(n)])
                error = np.array([[Q[(j - i) % n, g] for j in range(n)] for i in range(n)])
                assert np.linalg.norm(f @ candidate - np.eye(n) - error, 2) < 3e-12
        print("TRANSPARENT_RESIDUAL_REGRESSION", n, root, "pentagons", count, "entries", entries,
              "Q_magnitude", np.max(np.abs(Q)), "C_magnitude", np.max(np.abs(C)),
              "identity_error", worst, flush=True)
        trial.fusion.cache_clear()
        trial.channels.cache_clear()
        trial.column.cache_clear()
    # Replay the correction inequality with exact rational arithmetic on
    # outward printed bounds. The interval construction supplies the bounds;
    # this separate check verifies their implication without FLINT arithmetic.
    log = Path(__file__).with_name("hi_shintani_correction_results.txt").read_text()
    assert "COMPLETE: certified candidate and residual enclosures" in log
    for n in (3, 7, 11):
        pattern = rf"CORRECTION n={n} M0_upper=\[([^ ]+) \+/- ([^\]]+)\]"
        midpoint, radius = re.search(pattern, log).groups()
        m0 = Fraction(midpoint) + Fraction(radius)
        errors = []
        for kind in ("Q", "C"):
            match = re.search(rf"ENCLOSURE n={n} {kind} count=\d+ every residual lies in \[\+/- ([^\]]+)\]", log)
            errors.append(Fraction(match[1]))
        eq, ec = errors
        assert n * eq < 1
        # sqrt(d) < n+1 is deliberately coarser, but rational and sufficient.
        q = (n * n + 2) * m0 * m0 * max(ec, (n + 1) * eq)
        ratio = 870 * (2 * m0) ** 14 * q
        rigidity = 2 * (2 * m0) ** 3 * q
        assert ratio < 1 and rigidity < 1
        print("EXACT_RATIONAL_CORRECTION_REPLAY", n, "sufficient_ratio_less_than",
              (ratio.numerator * 10**16 // ratio.denominator + 1) / 10**16,
              "rigidity_margin_passed", flush=True)
    print(f"Peak RSS: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.1f} MiB")
    print("COMPLETE: transparent residual identities and inverse bounds; NO INFINITUDE CLAIM")


if __name__ == "__main__":
    run()
