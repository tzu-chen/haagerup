#!/usr/bin/env python3
"""Exact checks of small textbook examples, not of the full CFT construction.

Run only under the central research guard, from this textbook directory:
  ~/.local/bin/research-safe-run --limit-mib 256 --memory-mib 256 \
      --threads 1 -- timeout 90s python3 check_examples.py

Allocation estimate: a fixed degree-12 rational field, a 12-by-12 matrix,
and at most 936 cached field elements, each with twelve rational entries.
Arithmetic data are below 16 MiB; interpreter and output overhead bring
the conservative expected peak below 64 MiB. No NumPy, BLAS, workers,
large lattices, eigenproblems, or research certificate replays are used.
The larger 256 MiB cap provides headroom while imposing a small hard budget.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import os
import resource
import time


if not os.environ.get("RESEARCH_SAFE_RUN_ACTIVE"):
    raise SystemExit("Use the canonical research-safe-run; no unguarded computation.")


class C13:
    """Q[z]/(1+z+...+z^12), using coefficients of powers zero through eleven."""
    __slots__ = ("a",)

    def __init__(self, value=0):
        if isinstance(value, C13):
            self.a = value.a
        elif isinstance(value, (int, F)):
            self.a = (F(value),) + (F(0),) * 11
        else:
            assert len(value) == 12
            self.a = tuple(F(x) for x in value)

    def __add__(self, other):
        other = C13(other)
        return C13(tuple(x + y for x, y in zip(self.a, other.a)))

    __radd__ = __add__

    def __neg__(self):
        return C13(tuple(-x for x in self.a))

    def __sub__(self, other):
        return self + (-C13(other))

    def __rsub__(self, other):
        return C13(other) - self

    def __mul__(self, other):
        other = C13(other)
        # First use z^13=1, then eliminate z^12 by Phi_13(z)=0.
        out = [F(0)] * 13
        for i, x in enumerate(self.a):
            if x:
                for j, y in enumerate(other.a):
                    if y:
                        out[(i + j) % 13] += x * y
        return C13(tuple(out[k] - out[12] for k in range(12)))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, (int, F)):
            raise TypeError("Only rational division is used in this checker.")
        return self * (F(1) / other)

    def __pow__(self, n):
        assert n >= 0
        out, base = C13(1), self
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n //= 2
        return out

    def __eq__(self, other):
        return self.a == C13(other).a

    def integer(self):
        assert all(x == 0 for x in self.a[1:]), self.a
        assert self.a[0].denominator == 1, self.a
        return int(self.a[0])


def zeta_power(n):
    n %= 13
    if n == 12:
        return C13((-1,) * 12)
    return C13(tuple(int(k == n) for k in range(12)))


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def cyclotomic_examples():
    residues = {k * k % 13 for k in range(1, 13)}
    r = sum((1 if k in residues else -1) * zeta_power(k)
            for k in range(1, 13))
    assert r * r == 13
    d = (3 + r) / 2
    di = d - 3
    s = 1 + d * d
    big_d = 3 * s
    assert d * d == 1 + 3 * d
    assert d * di == 1
    assert 1 + d ** 4 + 4 * s ** 2 + 54 * d ** 2 == big_d ** 2
    a, b, u, v = C13(F(1, 6)) - r / 26, C13(F(1, 6)) + r / 26, C13(F(1, 3)), r / 13
    middle = [[2, -1, -1, -1], [-1, 2, -1, -1],
              [-1, -1, -1, 2], [-1, -1, 2, -1]]
    matrix = [[C13() for _ in range(12)] for _ in range(12)]
    matrix[0][0], matrix[1][1] = a, a
    matrix[0][1], matrix[1][0] = b, b
    for j in range(2, 6):
        matrix[0][j] = matrix[j][0] = u
        matrix[1][j] = matrix[j][1] = u
        for k in range(2, 6):
            matrix[j][k] = C13(F(middle[j - 2][k - 2], 3))
    for j in range(6, 12):
        matrix[0][j] = matrix[j][0] = v
        matrix[1][j] = matrix[j][1] = -v
        for k in range(6, 12):
            power = (j - 5) * (k - 5)
            matrix[j][k] = -v * (zeta_power(power) + zeta_power(-power))
    square = matmul(matrix, matrix)
    assert all(square[i][j] == int(i == j) for i in range(12) for j in range(12))
    inv_vacuum = [big_d, big_d * di ** 2] + [C13(3)] * 4 + [r] * 6
    assert all(matrix[0][j] * inv_vacuum[j] == 1 for j in range(12))
    fusion = [[[0] * 12 for _ in range(12)] for _ in range(12)]
    for i in range(12):
        for j in range(i, 12):
            pair = [matrix[i][k] * matrix[j][k] * inv_vacuum[k]
                    for k in range(12)]
            for ell in range(12):
                value = sum(pair[k] * matrix[ell][k] for k in range(12)).integer()
                assert value >= 0
                fusion[i][j][ell] = fusion[j][i][ell] = value
    assert all(fusion[0][i][j] == int(i == j) for i in range(12) for j in range(12))
    assert fusion[4][4][4] == 2
    talpha = [C13(1), C13(1), C13(-1)] + [C13()] * 9
    trho = [d, -di] + [C13()] * 10
    assert [sum(x * y for x, y in zip(row, talpha)) for row in matrix] == [
        C13(int(i in (3, 4, 5))) for i in range(12)]
    assert [sum(x * y for x, y in zip(row, trho)) for row in matrix] == [
        C13(int(i > 0)) for i in range(12)]
    return {"S_squared_identity": True, "nonnegative_integer_Verlinde_entries": 1728,
            "c1_c1_c1": fusion[4][4][4], "twined_to_twisted_vectors": 2}


def rational_examples():
    # Virasoro Gram matrix and the Ising null direction.
    c, h = F(1, 2), F(1, 16)
    g = [[4 * h + c / 2, 6 * h], [6 * h, 4 * h * (2 * h + 1)]]
    null = [F(1), F(-4, 3)]
    assert all(sum(x * y for x, y in zip(row, null)) == 0 for row in g)
    # Parafermion W_4 norm, using both subtraction and closed formula.
    gamma = []
    for c, lam in [(F(4, 5), F(4, 13)), (F(8, 5), F(14, 473))]:
        q = 5 * c + 22
        n = c / 3
        b = n * (31 - 16 * lam * (c + 2))
        subtract = (b - 9 * c / 5 - 512 * c / (5 * q)) / n ** 2
        formula = 48 * (c + 2) * (8 - lam * q) / (c * q)
        assert subtract == formula
        gamma.append(formula)
    assert gamma == [F(0), F(60552, 2365)]
    # Global-block triangular subtraction.
    assert F(65, 3) - F(2, 3) - F(21, 5) - F(29, 3) == F(107, 15)
    # Exact neutral/charged crossing at several rational points.
    def g0(x):
        return (3 - 4 * x + 4 * x ** 2) / (3 * x ** 4 * (1 - x) ** 4)
    def gp(x):
        return x ** 2 * (4 - 4 * x + 3 * x ** 2) / (3 * (1 - x) ** 4)
    for x in (F(1, 7), F(2, 5), F(1, 2), F(8, 3)):
        assert g0(1 - x) == g0(x)
        assert gp(x) == x ** -4 * g0(1 / x)
    assert g0(F(1, 2)) == F(512, 3) and gp(F(1, 2)) == F(11, 3)
    # Residual light-sector Gram eigenvectors, all exactly rational.
    q = [2, 0, -2]
    k = [[F(int(i == j)) - F(1, 3) - F(q[i] * q[j], 78)
          for j in range(3)] for i in range(3)]
    for vector, eigenvalue in [([1, 1, 1], F(0)), ([1, 0, -1], F(35, 39)),
                               ([1, -2, 1], F(1))]:
        assert [sum(x * y for x, y in zip(row, vector)) for row in k] == [
            eigenvalue * x for x in vector]
    # Character and full-spectrum arithmetic.
    assert 8 + 64 + 36 + 288 + 330 == 726
    assert 17520 + 6720 * 8 + 2160 * 44 + 240 * 192 + 726 == 213126
    assert sum(x * x for x in (3, 5, 7, 13, 14, 27, 42)) == 2941
    assert 80 ** 2 + 81 ** 2 + 81 ** 2 + 6 ** 2 == 19558
    assert 248 ** 2 + 2 * 3875 + 2 * 248 + 2 == 69752
    for states, primaries in [
        ([80, 1250, 10630, 65042], [80, 1170, 9300, 53162]),
        ([5, 229, 2738, 19942], [5, 224, 2504, 16975]),
    ]:
        partitions = [1, 1, 2, 3]
        assert [sum(primaries[j] * partitions[n - j] for j in range(n + 1))
                for n in range(4)] == states
    return {"Ising_null": True, "weight_four_couplings": [str(x) for x in gamma],
            "light_Gram_eigenvalues": ["0", "35/39", "1"],
            "character_and_spectrum_arithmetic": True,
            "rational_crossing_samples": 4}


def main():
    start = time.monotonic()
    output = {
        "scope": "Small exact textbook examples only; no all-weight CFT certificate",
        "rational": rational_examples(),
        "cyclotomic": cyclotomic_examples(),
        "seconds": round(time.monotonic() - start, 3),
        "max_rss_mib": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 3),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "guard_sha256": hashlib.sha256(Path.home().joinpath(".local/bin/research-safe-run").read_bytes()).hexdigest(),
    }
    destination = Path(__file__).resolve().parent / "editorial/example_check_results.json"
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
