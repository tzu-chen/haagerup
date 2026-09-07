"""Exact reduced associators and the obstruction to their balanced HI extension.

The reduced rule omits alpha_(a-b) from rho_a rho_b. Its associators
are exact for every cyclic order, but do not supply rigid HI categories.
Symbolic checks below are exact; floating-point checks are regressions.
"""

from functools import cache
from itertools import product
import resource

import numpy as np
import sympy as sp
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import svds


def check_reduced_pentagons():
    """Check every type pattern over Z, with free fusion labels symbolic."""
    a, b, c, d, x, y, o = sp.symbols("a b c d x y o")

    def multiply(p, q, free):
        pt, pl = p
        qt, ql = q
        return (1, free) if pt == qt == 1 else (pt | qt, pl + (-1)**pt * ql)

    def rotate(p, q, r, out, left):
        if p[0] == q[0] == r[0] == 1:
            return (1, q[1] + out[1] - left[1])
        # There is a unique admissible right intermediate channel.
        return multiply(q, r, out[1] - p[1])

    for types in product((0, 1), repeat=4):
        aa, bb, cc, dd = zip(types, (a, b, c, d))
        xx = multiply(aa, bb, x)
        yy = multiply(xx, cc, y)
        oo = multiply(yy, dd, o)
        u = rotate(aa, bb, cc, yy, xx)
        v = rotate(aa, u, dd, oo, yy)
        w = rotate(bb, cc, dd, v, u)
        s = rotate(xx, cc, dd, oo, yy)
        t = rotate(aa, bb, s, oo, xx)
        assert w[0] == s[0] and v[0] == t[0]
        assert sp.expand(w[1] - s[1]) == 0
        assert sp.expand(v[1] - t[1]) == 0
    print("EXACT: all 16 reduced pentagon type patterns hold over Z")


def check_affine_uniqueness():
    """Replay a deduction valid modulo composite n as well as over fields."""
    A, B, C, D, E, K = sp.symbols("A B C D E K")
    a, b, c, d, o, x, y = sp.symbols("a b c d o x y")
    variables = (a, b, c, d, o, x, y)

    def f(a, b, c, out, left):
        return A*a + B*b + C*c + D*out + E*left + K

    u = f(a, b, c, y, x)
    v = f(a, u, d, o, y)
    w = f(b, c, d, v, u)
    s = f(x, c, d, o, y)
    t = f(a, b, s, o, x)
    p, q = sp.Poly(v-t, *variables), sp.Poly(w-s, *variables)
    coeff = lambda poly, var: poly.coeff_monomial(var)
    assert coeff(p, o) == -C*D
    assert sp.expand(coeff(q, c) + B*coeff(p, o)) == C*E
    # E is invertible, hence C=0. Each following cancellation is by a unit.
    assert sp.expand(coeff(p, x).subs(C, 0) - E*(B-1)) == 0
    assert coeff(p, a).subs(B, 1) == A
    assert coeff(p, y).subs({B: 1, C: 0}) == D+E
    assert sp.expand(coeff(q, o).subs(D, -E) - E*(E+1)) == 0
    assert coeff(p, 1).subs({B: 1, C: 0}) == K
    solution = {A: 0, B: 1, C: 0, D: 1, E: -1, K: 0}
    assert all(sp.expand(z.subs(solution)) == 0 for z in p.coeffs()+q.coeffs())
    print("EXACT: the unique invertible affine rule is f(a,b,c,o,x)=b+o-x")


def check_monomial_uniqueness():
    """Check mixed support equations and the finite-map lemma independently."""
    a, b, c, g, o, x, y = sp.symbols("a b c g o x y")
    raw_f = sp.Function("f")
    f = lambda *args: raw_f(*(sp.expand(arg) for arg in args))

    def multiply(p, q, free):
        pt, pl = p
        qt, ql = q
        return (1, free) if pt == qt == 1 else (pt | qt, pl+(-1)**pt*ql)

    def rotate(p, q, r, out, left):
        if p[0] == q[0] == r[0] == 1:
            return (1, f(p[1], q[1], r[1], out[1], left[1]))
        return multiply(q, r, out[1]-p[1])

    patterns = (
        ((0, g), (1, a), (1, b), (1, c)),
        ((1, a), (0, g), (1, b), (1, c)),
        ((1, a), (1, b), (0, g), (1, c)),
        ((1, a), (1, b), (1, c), (0, g)),
    )
    r0 = f(a, b, c, o-g, y-g)-f(a+g, b, c, o, y)
    r1 = f(a, b+g, c, o, y)-g-f(a-g, b, c, o, y)
    r2 = f(a, b-g, c, o, x-g)-f(a, b, c+g, o, x)
    r3 = f(a, b, c, o+g, x)-g-f(a, b, c-g, o, x)
    for labels, expected in zip(patterns, ((r0, 0), (r1, r1), (0, r2), (0, r3))):
        aa, bb, cc, dd = labels
        xx = multiply(aa, bb, x)
        yy = multiply(xx, cc, y if dd[0] else o+g)
        oo = multiply(yy, dd, o)
        u = rotate(aa, bb, cc, yy, xx)
        v = rotate(aa, u, dd, oo, yy)
        w = rotate(bb, cc, dd, v, u)
        s = rotate(xx, cc, dd, oo, yy)
        t = rotate(aa, bb, s, oo, xx)
        assert sp.expand(w[1]-s[1]-expected[0]) == 0
        assert sp.expand(v[1]-t[1]-expected[1]) == 0
    print("EXACT: all four mixed pentagons give the stated support covariances")

    # The proof uses range-translation invariance, then bijectivity of h.
    # Exhausting these small finite maps is an independent regression.
    for n in (3, 5, 7):
        solutions = []
        for h in product(range(n), repeat=n):
            if all(h[(h[(z+h[y]) % n]-y) % n] == (h[z]+h[y]-y) % n
                   for z in range(n) for y in range(n)):
                solutions.append(h)
        assert solutions == [tuple(range(n))]
        print(f"EXACT finite-map lemma regression: n={n}, {n**n} maps, only h(y)=y")


class BalancedExtension:
    def __init__(self, n):
        self.n = n
        self.d = (n + np.sqrt(n*n+4))/2
        self.t = 1/self.d
        self.s = 1/np.sqrt(self.d)

    @cache
    def fusion(self, a, b):
        at, ag = a
        bt, bg = b
        if at == bt == 1:
            return ((0, (ag-bg) % self.n),) + tuple((1, k) for k in range(self.n))
        return (((at+bt) % 2, (ag + (-1)**at * bg) % self.n),)

    @cache
    def channels(self, a, b, c, out):
        left = tuple(x for x in self.fusion(a, b) if out in self.fusion(x, c))
        right = tuple(y for y in self.fusion(b, c) if out in self.fusion(a, y))
        return left, right

    @cache
    def column(self, a, b, c, out, x):
        _, right = self.channels(a, b, c, out)
        if len(right) == 1 and not (a[0] == b[0] == c[0] == out[0] == 1):
            return ((right[0], 1.0),)
        special = out[1] == (a[1]-b[1]+c[1]) % self.n
        if not special:
            return (((1, (b[1]+out[1]-x[1]) % self.n), 1.0),)
        if x[0] == 0:
            return tuple((y, self.t if y[0] == 0 else self.s) for y in right)
        return tuple((y, self.s if y[0] == 0 else
                      float(y[1] == (b[1]+out[1]-x[1]) % self.n) - (1+self.t)/self.n)
                     for y in right)

    def basic(self, a, b, c, out):
        left, right = self.channels(a, b, c, out)
        rows = {y: j for j, y in enumerate(right)}
        matrix = np.zeros((len(right), len(left)))
        for j, x in enumerate(left):
            for y, value in self.column(a, b, c, out, x):
                matrix[rows[y], j] = value
        return left, right, matrix

    def paths(self, a, b, c, d, out):
        """Build all five rotation edges directly from fusion paths."""
        fusion = self.fusion
        bases = [
            [(x, y) for x in fusion(a, b) for y in fusion(x, c) if out in fusion(y, d)],
            [(u, y) for u in fusion(b, c) for y in fusion(a, u) if out in fusion(y, d)],
            [(u, w) for u in fusion(b, c) for w in fusion(u, d) if out in fusion(a, w)],
            [(z, w) for z in fusion(c, d) for w in fusion(b, z) if out in fusion(a, w)],
            [(x, z) for x in fusion(a, b) for z in fusion(c, d) if out in fusion(x, z)],
        ]
        F = self.column
        rotations = (
            lambda x, y: [((u, y), v) for u, v in F(a, b, c, y, x)],
            lambda u, y: [((u, w), v) for w, v in F(a, u, d, out, y)],
            lambda u, w: [((z, w), v) for z, v in F(b, c, d, w, u)],
            lambda x, y: [((x, z), v) for z, v in F(x, c, d, out, y)],
            lambda x, z: [((z, w), v) for w, v in F(a, b, z, out, x)],
        )
        matrices = []
        for i, j, rotate in zip((0, 1, 2, 0, 4), (1, 2, 3, 4, 3), rotations):
            index = {key: k for k, key in enumerate(bases[j])}
            rows, cols, values = [], [], []
            for col, key in enumerate(bases[i]):
                for target, value in rotate(*key):
                    rows.append(index[target])
                    cols.append(col)
                    values.append(value)
            matrices.append(coo_matrix((values, (rows, cols)),
                                      shape=(len(bases[j]), len(bases[i]))).tocsr())
        long = matrices[2] @ matrices[1] @ matrices[0]
        short = matrices[4] @ matrices[3]
        return bases, long, short


def check_trials():
    # Exhaustive unitarity at n=3, including every mixed and unit input.
    trial = BalancedExtension(3)
    objects = tuple(product((0, 1), range(3)))
    for a, b, c, out in product(objects, repeat=4):
        left, _, matrix = trial.basic(a, b, c, out)
        if left:
            assert np.linalg.norm(matrix.T @ matrix - np.eye(len(left)), 2) < 1e-12
    print("NUMERICAL: all associator blocks unitary at n=3")

    # Check both cup weights, using each simple object's actual dual.
    def dual(a):
        return a if a[0] else (0, -a[1] % 3)

    dim = lambda a: trial.d if a[0] else 1.0
    one = (0, 0)
    for a, b in product(objects, repeat=2):
        for z in trial.fusion(a, b):
            left, right, first = trial.basic(dual(a), a, b, b)
            left2, right2, second = trial.basic(b, dual(z), z, b)
            weight1 = dim(a)**2 * abs(first[right.index(z), left.index(one)])**2
            weight2 = dim(z)**2 * abs(second[right2.index(one), left2.index(dual(a))])**2
            assert abs(weight1-weight2) < 1e-12
    print("NUMERICAL: every scalar balance summand agrees at n=3")

    # At n=1 the extension is the usual Fibonacci associator.
    fibonacci = BalancedExtension(1)
    for labels in product(((0, 0), (1, 0)), repeat=5):
        _, long, short = fibonacci.paths(*labels)
        assert np.linalg.norm((long-short).toarray()) < 1e-12
    print("NUMERICAL: all Fibonacci pentagons pass at n=1")

    rho = (1, 0)
    for n in (3, 5, 7, 9, 11, 15, 23):
        trial = BalancedExtension(n)
        for k in range(1, n):
            bases, long, short = trial.paths(rho, rho, rho, rho, (0, k))
            assert len(bases[0]) == n
            target = {pair[0][1]: j for j, pair in enumerate(bases[3])}
            # These entries are 0/1, so this checks the permutations exactly.
            for col, (x, _) in enumerate(bases[0]):
                lc, sc = long.getcol(col), short.getcol(col)
                assert lc.nnz == sc.nnz == 1
                assert lc[target[(x[1]-2*k) % n], 0] == 1
                assert sc[target[(x[1]-k) % n], 0] == 1
            order = n // int(sp.gcd(n, k))
            expected = 2*np.cos(np.pi/(2*order))
            actual = np.linalg.norm((long-short).toarray(), 2)
            assert abs(actual-expected) < 2e-12
            if k == 1:
                # Arbitrary phases retain a weighted n-cycle in short* long.
                rng = np.random.default_rng(8800+n)
                for _ in range(8):
                    phase1 = np.exp(1j*rng.uniform(-np.pi, np.pi, n))
                    phase2 = np.exp(1j*rng.uniform(-np.pi, np.pi, n))
                    rephased = long.toarray()*phase1 - short.toarray()*phase2
                    assert np.linalg.norm(rephased, 2) >= expected-2e-12
        # A second output type checks the augmented blocks in the path engine.
        _, long, short = trial.paths(rho, rho, rho, rho, (1, 0))
        defect = long-short
        if defect.shape[0] < 200:
            sampled = np.linalg.norm(defect.toarray(), 2)
        else:
            sampled = float(svds(defect, k=1, return_singular_vectors=False,
                                rng=np.random.default_rng(8801))[0])
        print(f"n={n}: invertible-output lower bound={2*np.cos(np.pi/(2*n)):.12f}; "
              f"one noninvertible-output defect={sampled:.12f}; threshold="
              f"{min(1/130, 1/(4*trial.d)):.12f}")
        # functools.cache on bound methods otherwise retains earlier trials.
        trial.fusion.cache_clear()
        trial.channels.cache_clear()
        trial.column.cache_clear()


if __name__ == "__main__":
    check_reduced_pentagons()
    check_affine_uniqueness()
    check_monomial_uniqueness()
    check_trials()
    print(f"Peak RSS: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.1f} MiB")
    print("COMPLETE: reduced construction and uniform extension obstruction; NO HI INFINITUDE CLAIM")
