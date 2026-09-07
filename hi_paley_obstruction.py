"""Exact classification of the real two-value quadratic-character ansatz.

The necessary quadratic identities restrict prime orders p == 3 mod 4
to p = 3 or 11. Both remaining real branches pass every Q and C equation.
This rules out this particular route to infinitude; it does not rule out HI.
"""

from itertools import product
import time

import sympy as sp


def character_sum_checks():
    a, b = sp.symbols("a b")
    for p in [3, 7, 11, 19, 23, 31, 43]:
        chi = lambda j: int(sp.legendre_symbol(j % p, p))
        c = [sp.Integer(-1)] + [a + b * chi(j) for j in range(1, p)]
        correction = -1 - a
        for lam in range(1, p):
            actual = sum(c[j] * c[(1-j) % p] * c[(-j-lam) % p]
                         * c[(j+lam-1) % p] for j in range(p))
            if lam in (1, p-1):
                expected = (p*a**4 + (p+2)*a*a*b*b + (1-a*a)*(a*a-b*b)
                            + 2*correction*a**3
                            + 2*correction*a*b*b*(1-2*chi(2)))
            else:
                k = sum(chi(j*(j-1)*(j+lam)*(j+lam-1)) for j in range(p))
                e = ((1-chi(lam))*chi(lam-1)
                     - (1+chi(lam))*chi(lam+1))
                expected = (p*a**4 + 2*a*a*b*b + b**4*k
                            + correction*(4*a**3 + 2*a*b*b*e))
            assert sp.expand(actual-expected) == 0
        print(f"EXACT off-solution character identities: p={p}", flush=True)


def universal_elimination():
    a, d, p, e = sp.symbols("a d p e")
    qdiag = ((4*e+2*p-2)*a**4 + (4*e-4)*a**3
             - d*(4*e+p+1)*a*a + d*(2-4*e)*a + d)
    qsum = sp.expand(((p-1)*a*a-2*a-d)**2 - 4*(a*a-d)*(a+1)**2
                     - 2*d - (p-2)*d*d)
    expected = {
        -1: p**6*(p-11)**2*(p-3)**14,
        1: p**6*(p+1)**12*(p**4-76*p**3+406*p*p+532*p-4047),
    }
    for sign in [-1, 1]:
        r = sp.resultant(qsum, qdiag.subs(e, sign), a)
        r = sp.factor(sp.resultant(r, d*d-p*d-1, d))
        assert sp.expand(r-expected[sign]) == 0
        print(f"EXACT double resultant, chi(2)={sign}: {r}", flush=True)
    obstruction = p**4-76*p**3+406*p*p+532*p-4047
    assert sp.factorint(4047) == {3: 1, 19: 1, 71: 1}
    assert all(obstruction.subs(p, j) != 0 for j in [3, 19, 71])
    print("Necessary Q identities exclude every prime p == 3 mod 4 except 3, 11.",
          flush=True)


def finite_certificates():
    for n in (3, 11):
        started = time.monotonic()
        theta = (sp.sqrt((sp.sqrt(13)-1)/8) if n == 3
                 else sp.sqrt((-13+6*sp.sqrt(5))/4))
        field = sp.QQ.algebraic_field(theta)
        b = field.from_sympy(theta)
        d = field.one-4*b*b if n == 3 else (field.one-20*b*b)/12
        a = d/2 if n == 3 else (2*d-field.one)/10
        assert d*d-n*d-field.one == field.zero and a*a-b*b == d
        # Changing the sign of b is a field automorphism, so one calculation
        # certifies both real lifts. All positions are checked, with no orbits.
        w = [-field.one] + [a+b*int(sp.legendre_symbol(j, n)) for j in range(1, n)]
        A = [[(d-2 if g == h == 0 else -field.one if not g or not h or g == h
               else w[g]*w[(h-g) % n]/w[h])/(d-field.one)
              for h in range(n)] for g in range(n)]
        for g, h in product(range(n), repeat=2):
            assert sum((A[(g+j) % n][h]*A[h][j] for j in range(n)), field.zero) == (
                field.convert(int(g == 0))-field.convert(int(h == 0))/d)
        for g, h, k, l in product(range(n), repeat=4):
            assert sum((A[j][(g+h) % n]*A[g][(j+k) % n]*A[h][(j+l) % n]
                        for j in range(n)), field.zero) == (
                A[(g+l) % n][k]*A[(h+k) % n][l]-field.convert(int(g == h == 0))/d)
        print(f"EXACT p={n}: all {n*n} Q and {n**4} C positions passed; "
              f"{time.monotonic()-started:.2f} seconds", flush=True)


if __name__ == "__main__":
    character_sum_checks()
    universal_elimination()
    finite_certificates()
    print("PALEY OBSTRUCTION AND BOTH FINITE CERTIFICATES PASSED")
