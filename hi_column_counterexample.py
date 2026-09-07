"""Exact algebraic counterexample to extending one Q column to all columns.

At order 5 the row has r1=x, r2=((2-d)*x-1)/2,
where x^2+2*d*x+d=0 and d^2=5*d+1. This works over either
quadratic embedding. At the negative embedding it is a real ghost
candidate, but it is outside the canonical coordinate-sign chamber.
No physical unit-modulus counterexample is asserted by this file.
"""

import sympy as sp


def main():
    x = sp.Symbol("x")
    d = (5 + sp.sqrt(29)) / 2
    field = sp.QQ.algebraic_field(sp.sqrt(29))
    f = sp.Poly(x * x + 2 * d * x + d, x, domain=field)

    def q(value):
        return sp.Poly(value, x, domain=field).rem(f)

    one, zero = q(1), q(0)

    def mul(*values):
        answer = one
        for value in values:
            answer = (answer * value).rem(f)
        return answer

    def inv(value):
        return sp.invert(value, f)

    r1, r2 = q(x), q(((2 - d) * x - 1) / 2)
    pref = [one, one, r1, mul(r1, r2), mul(r1, r1, r2)]
    B = [[q(-1) for _ in range(5)] for _ in range(5)]
    B[0][0] = q(d - 2)
    for g in range(1, 5):
        for h in range(g + 1, 5):
            B[g][h] = mul(pref[h], inv(pref[g]), inv(pref[h - g]))
            B[h][g] = mul(q(d), inv(B[g][h]))
    for g in range(5):
        for h in range(5):
            assert B[g][h] == B[-h % 5][(g - h) % 5]
            if g and h and g != h:
                assert mul(B[g][h], B[h][g]) == q(d)
            value = sum((mul(B[(g + j) % 5][h], B[h][j]) for j in range(5)), zero)
            value -= q((d - 1) ** 2 * (int(g == 0) - int(h == 0) / d))
            expected = q(-31 * d - 4) if g in (2, 3) and h in (2, 3) else zero
            assert value == expected, (g, h)
    assert q(-31 * d - 4) != zero
    print("[ok] exact order-three symmetry, generic norms, and complete columns 0, 1, 4")
    print("[ok] the four remaining nonzero Q residuals equal -31*d-4")
    print("EXACT ALGEBRAIC ONE-COLUMN COUNTEREXAMPLE PASSED")


if __name__ == "__main__":
    main()
