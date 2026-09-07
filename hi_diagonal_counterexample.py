"""Exact physical order-5 counterexample to using only diagonal quadratics.

The row satisfies the phase cocycle, all physical norms, multiplier Galois
covariance, and Q(g,g)=0 for every nonzero g. Its off-diagonal quadratics
are nonzero. This is not an HI category or a counterexample to HI existence.
"""

import sympy as sp


def main():
    x = sp.Symbol('x')
    d = (5+sp.sqrt(29))/2
    field = sp.QQ.algebraic_field(sp.sqrt(29))
    f = sp.Poly(x**4+(d-2)*x**3+d*x**2+(3*d+1)*x+d**2,
                x, domain=field)

    def q(expression):
        return sp.Poly(expression, x, domain=field).rem(f)

    one, zero = q(1), q(0)

    def mul(*factors):
        value = one
        for factor in factors:
            value = (value*factor).rem(f)
        return value

    def inv(value):
        return sp.invert(value, f)

    r = q(x)
    r2 = q(((d-6)*x**3+(6-d)*x**2+(13-3*d)*x+3-3*d)/5)

    def phi(value):
        return value.compose(r2).rem(f)

    assert f.compose(r2).rem(f) == zero
    assert phi(r2) == mul(q(d), inv(r))
    assert phi(phi(phi(phi(r)))) == r
    factors = sp.factor_list(f)[1]
    assert len(factors) == 1 and factors[0][0].degree() == 4 and factors[0][1] == 1
    print('[ok] irreducible quartic and cyclic order-4 multiplier automorphism')

    prefix = [one, one, r, mul(r, r2), mul(r, r, r2)]
    B = [[q(-1) for _ in range(5)] for _ in range(5)]
    B[0][0] = q(d-2)
    for g in range(1, 5):
        for h in range(g+1, 5):
            B[g][h] = mul(prefix[h], inv(prefix[g]), inv(prefix[h-g]))
            B[h][g] = mul(q(d), inv(B[g][h]))
    for g in range(5):
        for h in range(5):
            assert phi(B[g][h]) == B[2*g % 5][2*h % 5]
            assert phi(phi(B[g][h])) == B[h][g]
    print('[ok] every multiplier-covariance and formal-conjugation identity')

    # The two possible traces x+d/x are the roots of
    # v^2+(d-2)v-d. Both lie strictly inside (-2*sqrt(d),2*sqrt(d)).
    # Positivity here is decided exactly for real algebraic expressions.
    traces = [(-(d-2)+sign*sp.sqrt(d**2+4))/2 for sign in (-1, 1)]
    for trace in traces:
        assert sp.simplify(4*d-trace**2).is_positive is True
    print('[ok] all four quartic roots have physical modulus sqrt(d)')

    failed_pairs = []
    for g in range(1, 5):
        for h in range(1, 5):
            residual = sum((mul(B[(g+j) % 5][h], B[h][j])
                            for j in range(5)), zero)
            residual = residual.rem(f)
            if h in (g, -g % 5):
                assert residual == zero
            else:
                assert residual == q(2*(d-1))
                failed_pairs.append((g, h))
    assert len(failed_pairs) == 8
    print('[ok] all diagonal quadratics vanish exactly')
    print('[ok] all 8 remaining quadratics equal 2*(d-1), hence are nonzero')
    print('EXACT PHYSICAL DIAGONAL COUNTEREXAMPLE PASSED')


if __name__ == '__main__':
    main()
