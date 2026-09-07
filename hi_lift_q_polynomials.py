"""Free-Laurent expansion of the first balanced Q lift errors, equation 103.1.

This constructs products and squares of sparse polynomials. The batch
search instead expands the underlying index lists directly, providing a
separate route for replay in the canonical norm/Frobenius quotient.
"""

from functools import cache

from hi_laurent_q_certificate import MUL, add_term, phase_product


def multiply(left, right):
    result = {}
    for a, u in left.items():
        for b, v in right.items():
            add_term(result, tuple(x+y for x, y in zip(a, b)), MUL[u][v])
    return result


def square(poly):
    return {tuple(2*a for a in e): MUL[v][v] for e, v in poly.items()}


@cache
def pair_squares(n):
    pairs = [{} for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            add_term(pairs[(i+j) % n], *phase_product(n, (i, j)))
    return tuple(square(poly) for poly in pairs)


def lift_polynomial(n, g, h):
    result, partial = {}, {}
    U2 = pair_squares(n)
    for m in range(n):
        indices = (m, (h-m) % n, (-m-g) % n, (m+g-h) % n)
        exponent, value = phase_product(n, indices)
        term = {exponent: value}
        for e, v in multiply(partial, term).items():
            add_term(result, e, v)
        add_term(partial, exponent, value)
        for slot, a in enumerate(indices):
            e, v = phase_product(n, indices[:slot]+indices[slot+1:])
            other_square = square({e: v})
            e, v = phase_product(n, (a,))
            contribution = multiply({e: v}, multiply(other_square, U2[a]))
            for e, v in contribution.items():
                add_term(result, e, v)
    return result


def derivative_parts(n, g, h):
    """Return the carry and w_a U_a^2 (partial_a F)^2, before Frobenius.

    Derivatives are taken with every X_a, including X_0, independent;
    only afterward are the origin and inverse-norm identities substituted.
    """
    derivatives = [{} for _ in range(n)]
    carry, partial = {}, {}
    for m in range(n):
        indices = (m, (h-m) % n, (-m-g) % n, (m+g-h) % n)
        e, v = phase_product(n, indices)
        for exponent, value in multiply(partial, {e: v}).items():
            add_term(carry, exponent, value)
        add_term(partial, e, v)
        for slot, a in enumerate(indices):
            add_term(derivatives[a], *phase_product(n, indices[:slot]+indices[slot+1:]))
    parts = []
    for a, derivative in enumerate(derivatives):
        e, v = phase_product(n, (a,))
        parts.append(multiply({e: v}, multiply(pair_squares(n)[a], square(derivative))))
    return carry, parts
