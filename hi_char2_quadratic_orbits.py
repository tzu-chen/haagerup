"""Uniform orbit representatives for Q at n=3^k in the Frobenius gauge.

Exactly (n-1)/2 residuals suffice. This is an equation reduction, not a
nonemptiness or cubic-completion theorem. The standalone checker verifies
coverage of every nonzero pair through n=729, without solving equations.
"""


def valuation3(a):
    value = 0
    while a % 3 == 0:
        a //= 3
        value += 1
    return value


def representative(n, g, h):
    assert 0 < g < n and 0 < h < n
    scale = 3**min(valuation3(g), valuation3(h))
    m = n//scale
    a, b = g//scale, h//scale
    if a % 3 == 0:
        a, b = b, a
    ratio = b*pow(a, -1, m) % m
    choices = [ratio, m-ratio]
    if ratio % 3:
        inverse = pow(ratio, -1, m)
        choices += [inverse, m-inverse]
    return scale, scale*min(choices)


def representatives(n):
    m, scale, answer = n, 1, []
    while m > 1:
        assert m % 3 == 0
        for t in range(1, (m+1)//2):
            if t % 3:
                inverse = pow(t, -1, m)
                if t > min(inverse, m-inverse):
                    continue
            answer.append((scale, scale*t))
        m //= 3
        scale *= 3
    assert len(answer) == (n-1)//2
    return answer


def main():
    for n in [3, 9, 27, 81, 243, 729]:
        expected = set(representatives(n))
        seen = set()
        for g in range(1, n):
            for h in range(1, n):
                rep = representative(n, g, h)
                assert rep in expected
                assert rep == representative(n, h, g)
                assert rep == representative(n, n-g, h)
                assert rep == representative(n, 2*g % n, 2*h % n)
                seen.add(rep)
        assert seen == expected
        print(f'EXACT Q ORBIT COVERAGE n={n}: {(n-1)**2} pairs, '
              f'{len(seen)} representatives', flush=True)
    print('ALL ORBIT CHECKS PASSED; existence and uniform Q => C remain open.')


if __name__ == '__main__':
    main()
