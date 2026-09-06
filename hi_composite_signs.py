"""Exact checks for scalar sign transport at composite odd orders.

Run: python hi_composite_signs.py
Checks the prime-power stabilizers, transport on each orbit, and an
abstract obstructed error cocycle at n=15. The last example is not
asserted to arise from an HI matrix or from Stark units.
"""

from math import gcd


def units(n):
    return [h for h in range(n) if gcd(h, n) == 1]


def transport(n, f):
    H = units(n)
    t = {0: 1}
    count = 0
    for a in range(1, n):
        if a in t:
            continue
        count += 1
        for h in H:
            target, value = h*a % n, f(h, a)
            if target in t and t[target] != value:
                return None
            t[target] = value
    assert all(t[h*a % n] == f(h, a)*t[a] for h in H for a in range(n))
    return t, count


def main():
    for p, k in ((3, 2), (3, 3), (5, 2), (7, 2), (3, 4)):
        n, H = p**k, units(p**k)
        for a in range(1, n):
            order = n//gcd(a, n)
            stabilizer = [h for h in H if h*a % n == a]
            assert len(stabilizer) == n//order and len(stabilizer) % 2 == 1
        signs = [1]+[(-1)**(min(a, n-a)//2) for a in range(1, n)]

        def f(h, a):
            return signs[h*a % n]*signs[a]

        result = transport(n, f)
        assert result is not None and result[1] == k
        assert all(result[0][-a % n] == result[0][a] for a in range(n))
        print(f"[ok] n={n}: all stabilizers odd; {k} independent orbit signs")

    n, H = 15, units(15)
    representatives = {3: 1, 6: 2, 9: 13, 12: 14}

    def f(h, a):
        if a not in representatives:
            return 1
        z = pow(representatives[h*a % n], -1, n)*h*representatives[a] % n
        assert z in (1, 11)
        return 1 if z == 1 else -1

    assert all(f(14, a) == 1 for a in range(n))
    assert all(f(h*k % n, a) == f(h, k*a % n)*f(k, a)
               for h in H for k in H for a in range(n))
    assert f(11, 3) == -1 and 11*3 % n == 3
    assert transport(n, f) is None
    print("[ok] n=15 abstract stabilizer obstruction, despite trivial negation error")
    print("ALL COMPOSITE SIGN CHECKS PASSED")


if __name__ == "__main__":
    main()
