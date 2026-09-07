"""Independent checks for the elementary series and Arb boundary enclosures.

Rational Richardson identities are exact. Double-sine integral comparisons
are numerical regressions; the C program encloses rounding and analytic
remainders using FLINT/Arb. Neither verifier proves exact Q/C or infinitude.
"""

import argparse
from fractions import Fraction
from pathlib import Path
import re

import mpmath as mp
import sympy as sp

from hi_shintani_meromorphic import sine


def richardson_checks():
    for p in range(2, 13):
        nodes = [Fraction(1, 4**j) for j in range(p)]
        weights = []
        for j in range(p):
            w = Fraction(1)
            for k in range(p):
                if k != j:
                    w *= nodes[k]/(nodes[k]-nodes[j])
            weights.append(w)
        assert sum(weights) == 1
        for k in range(1, p):
            assert sum(w*t**k for w, t in zip(weights, nodes)) == 0
        lebesgue = Fraction(1)
        for k in range(1, p):
            lebesgue *= Fraction(4**k+1, 4**k-1)
        assert sum(abs(w) for w in weights) == lebesgue
        absolute_moment = sum(abs(w)*t**p for w, t in zip(weights, nodes))
        assert absolute_moment == lebesgue/Fraction(2**(p*(p-1)))
        error = Fraction(5, 2*p)*absolute_moment/Fraction(8**(2*p))
        assert error == Fraction(5, 2*p)*lebesgue/Fraction(2**(p*p+5*p))
        assert lebesgue < 3
        if p in (4, 6, 8, 10, 12):
            print(f"EXACT p={p}: E_p={error}; decimal upper approximation={float(error):.8e}", flush=True)
    # The two-dimensional divisor bound is <= 5*2^-s for every s>=4.
    s = sp.symbols('s', integer=True, positive=True)
    expression = 2*(1+2/(s-1)+4/((s-1)*(s-2)))
    assert expression.subs(s, 4) == sp.Rational(14, 3) < 5
    print("EXACT: geometric weights, moment cancellations, and remainder formula passed.", flush=True)


def small_divisor_checks():
    n, k, m, theta = sp.symbols('n k m theta')
    norm = sp.expand((k*theta-m)*(k*(-n-theta)-m))
    remainder = sp.rem(norm-(m*m+n*k*m-k*k), theta*theta+n*theta-1, theta)
    assert remainder == 0
    for order in (3, 7, 11, 33, 101):
        delta = mp.sqrt(order*order+4)
        d = (order+delta)/2
        theta_value = 1/d
        for j in range(1, 513):
            nearest = int(mp.nint(j*theta_value))
            integer_norm = nearest*nearest+order*j*nearest-j*j
            assert integer_norm != 0
            distance = abs(j*theta_value-nearest)
            assert distance >= 1/(j*delta+mp.mpf('0.5'))
            assert abs(mp.expm1(2j*mp.pi*j*theta_value)) >= 4/(j*delta+mp.mpf('0.5'))
    print("EXACT norm identity and 2560 numerical small-divisor bound regressions passed.", flush=True)


def kernel_check(n, a, c):
    r = len(a)
    d = (n+mp.sqrt(n*n+4))/2
    A, B = d+1, 1+1/d
    q = mp.exp(2j*mp.pi/d)
    kappa = n/(A*B)
    alpha = [mp.exp(2j*mp.pi*u/A) for u in a]
    gamma = [mp.exp(2j*mp.pi*u/A) for u in c]
    constant = mp.exp(mp.pi*1j/(2*A*B)
                      *(sum(u*u for u in a)-sum(u*u for u in c)-n*(sum(a)-sum(c))))
    z = mp.mpc('0.37', '0.8')
    x, v = mp.exp(2j*mp.pi*z/A), mp.exp(2j*mp.pi*z/B)
    coefficient_bound = r*(mp.sqrt(n*n+4)+mp.mpf('0.5'))/2
    count = 0
    while True:
        count += 1
        tail = coefficient_bound*(abs(x)**(count+1)/(1-abs(x))
                                  + abs(v)**(count+1)/(1-abs(v)))
        if tail < mp.mpf('1e-32'):
            break
    terms = []
    for j in range(1, count+1):
        c1 = (q**j*sum(t**j for t in alpha)-sum(t**(-j) for t in gamma))/(j*(q**j-1))
        c2 = (sum(t**(-j) for t in alpha)-q**j*sum(t**j for t in gamma))/(j*(q**j-1))
        assert abs(c2+mp.conj(c1)) < mp.mpf('1e-40')
        assert abs(c1) <= coefficient_bound and abs(c2) <= coefficient_bound
        terms.append(c1*x**j+c2*v**j)
    approximated = constant*mp.exp(-2j*mp.pi*kappa*z+mp.fsum(terms))
    reference = (mp.fprod(sine(1+(z+u)/B, d) for u in a)
                 * mp.fprod(sine(1+(u-z)/B, d) for u in c))
    error = abs(approximated/reference-1)
    assert error <= mp.expm1(tail)+mp.mpf('1e-40')
    print(f"NUMERICAL complex kernel n={n} r={r} terms={count} "
          f"relative error={mp.nstr(error,7)} tail bound={mp.nstr(mp.expm1(tail),7)}", flush=True)


def check_saved_arb_balls(path):
    data = Path(path).read_text()
    assert 'COMPLETE: certified candidate and residual enclosures' in data
    rows = re.findall(r'^BALL n=(\d+) w=(\d+) terms=(\d+) \[([^\]]+)\]$', data, re.M)
    assert rows
    for order, label, _, ball in rows:
        n, w = int(order), int(label)
        midpoint, radius = [mp.mpf(s.strip()) for s in ball.split('+/-')]
        d = (n+mp.sqrt(n*n+4))/2
        B = 1+1/d
        reference = sine(1+w/B, d)
        assert abs(reference.imag) < mp.mpf('1e-40')
        assert abs(reference.real-midpoint) < radius
    print(f"NUMERICAL independent integral values lie in all {len(rows)} printed Arb balls.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--arb-results', default='hi_shintani_boundary_series_results.txt')
    args = parser.parse_args()
    mp.mp.dps = 50
    richardson_checks()
    small_divisor_checks()
    for n in (3, 7, 11):
        kernel_check(n, [0, -(n-1)], [1, n-2])
        kernel_check(n, [0, 0, 0], [1, 1, n-2])
    check_saved_arb_balls(args.arb_results)
    print('COMPLETE: independent checks passed; no exact Q/C or infinitude claim.')


if __name__ == '__main__':
    main()
