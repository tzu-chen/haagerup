"""Uniform normalized-cup bounds and a stronger ghost correction test.

Section 92 proves the estimates. Numerical off-pentagon checks use both
Fibonacci dimension roots. Rational replay uses the previously certified
order-3, 7, and 11 bounds; it does not certify an unbounded family.
"""

from fractions import Fraction
from pathlib import Path
import re
import resource

import numpy as np
import sympy as sp

from hi_nonunitary_pentagon_correction import (
    GLTrial, inv, average, cofaces, differential, random_operator, update,
    ONE, TAU, SIMPLES, PHI, zero, identity, tensor, tensor_obj, right_obj,
)


def normalized_cup_bound(trial):
    bound = 0.0
    for obj in SIMPLES:
        grams = [zero(obj) for _ in range(4)]
        for a, sa in enumerate(SIMPLES):
            left = trial.F(sa, sa, obj)
            right = trial.F(obj, sa, sa)
            lp = left @ tensor(trial.cup(a), identity(obj))
            lm = tensor(trial.cap(a), identity(obj)) @ inv(left)
            rp = inv(right) @ tensor(identity(obj), trial.cup(a))
            rm = tensor(identity(obj), trial.cap(a)) @ right
            weight = abs(trial.dims[a]) / abs(trial.global_dim)
            # Euclidean Grams measure auxiliary stack norms. They are not
            # categorical adjoints or replacements for associator inverses.
            for j, gram in enumerate((lp.adjoint() @ lp, lm @ lm.adjoint(),
                                      rp.adjoint() @ rp, rm @ rm.adjoint())):
                grams[j] = grams[j] + gram.scale(weight)
        bound = max(bound, *(g.norm() for g in grams))
    return bound


def exact_constants():
    d = sp.symbols('d', positive=True)
    n = d - 1/d
    D = n * (1 + 1/d**2)
    noninvertible = (n + n/d * (d+n)) / D
    invertible = (n + n/d**2) / D
    assert sp.cancel(noninvertible - (3 - 1/d**2)/(1 + 1/d**2)) == 0
    assert sp.cancel(invertible - 1) == 0
    assert 14*4 + 400*4 + Fraction(25, 2)*16 == 1856
    assert 1856 + 4*8 == 1888
    assert Fraction(1888, 3776) == Fraction(1, 2)
    assert Fraction(7, 4)**2 > 3
    assert Fraction(7, 4) + Fraction(1, 472) < 2
    assert Fraction(8, 3776) == Fraction(1, 472)
    assert 2**12 * 4**14 == 2**40
    print("EXACT: ghost normalized cup bound H0=(3-d^-2)/(1+d^-2)<3; S=1")
    print("EXACT: H<=4; quadratic constant 1856*M^12; with drift 1888*M^12; threshold 1/(3776*M^12)")


def regressions():
    rng = np.random.default_rng(9201)
    for name, delta in (('Fibonacci', PHI), ('Yang-Lee', -1/PHI)):
        t = 1 / np.sqrt(complex(delta))
        original = GLTrial(np.array([[t*t, t], [t, -t*t]]), 1, delta)
        H0 = normalized_cup_bound(original)
        predicted = 1 if delta > 0 else (3 - delta**2)/(1 + delta**2)
        assert abs(H0 - predicted) < 2e-14
        u = random_operator(rng, right_obj((TAU,)*3))
        for scale in (0.0, 0.001, 0.02):
            trial = update(original, u, scale)
            q, qi = trial.errors()
            H, M = normalized_cup_bound(trial), trial.M
            Mpath = original.M * np.exp(scale)
            assert H <= (np.sqrt(H0) + Mpath*scale)**2 + 2e-14
            mu = max(trial.imbalance(b) for b in range(2))
            for obj in (TAU, (2, 3)):
                operators = [random_operator(rng, tensor_obj(sa, obj)) for sa in SIMPLES]
                for b in range(2):
                    l, r, rl, rr = trial.handle(b, obj, operators)
                    assert (l-rl).norm() <= H*M*M*(q+qi) + 2e-11
                    assert (r-rr).norm() <= H*M*M*(q+qi) + 2e-11
                    assert (l-r).norm() <= 2*H*M*M*(q+qi) + M*M*mu + 3e-11
            y = random_operator(rng, right_obj((TAU,)*4))
            faces = [zero(y.source) for _ in range(6)]
            for a in range(2):
                for j, f in enumerate(cofaces(trial, y, 4, (SIMPLES[a],)+(TAU,)*4)):
                    faces[j] = faces[j] + trial.trace(a, y.source, f).scale(trial.dims[a]/trial.global_dim)
            after = cofaces(trial, average(trial, y, 4), 3)
            boundary = (faces[5] - after[4]).norm()
            assert boundary <= H*M**6*(q+qi) + 3e-11
            homotopy = y - differential(trial, average(trial, y, 4), 3) - average(trial, differential(trial, y, 4), 5)
            assert homotopy.norm() <= H*(2*M*M+M**6)*(q+qi) + M*M*mu + 3e-11
            assert average(trial, y, 4).norm() <= H + 2e-12
            print("NORMALIZED_TRACE_REGRESSION", name, scale, "H", H, "M", M,
                  "q", q, "mu", mu, "homotopy_sample", homotopy.norm(),
                  "boundary_sample", boundary, flush=True)


def replay_certificates():
    data = Path(__file__).with_name('hi_shintani_correction_results.txt').read_text()
    assert 'COMPLETE: certified candidate and residual enclosures' in data
    for n in (3, 7, 11):
        pattern = rf"CORRECTION n={n} M0_upper=\[([^ ]+) \+/- ([^\]]+)\] full_pentagon_upper=\[([^ ]+) \+/- ([^\]]+)\]"
        mm, mr, qm, qr = re.search(pattern, data).groups()
        M = 2*(Fraction(mm)+Fraction(mr))
        q = Fraction(qm)+Fraction(qr)
        ratio = 3776*M**12*q
        assert ratio < 1
        assert 8*M*q < Fraction(1, 472)
        assert q < 1/(16*M**6)
        print("EXACT_IMPROVED_CORRECTION_REPLAY", n,
              "ratio_approx", float(ratio), "gain_approx", float(870*M*M/3776),
              "proved_ratio_below_one_and_rigidity_margin", flush=True)


if __name__ == '__main__':
    exact_constants()
    regressions()
    replay_certificates()
    print(f"Peak RSS: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.1f} MiB")
    print("COMPLETE: normalized ghost trace and correction checks; NO INFINITUDE CLAIM")
