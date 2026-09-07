"""Exact counterexamples to completion from finite-precision norms alone.

For primes p = 3 mod 8, the Legendre two-value ansatz reduces the
quartic convolution lift to three coordinates. Check its exact norm
valuation formula, and exhibit failed Q and C at orders passing the
modulo-8 norm test. No counterexample here satisfies all residue Q.
"""

import json
from pathlib import Path
import resource
import time

import sympy as sp

from hi_convolution_hensel import UnramifiedRing, lift_convolution


def compressed_lift(ring, p, a, b):
    delta = ring.lift(6)
    for _ in range(ring.bits.bit_length()+1):
        error = ring.sub(ring.sub(ring.mul(delta, delta), ring.scale(delta, p)), ring.one)
        if error == ring.zero:
            break
        delta = ring.sub(delta, ring.mul(error, ring.inv(ring.sub(ring.scale(delta, 2), ring.scalar(p)))))
    assert ring.sub(ring.sub(ring.mul(delta, delta), ring.scale(delta, p)), ring.one) == ring.zero
    coefficient = ring.scale(ring.inv(ring.mul(delta, ring.sub(delta, ring.one))), -1)
    x, u, v = ring.one, ring.lift(a), ring.lift(b)
    A = (p-3)//4
    for _ in range(ring.bits+2):
        uu, vv, uv = ring.mul(u, u), ring.mul(v, v), ring.mul(u, v)
        s0 = ring.add(ring.mul(x, x), ring.scale(uv, p-1))
        sr = ring.add(ring.add(ring.scale(ring.mul(x, u), 2), ring.scale(uu, A)),
                      ring.add(ring.scale(uv, 2*A), ring.scale(vv, A+1)))
        sn = ring.add(ring.add(ring.scale(ring.mul(x, v), 2), ring.scale(vv, A)),
                      ring.add(ring.scale(uv, 2*A), ring.scale(uu, A+1)))
        updated = (ring.mul(coefficient, ring.mul(ring.mul(x, x), s0)),
                   ring.mul(coefficient, ring.mul(vv, sr)),
                   ring.mul(coefficient, ring.mul(uu, sn)))
        if updated == (x, u, v):
            return delta, updated
        x, u, v = updated
    raise AssertionError('Compressed convolution failed to converge')


def residue_witness(ring, p, phases):
    mul = ring.ff_mul
    delta = 6
    inverse = [ring.ff_inv(value) for value in phases]

    def core(g, h):
        g, h = g % p, h % p
        if g == h == 0:
            return delta ^ 1
        if not g or not h or g == h:
            return delta
        return mul(delta, mul(mul(phases[g], phases[(h-g) % p]), inverse[h]))

    for h in range(1, min(p, 25)):
        q = 0
        for m in range(p):
            q ^= mul(core(m+1, h), core(h, m))
        if not q:
            continue
        ell = p-1
        k = next(k for k in range(p) if k not in {0, -h % p, ell, (ell-h) % p})
        c = mul(core(ell, k), core(h+k, ell))
        for m in range(p):
            c ^= mul(core(m, h), mul(core(0, m+k), core(h, m+ell)))
        assert c == mul(delta, q) and c
        return dict(q_indices=[1, h], q=q, c_indices=[0, h, k, ell], c=c)
    return None


def symbolic_identity():
    x, u, v, B, lam = sp.symbols('x u v B lam')
    N, Z = u*v, u+v
    sr = 2*x*u+(B-1)*u*u+2*(B-1)*u*v+B*v*v
    sn = 2*x*v+B*u*u+2*(B-1)*u*v+(B-1)*v*v
    hu, hv = u*u*sn+lam*v, v*v*sr+lam*u
    difference = B*Z**3-2*N*Z+2*x*N-lam
    norm_equation = B*N*Z**2-lam*Z-N**2
    assert sp.expand(hu-hv-(u-v)*difference) == 0
    assert sp.expand(hu+hv-Z*difference+2*norm_equation) == 0
    k, d, z = sp.symbols('k d z')
    B = 2*k+1
    numerator = d*(k*d+k+1)
    denominator = 3*k*d+1
    polynomial = sp.expand(B*numerator**2-(d-1)*numerator*denominator-d*denominator**2)
    result = sp.rem(polynomial, d*d-(8*k+3)*d-1, d)
    unit = 512*d*k**3+448*d*k**2+144*d*k+16*d+64*k**2+32*k+5
    assert sp.expand(result-k*(k-1)*B*unit) == 0
    q = B*z*z-(d-1)*z-d
    D = B*z**3-2*d*z-d*(d+1)
    L = denominator*z-numerator
    assert sp.rem(sp.expand(B*D-(B*z+d-1)*q-2*L), d*d-(8*k+3)*d-1, d) == 0
    print('EXACT symbolic elimination and unit factor: PASS', flush=True)


def main():
    started = time.monotonic()
    symbolic_identity()
    ring = UnramifiedRing([1, 1, 0, 0, 1], 16)
    seeds = [a for a in range(1, 16) if ring.ff_pow(a, 5) == 6 and a != ring.ff_pow(a, 4)]
    records = []
    for p in (3, 11, 19, 43, 67, 131, 4099):
        assert sp.isprime(p) and p % 8 == 3
        k = (p-3)//8
        z = 6 if k % 2 == 0 else 1
        a = next(a for a in seeds if a ^ ring.ff_pow(a, 4) == z)
        b = ring.ff_pow(a, 4)
        delta, (x, u, v) = compressed_lift(ring, p, a, b)
        norm = ring.valuation(ring.sub(ring.mul(u, v), delta))
        origin = ring.valuation(ring.add(x, ring.one))
        obstruction = k*(k-1)
        expected = 16 if not obstruction else min(16, (obstruction & -obstruction).bit_length())
        assert norm == expected and origin == min(16, norm+1)
        phases = [1]+[a if pow(j, (p-1)//2, p) == 1 else b for j in range(1, p)]
        assert all(ring.ff_mul(phases[j], phases[-j]) == 6 and
                   ring.ff_pow(phases[j], 4) == phases[2*j % p] for j in range(1, p))
        if p <= 67:
            direct_delta, direct, _ = lift_convolution(ring, p, 6, phases)
            assert delta == direct_delta and direct[0] == x
            assert all(direct[j] == (u if phases[j] == a else v) for j in range(1, p))
        witness = residue_witness(ring, p, phases)
        assert (witness is None) == (p in (3, 11))
        # Also check the other nonconstant Frobenius branch: its first
        # norm obstruction already fails, as predicted by the proof.
        other_a = next(a for a in seeds if a ^ ring.ff_pow(a, 4) != z)
        other_d, (other_x, other_u, other_v) = compressed_lift(ring, p, other_a, ring.ff_pow(other_a, 4))
        assert ring.valuation(ring.sub(ring.mul(other_u, other_v), other_d)) == 1
        print(f'EXACT p={p}; a={a}; b={b}; norm_v={norm}; origin_v={origin}; witness={witness}', flush=True)
        records.append(dict(p=p, a=a, b=b, delta=delta, lift=[x, u, v],
                            norm_valuation=norm, origin_valuation=origin, witness=witness))
    Path('hi_convolution_paley_obstruction_certificates.json').write_text(json.dumps(
        dict(modulus=19, residue_delta=6, bits=16, records=records), indent=2)+'\n')
    print(f'elapsed_seconds={time.monotonic()-started:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: norm-only modulo-8 completion is false; residue-Q completion is not refuted.')


if __name__ == '__main__':
    main()
