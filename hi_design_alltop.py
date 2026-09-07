"""Checks for the weighted-design formulation and the Alltop rigidity theorem.

The dimension/weight identities and cyclotomic nonvanishing checks are exact.
The tensor-design and differential checks use floating point, independently
of the exact finite HI existence certificates.
"""

from pathlib import Path
import re

import numpy as np
import sympy as sp


def design_residual(b):
    n = len(b)
    u = abs(b[0])**2
    total = n-1+u
    diag_overlap = (u-1)**2/total**2
    off_overlap = (n-2+2*u)/total**2
    weight = n*(off_overlap-diag_overlap)
    v = b/np.sqrt(total)
    tensor_sum = np.zeros((n*n, n*n), complex)
    for h in range(n):
        for k in range(n):
            orbit = np.roll(v, h)*np.exp(2j*np.pi*k*np.arange(n)/n)
            vv = np.kron(orbit, orbit)
            tensor_sum += np.outer(vv, vv.conjugate())
    for j in range(n):
        tensor_sum[j*n+j, j*n+j] += weight
    swap = np.zeros_like(tensor_sum)
    for j in range(n):
        for k in range(n):
            swap[j*n+k, k*n+j] = 1
    target = n*off_overlap*(np.eye(n*n)+swap)
    return np.max(np.abs(tensor_sum-target))


def alltop_differential_check(p, c):
    residues = np.arange(p)
    b = -np.exp(2j*np.pi*c*(residues**3 % p)/p)
    theta = np.zeros(p)
    for g in range(1, (p+1)//2):
        theta[g], theta[-g] = np.sin(g+0.3), -np.sin(g+0.3)
    amplitude = 0.37
    worst = 0
    for g in range(1, p):
        for h in range(1, p):
            direct = 0j
            for m in range(p):
                indices = [m, (h-m) % p, (-m-g) % p, (m+g-h) % p]
                direct += np.prod(b[indices])*(1j*sum(theta[j] for j in indices)
                                               +amplitude*indices.count(0))
            ell = -6*c*g*h % p
            fourier = sum(theta*np.exp(2j*np.pi*ell*residues/p))
            X = np.exp(2j*np.pi*(ell*h % p)/p)
            Y = np.exp(2j*np.pi*(-ell*g % p)/p)
            prefactor = np.exp(2j*np.pi*(-3*c*g*h*(g-h) % p)/p)
            transformed = prefactor*(1j*(1-X)*(1-Y)*fourier
                                     +(1+X)*(1+Y)*amplitude)
            worst = max(worst, abs(direct-transformed))
    assert worst < 2e-11, (p, c, worst)
    return worst


def cyclotomic_obstruction(p):
    z = sp.Symbol("z")
    inverse_two = pow(2, -1, p)
    def numerator(a):
        return 1+z**(a % p)
    def denominator(a):
        return 1-z**(a % p)
    difference = (numerator(1)*numerator(-1)*denominator(2)*denominator(-inverse_two)
                  -numerator(2)*numerator(-inverse_two)*denominator(1)*denominator(-1))
    remainder = sp.rem(difference, sp.cyclotomic_poly(p, z), z)
    assert remainder != 0


def main():
    n, u = sp.symbols("n u")
    total = n-1+u
    a, beta = (u-1)**2/total**2, (n-2+2*u)/total**2
    assert sp.factor(a+n*beta-1) == 0
    d = sp.Symbol("d", positive=True)
    assert sp.factor((n*(beta-a)).subs(u, 1/d).subs(n, d-1/d)
                     -(d-1/d)*(d-1)/d**2) == 0
    print("[ok] exact general design weights and the HI specialization")
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31):
        cyclotomic_obstruction(p)
        worst = alltop_differential_check(p, 1)
        print(f"[ok] p={p}: exact cyclotomic obstruction; differential error {worst:.3g}")
    for p in (5, 7, 11):
        b = -np.exp(2j*np.pi*(np.arange(p)**3 % p)/p)
        error = design_residual(b)
        assert error < 1e-12
        print(f"[ok] Alltop tensor design at p={p}; residual {error:.3g}")
    source = Path(__file__).with_name("z13_stark_test.gp").read_text()
    j = list(map(float, re.search(r"jrefined = \[([^]]+)\];", source).group(1).split(",")))
    center = j[6]+j[7]
    for g in range(8, 13):
        j[g] = center-j[13-g]
    dimension = (13+np.sqrt(173))/2
    b = np.array([-1/np.sqrt(dimension)]
                 +[np.exp(-1j*(j[g]-center*g/13)) for g in range(1, 13)])
    error = design_residual(b)
    assert error < 2e-12
    print(f"[ok] HI weighted tensor design at n=13; residual {error:.3g}")
    print("ALL WEIGHTED-DESIGN AND ALLTOP CHECKS PASSED")


if __name__ == "__main__":
    main()
