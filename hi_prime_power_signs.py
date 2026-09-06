"""Check the prime-power linear sign identity independently on arbitrary phases.

These floating-point off-solution tests validate the algebraic change of
variables in Section 40. Exact solution and rank checks are in
hi_single_root_checks.gp; no existence claim comes from this script.
"""

import numpy as np

from hi_beta_reductions import phase_matrix


def valuation(a, p):
    assert a != 0
    result = 0
    while a % p == 0:
        result += 1
        a //= p
    return result


def main():
    for p, k in ((3, 1), (3, 2), (3, 3), (3, 4), (5, 2), (5, 3)):
        n = p**k
        d = (n+np.sqrt(n*n+4))/2
        b = np.empty(n, dtype=complex)
        b[0] = -1/np.sqrt(d)
        for g in range(1, (n+1)//2):
            b[g] = np.exp(1j*(g*g+3*g+1)/13)
            b[-g] = b[g].conjugate()
        B = (d-1)*phase_matrix(b, d)
        T = B[1, 2]+B[2, 1]
        constant = 1+0j
        coeffs = np.zeros(k, dtype=complex)
        for m in range(2, n-1):
            term = B[m+1, 1]*B[1, m]
            level = valuation(m*m-1, p)
            assert level < k
            if level:
                coeffs[level] += term
            else:
                constant += term
        worst = 0
        for choice in range(2**k):
            signs = [(-1)**((choice >> j) & 1) for j in range(k)]
            signed_b = b.copy()
            for g in range(1, n):
                signed_b[g] *= signs[valuation(g, p)]
            signed_B = (d-1)*phase_matrix(signed_b, d)
            direct = sum(signed_B[(m+1) % n, 1]*signed_B[m, 1].conjugate()
                         for m in range(n))
            linear = constant-signs[0]*T+sum(signs[0]*signs[j]*coeffs[j]
                                            for j in range(1, k))
            worst = max(worst, abs(direct-linear))
        assert worst < 1e-9, (n, worst)
        print(f"[ok] n={n}: every one of {2**k} sign choices; max residual {worst:.3g}")
    print("ALL PRIME-POWER LINEAR SIGN IDENTITIES PASSED")


if __name__ == "__main__":
    main()
