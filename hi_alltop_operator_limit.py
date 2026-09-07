"""Check the large-order Alltop approximation in operator norms.

The quadratic operator error tends to zero at the HI amplitude, but
the necessary cubic polynomial has normalized Hilbert--Schmidt norm
tending to sqrt(2) along primes p=2 mod 3. Exact identities below
support the proof; randomized large-matrix measurements are labelled
as estimates and are not existence certificates.
"""

import argparse
from itertools import product

import numpy as np
import sympy as sp


def exact_checks():
    x = sp.symbols('x:5')
    action = sum(x[i]*(x[(i-1) % 5]+x[(i+1) % 5])
                 *(x[i]-x[(i-1) % 5]-x[(i+1) % 5]) for i in range(5))
    cubic = sum(x[(i-1) % 5]*x[i]*x[(i+1) % 5] for i in range(5))
    assert sp.expand(action+2*cubic) == 0
    exponent_matrix = sp.Matrix(5,5,lambda i,j: int(j in [(i-1)%5,i,(i+1)%5]))
    assert exponent_matrix.det() == 3
    print('EXACT cyclic five-factor phase is minus twice the consecutive-triple cubic.', flush=True)
    print('EXACT torus monomial exponent determinant is 3; the torus character sum is -1.', flush=True)
    for p in [5,11,17,23]:
        zeros = 0
        for a,b,c,d in product(range(p), repeat=4):
            coefficient = (a*b+c*d+d*a) % p
            constant = b*c*(a+d) % p
            zeros += 1 if coefficient else p if not constant else 0
        assert zeros == p**4+5*p*(p-1)**2
        assert (p**5-zeros) % (p-1) == 0
        nonzero = (p**5-zeros)//(p-1)
        assert zeros-nonzero == 5*p*p*(p-1)
        torus_zeros = 0
        for a,b,c,d in product(range(1,p),repeat=4):
            coefficient = (a*b+c*d+d*a) % p
            constant = b*c*(a+d) % p
            torus_zeros += int(constant != 0) if coefficient else p-1 if not constant else 0
        assert p*torus_zeros == (p-1)**5-(p-1)
        print(f'EXACT p={p}: cubic zero count={zeros}, additive character sum={zeros-nonzero}', flush=True)


def matrices(p, c=1):
    d = (p+np.sqrt(p*p+4.0))/2
    t = 1/d
    alpha = np.sqrt(d)/(d-1)
    epsilon = 1/(d-1)
    g = np.arange(p, dtype=np.int64)[:,None]
    h = np.arange(p, dtype=np.int64)[None,:]
    phase = np.exp(2j*np.pi*((3*c*g*h*(g-h)) % p)/p)
    A = -alpha*phase
    A[(g == 0) | (h == 0) | (g == h)] = -epsilon
    A[0,0] = 1-epsilon
    B = -phase/np.sqrt(p)
    B[0,:] = A[0,:]
    bound = np.sqrt((d+1)/(d-1))-1+2/(np.sqrt(d)+1)
    return A, B, t, bound


def apply_operator(fourier, vectors):
    p = fourier.shape[0]
    shape = vectors.shape
    arrays = vectors.reshape((-1,p,p))
    transformed = np.fft.fft(arrays, axis=2)[:,:,(-np.arange(p)) % p]
    output = np.fft.ifft(fourier[None,:,:]*transformed, axis=2).transpose(0,2,1)
    return output.reshape(shape)


def dense(A):
    p = A.shape[0]
    R = np.zeros((p*p,p*p), dtype=complex)
    for a,b,e in product(range(p), repeat=3):
        R[a*p+b,b*p+e] = A[b,(a+e) % p]
    return R


def fifth_trace_formula(p,t):
    e = (1+t)/p
    m = p-1
    u,v = 1-e*m,1-e
    # Contributions from the eight cyclic types of zero-index subsets.
    return (p**(-2.5)+5*m*m*(m-e)/p**2
            +5*e*e*m*m/p**1.5-5*m*u*u/p**1.5
            +5*e*e*v*m*m/p+5*e*e*m*u/p
            -5*e*e*v*v*m/p**0.5+v**5)


def probe(p, samples, rng):
    assert sp.isprime(p) and p % 3 == 2
    A,B,t,bound = matrices(p)
    fa,fb = np.fft.fft(A,axis=1),np.fft.fft(B,axis=1)
    assert np.max(np.abs(np.abs(fb[1:,:])-1)) < 2e-12
    expected = np.ones(p)
    expected[0] = t
    assert np.max(np.abs(np.abs(fb[0,:])-expected)) < 2e-12
    distance = np.max(np.abs(fa-fb))
    assert distance <= bound+2e-12
    qerror = np.max(np.abs(np.abs(fa[1:,:])**2-1))
    assert qerror <= 2*bound+bound*bound+2e-12
    vectors = rng.normal(size=(samples,p*p))+1j*rng.normal(size=(samples,p*p))
    vectors /= np.linalg.norm(vectors, axis=1)[:,None]
    powers = {0:vectors}
    current = vectors
    for k in range(1,9):
        current = apply_operator(fa,current)
        if k in [1,3,5,6,8]:
            powers[k] = current
    residual = (powers[8]-powers[3]
                +t*(powers[6]+powers[5]-powers[1]-powers[0]))
    norms = np.linalg.norm(residual,axis=1)
    current = vectors
    for k in range(5):
        current = apply_operator(fb,current)
    bar_trace_estimate = np.mean(np.sum(vectors.conjugate()*current,axis=1))
    bar_defect_estimate = np.mean(np.linalg.norm(current-vectors,axis=1)**2)
    if p <= 11:
        R,Rbar = dense(A),dense(B)
        assert np.max(np.abs(apply_operator(fa,vectors)-vectors@R.T)) < 2e-12
        I = np.eye(p*p)
        F = (np.linalg.matrix_power(R,5)-I)@(np.linalg.matrix_power(R,3)+t*R+t*I)
        assert np.max(np.abs(residual-vectors@F.T)) < 5e-11
        fifth = np.linalg.matrix_power(Rbar,5)
        assert abs(np.trace(fifth)-fifth_trace_formula(p,t)) < 2e-10
        hs = np.linalg.norm(fifth)**2
        assert p*p-5-1e-10 <= hs <= p*p+1e-10
        print(f'DIRECT MATRIX CHECK p={p}: normalized trace Rbar^5={np.trace(fifth)/(p*p)}, '
              f'normalized HS(F)^2={np.linalg.norm(F)**2/(p*p):.10g}',flush=True)
    print(f'OPERATOR PROBE p={p}: Q_error={qerror:.8g}, distance_to_Rbar={distance:.8g}, '
          f'proved_distance_bound={bound:.8g}; samples={samples}; '
          f'HS(F)^2/N estimate={np.mean(norms**2):.8g}; '
          f'operator_norm_F lower bound={max(norms):.8g}; '
          f'HS(Rbar^5-I)^2/N estimate={bar_defect_estimate:.8g}; '
          f'Tr(Rbar^5)/N estimate={bar_trace_estimate}; '
          f'exact-formula trace/N={fifth_trace_formula(p,t)/(p*p):.10g}',flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primes',type=int,nargs='+',default=[5,11,23,47,101,257,509])
    parser.add_argument('--samples',type=int,default=4)
    args = parser.parse_args()
    exact_checks()
    rng = np.random.default_rng(83084)
    for p in args.primes:
        probe(p,args.samples,rng)
    print('ALL CHECKS PASSED; large-matrix samples are numerical estimates, not HI certificates.')


if __name__ == '__main__':
    main()
