"""Certify the order-11 quadratic-to-cubic ideal containment exactly.

Run: python hi_row11_verify.py --timeout 600

A saved homogeneous candidate is verified by exact rational std and a
Hilbert-series sandwich against an independently computed finite-field
basis. No probabilistic ideal equality from nfmodStd is assumed.
"""

import argparse
import gzip
from pathlib import Path
import subprocess
import tempfile

from sympy import isprime, legendre_symbol

from hi_row_ideal import singular_source as row_source


def singular_source():
    assert isprime(32003) and legendre_symbol(125, 32003) == -1
    directory = Path(__file__).resolve().parent
    with gzip.open(directory / 'hi_row11_homogeneous_basis.txt.gz', 'rt') as f:
        homogeneous = f.read().strip()
    affine = (directory / 'hi_row11_basis.txt').read_text().strip()
    row = row_source(11)
    generators = row.split('ideal I=')[1].split(';')[0]
    cubic_checks = row.split('poly f;')[1].rsplit('quit;', 1)[0]
    return '\n'.join([
        'ring K=(0,d),(r1,r2,r3,r4,r5,t,z),dp;',
        'minpoly=d^2-11*d-1;',
        f'ideal I={generators};',
        'I=homog(I,z);',
        f'ideal H={homogeneous};',
        'int certification_failures=0; int j;',
        'ideal HH=homog(H,z);',
        'for(j=1;j<=size(H);j++){if(H[j]!=HH[j])'
        '{certification_failures=certification_failures+1;}}',
        'print("homogeneity_failures="+string(certification_failures));',
        # Exact rational arithmetic is substantially faster than direct
        # number-field arithmetic on this large homogeneous candidate.
        'ring Q=0,(r1,r2,r3,r4,r5,t,z,d),(dp(7),dp(1));',
        'ideal HQ=imap(K,H); HQ=HQ,d^2-11*d-1;',
        'option(pure_gb); ideal GQ=std(HQ);',
        'print("EXACT RATIONAL STANDARD BASIS FINISHED");',
        'setring K;',
        'ideal G=imap(Q,GQ); G=simplify(G,2);',
        # The block order puts all ordinary variables before d, so a
        # standard basis descends to the coefficient field Q[d]/(minpoly).
        'attrib(G,"isSB",1);',
        'int input_remainders=size(reduce(I,G));',
        'certification_failures=certification_failures+input_remainders;',
        'print("input_inclusion_remainders="+string(input_remainders));',
        'bigintvec hk=hilb(G,1);',
        'print("characteristic_zero_hilbert_numerator="+string(hk));',
        # 32003 is prime, is unramified in Q(sqrt(5)), and the displayed
        # quadratic minimal polynomial remains irreducible modulo it.
        'ring M=(32003,d),(r1,r2,r3,r4,r5,t,z),dp;',
        'minpoly=d^2-11*d-1;',
        'ideal IM=imap(K,I); ideal GM=std(IM);',
        'bigintvec hp=hilb(GM,1);',
        'print("finite_field_hilbert_numerator="+string(hp));',
        'if(hk!=hp){certification_failures=certification_failures+1;}',
        'setring K;',
        'ideal D=subst(G,z,1); attrib(D,"isSB",1);',
        f'ideal A={affine};',
        'ideal J=std(A);',
        'int affine_remainders=size(reduce(J,D))'
        '+size(reduce(subst(I,z,1),J));',
        'certification_failures=certification_failures+affine_remainders;',
        'print("affine_inclusion_remainders="+string(affine_remainders));',
        # Remove the unused homogenizing variable before measuring the
        # affine quotient length or checking cubic polynomials.
        'ring A11=(0,d),(r1,r2,r3,r4,r5,t),dp;',
        'minpoly=d^2-11*d-1;',
        'ideal J=imap(K,J); attrib(J,"isSB",1);',
        'print("affine_basis_size="+string(size(J)));',
        'print("affine_scheme_length="+string(vdim(J)));',
        'poly f;',
        cubic_checks,
        'if(certification_failures==0 && failures==0)'
        '{print("EXACT ORDER-11 HILBERT AND CUBIC CERTIFICATE PASSED");}',
        'quit;',
    ]) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--source', type=Path)
    args = parser.parse_args()
    source = singular_source()
    if args.source:
        args.source.write_text(source)
        return
    with tempfile.TemporaryDirectory(prefix='hi_row11_verify_') as tmp:
        path = Path(tmp) / 'verify.sing'
        path.write_text(source)
        try:
            result = subprocess.run(['Singular', '-q', str(path)],
                                    capture_output=True, text=True,
                                    timeout=args.timeout)
        except subprocess.TimeoutExpired:
            raise SystemExit('Timeout: this verification run did not finish')
    output = result.stdout + result.stderr
    print(output, end='')
    marker = 'EXACT ORDER-11 HILBERT AND CUBIC CERTIFICATE PASSED'
    if result.returncode or '?' in output or marker not in output:
        raise SystemExit('The order-11 certificate verification did not pass')


if __name__ == '__main__':
    main()
