"""Exact small-order mixed-characteristic cubic ideal tests.

Work over Z with 8 in the ideal and delta satisfying its quadratic.
Impose all inverse norms, the fixed origin, and the quartic
convolution equations. Test every polynomial cubic residual
multiplied by 1, 2, and 4 against a strong standard basis.
"""

import argparse
import os
from pathlib import Path
import resource
import subprocess
import tempfile
import time


def source(n, add_residue_q):
    def w(a):
        a %= n
        return f'x{a}' if a else '(-1)'

    def core(g, h):
        g, h = g % n, h % n
        if g == h == 0:
            return 'd*(d-2)'
        if not g or not h or g == h:
            return '(-d)'
        return f'{w(g)}*{w(h-g)}*{w(-h)}'

    equations = ['8', f'd^2-{n}*d-1']
    equations += [f'{w(a)}*{w(-a)}-d' for a in range(1, (n+1)//2)]
    for r in range(1, n):
        conv = '+'.join(f'{w(a)}*{w(2*r-a)}' for a in range(n))
        equations.append(f'{w(r)}^2*({conv})+d*(d-1)*{w(2*r)}')
    if add_residue_q:
        for g in range(1, n):
            for h in range(1, n):
                q = '+'.join(f'({core(g+a,h)})*({core(h,a)})' for a in range(n))
                equations.append('4*('+q+')')
    lines = [f'ring R=integer,(d,{",".join(w(a) for a in range(1,n))}),dp;',
             'number eight=8; number four=4;',
             'print("COEFFICIENT_CHECK="+string(eight)+","+string(four));',
             'ideal I='+','.join(equations)+';', 'ideal J=std(I);',
             'print("BASIS_SIZE="+string(size(J)));', f'matrix D[{n}][{n}];']
    for g in range(n):
        for h in range(n):
            lines.append(f'D[{g+1},{h+1}]={core(g,h)};')
    lines += [f'int n={n};', 'int g; int h; int k; int l; int a; int b;',
              'poly c;', 'intvec failures=0,0,0;', 'intvec factors=1,2,4;',
              'for(g=0;g<n;g++){for(h=0;h<n;h++){for(k=0;k<n;k++){for(l=0;l<n;l++){',
              'c=0;', 'for(a=0;a<n;a++){c=c+D[a+1,(g+h)%n+1]*D[g+1,(a+k)%n+1]*D[h+1,(a+l)%n+1];}',
              'c=c-d*(d-1)*D[(g+l)%n+1,k+1]*D[(h+k)%n+1,l+1];',
              'if(g==0 && h==0){c=c+d^2*(d-1)^3;}',
              'for(b=1;b<=3;b++){if(reduce(factors[b]*c,J)!=0){failures[b]=failures[b]+1;}}',
              '}}}}', 'print("C_FAILURES_1_2_4="+string(failures));',
              'print("COMPLETE_MOD8_C_IDEAL");', 'quit;']
    return '\n'.join(lines)+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[3, 5, 7])
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--add-residue-q', action='store_true')
    args = parser.parse_args()
    if any(n not in (3, 5, 7, 9) for n in args.orders):
        raise ValueError('This bounded exact test supports 3,5,7,9')
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='hi_convolution_mod8_') as directory:
        for n in args.orders:
            path = Path(directory) / f'n{n}.sing'
            path.write_text(source(n, args.add_residue_q))
            print(f'START n={n}; coefficient_ring=Z/8; residue_Q_imposed={args.add_residue_q}', flush=True)
            try:
                result = subprocess.run(['/usr/lib64/Singular/Singular', '-q'], input=path.read_text(),
                                        capture_output=True, text=True, timeout=args.timeout,
                                        env=dict(os.environ, SINGULAR_DATA_DIR='/usr/share'))
            except subprocess.TimeoutExpired as error:
                for value in (error.stdout, error.stderr):
                    if value:
                        print(value.decode() if isinstance(value, bytes) else value, end='', flush=True)
                print(f'INCOMPLETE n={n}; timeout_seconds={args.timeout}', flush=True)
                continue
            output = result.stdout+result.stderr
            print(output, end='', flush=True)
            crashed = any(marker in output.lower() for marker in
                          ('signal ', 'segment fault', 'bus error', 'trying to restart', 'internal error'))
            if result.returncode or '?' in output or crashed or 'COMPLETE_MOD8_C_IDEAL' not in output:
                raise ArithmeticError(f'Mixed-characteristic ideal computation failed at {n}')
            assert 'COEFFICIENT_CHECK=8,4' in output and 'BASIS_SIZE=0' not in output
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'child_peak_RSS_MiB={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/1024:.2f}', flush=True)


if __name__ == '__main__':
    main()
