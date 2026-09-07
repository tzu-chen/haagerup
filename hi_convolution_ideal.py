"""Exact small-order test of inverse norms plus the quartic convolution.

The ideal has fixed origin W_0=-1, all inverse norms, and every
quartic H_r. Test its dimension and reduction of every nontrivial
Q polynomial in characteristic zero. This is a finite test, not
a uniform implication. Each small Singular run has a time limit.
"""

import argparse
import os
from pathlib import Path
import resource
import subprocess
import tempfile
import time


def source(n):
    def w(a):
        a %= n
        return f'x{a}' if a else '(-1)'

    # D = delta * B is polynomial under the inverse norms.
    def core(g, h):
        g, h = g % n, h % n
        if g == h == 0:
            return '(d*(d-2))'
        if not g or not h or g == h:
            return '(-d)'
        return f'({w(g)}*{w(h-g)}*{w(-h)})'

    variables = ','.join(w(a) for a in range(1, n))
    equations = [f'{w(a)}*{w(-a)}-d' for a in range(1, (n+1)//2)]
    for r in range(1, n):
        conv = '+'.join(f'{w(a)}*{w(2*r-a)}' for a in range(n))
        equations.append(f'{w(r)}^2*({conv})+d*(d-1)*{w(2*r)}')
    lines = [f'ring R=(0,d),({variables}),dp;', f'minpoly=d^2-{n}*d-1;',
             'option(redSB);', 'ideal I='+','.join(equations)+';', 'ideal J=std(I);',
             'print("H_NORM_DIM="+string(vdim(J)));', 'poly q;', 'int failures=0;']
    for g in range(1, n):
        for h in range(1, n):
            q = '+'.join(f'{core(g+a,h)}*{core(h,a)}' for a in range(n))
            lines += ['q=reduce('+q+',J);',
                      f'if(q!=0){{failures=failures+1;if(failures==1){{print("FIRST_Q={g},{h}");print(q);}}}}']
    lines += ['print("Q_FAILURES="+string(failures));', 'print("COMPLETE_H_NORM_IDEAL");', 'quit;']
    return '\n'.join(lines)+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7])
    parser.add_argument('--timeout', type=float, default=30)
    args = parser.parse_args()
    if any(n not in (3, 5, 7, 9) for n in args.orders):
        raise ValueError('This bounded exact test supports 3,5,7,9')
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='hi_convolution_ideal_') as directory:
        for n in args.orders:
            path = Path(directory) / f'n{n}.sing'
            path.write_text(source(n))
            print(f'START n={n}; characteristic=0; timeout_seconds={args.timeout}', flush=True)
            try:
                # Use the inspected executable directly: the distribution's
                # shell wrapper sources environment modules before exec.
                result = subprocess.run(['/usr/lib64/Singular/Singular', '-q'], input=path.read_text(),
                                        capture_output=True, text=True, timeout=args.timeout,
                                        env=dict(os.environ, SINGULAR_DATA_DIR='/usr/share'))
            except subprocess.TimeoutExpired as error:
                for partial in (error.stdout, error.stderr):
                    if partial:
                        print(partial.decode() if isinstance(partial, bytes) else partial, end='', flush=True)
                print(f'INCOMPLETE n={n}; timeout_seconds={args.timeout}', flush=True)
                continue
            output = result.stdout+result.stderr
            print(output, end='', flush=True)
            crashed = any(marker in output.lower() for marker in
                          ('signal ', 'segment fault', 'bus error', 'trying to restart', 'internal error'))
            if result.returncode or '?' in output or crashed or 'COMPLETE_H_NORM_IDEAL' not in output:
                raise ArithmeticError(f'Exact ideal computation failed at {n}')
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'child_peak_RSS_MiB={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/1024:.2f}', flush=True)


if __name__ == '__main__':
    main()
