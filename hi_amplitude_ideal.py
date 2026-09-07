"""Exact elimination of the exceptional amplitude from the quadratic equations.

Run: python hi_amplitude_ideal.py --orders 5 7 --timeout 600
The calculation uses Singular's exact std, not a reconstructed modular basis.
It describes a complex algebraic scheme; physical conjugation is an additional
condition. Quotient dimensions below count scheme length, not physical points.
"""

import argparse
from pathlib import Path
import subprocess
import tempfile


def singular_source(n):
    if n < 3 or n % 2 == 0:
        raise ValueError("the order must be odd and at least 3")
    b = ["(-t)"] + [f"x{j}" for j in range(1, n)]
    variables = b[1:] + ["v", "t"]
    polynomials = [f"x{j}*x{n-j}-1" for j in range(1, (n+1)//2)]
    for g in range(1, n):
        for h in range(1, n):
            polynomials.append("+".join(
                "*".join(b[j % n] for j in (m, h-m, -m-g, m+g-h))
                for m in range(n)))
    polynomials.append("v*t-1")
    out = [f'ring R=0,({",".join(variables)}),dp;',
           'option(redSB);', f'ideal I={",".join(polynomials)};',
           'ideal J=std(I);',
           'print("basis_size="+string(size(J)));',
           'print("dimension="+string(dim(J)));',
           'print("scheme_length="+string(vdim(J)));',
           f'ideal E=eliminate(J,{"*".join(variables[:-1])});',
           'E=std(E);', 'print("amplitude_elimination="+string(E));']
    # These are observed exact answers in two small orders, not a formula
    # presumed for other n. Test equality of elimination ideals both ways.
    expected = {5: '(t^2-1)*(t^4+5*t^2-1)',
                7: '(t^2-1)*(t^4+7*t^2-1)*(t^4-4*t^2-4)'}
    if n in expected:
        out += [f'ideal H=std(ideal({expected[n]}));',
                'if(size(reduce(E,H)) || size(reduce(H,E)))'
                '{print("ELIMINATION MISMATCH");quit;}',
                'print("EXACT ELIMINATION IDEAL EQUALITY PASSED");']
    for name, factor in [('Alltop', 't^2-1'),
                         ('HI', f't^4+{n}*t^2-1'),
                         ('SIC', f't^4-4*t^2-{n-3}')]:
        out += [f'ideal K{name}=std(J+ideal({factor}));',
                f'print("{name}_scheme_length="+string(vdim(K{name})));']
    out += ['print("EXACT AMPLITUDE CALCULATION PASSED");', 'quit;']
    return '\n'.join(out) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[5, 7])
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--source', type=Path)
    args = parser.parse_args()
    if args.source:
        if len(args.orders) != 1:
            parser.error('--source requires exactly one order')
        args.source.write_text(singular_source(args.orders[0]))
        return
    for n in args.orders:
        with tempfile.TemporaryDirectory(prefix='hi_amplitude_') as tmp:
            path = Path(tmp) / f'order_{n}.sing'
            path.write_text(singular_source(n))
            try:
                result = subprocess.run(['Singular', '-q', str(path)],
                                        capture_output=True, text=True,
                                        timeout=args.timeout)
            except subprocess.TimeoutExpired:
                raise SystemExit(f'n={n}: timeout; no elimination certified')
        output = result.stdout + result.stderr
        print(f'CASE n={n}\n{output}', end='', flush=True)
        if (result.returncode or '?' in output or
                'EXACT AMPLITUDE CALCULATION PASSED' not in output or
                'MISMATCH' in output):
            raise SystemExit('The exact amplitude calculation did not pass')
    print('ALL REQUESTED AMPLITUDE CHECKS PASSED')


if __name__ == '__main__':
    main()
