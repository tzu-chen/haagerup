"""Exact quadratic-to-cubic checks after quotienting the cyclic character gauge.

The Laurent row coordinates have (n-1)/2 variables. One extra variable
saturates their product. Singular std certifies actual ideal membership.
This file does not use the unverified modular candidate at order 11.
"""

from pathlib import Path
from collections import defaultdict
import argparse
import subprocess
import tempfile
import sympy as sp
from hi_beta_reductions import beta_representatives


def singular_source(n):
    if n < 3 or n % 2 == 0:
        raise ValueError("the order must be odd and at least 3")
    m=(n-1)//2;d=sp.Symbol('d')
    zero=(0,)*m
    pref=[list(zero) for _ in range(n)]
    for h in range(2,n):
        pref[h]=pref[h-1].copy();pref[h][min(h,n+1-h)-2]+=1

    def B(g,h):
        g%=n;h%=n
        if g==h==0:return {zero:d-2}
        if g==0 or h==0 or g==h:return {zero:sp.Integer(-1)}
        sign=1 if g<h else -1
        a,b=sorted((g,h))
        exp=tuple(sign*(pref[b][i]-pref[a][i]-pref[b-a][i]) for i in range(m))
        return {exp:sp.Integer(1) if sign==1 else d}

    def mul(*args):
        out={zero:sp.Integer(1)}
        for arg in args:
            nxt=defaultdict(lambda:sp.Integer(0))
            for x,a in out.items():
                for y,b in arg.items():nxt[tuple(u+v for u,v in zip(x,y))]+=a*b
            out=nxt
        return out

    def polynomial(terms):
        out=defaultdict(lambda:sp.Integer(0))
        for term in terms:
            for exp,coef in term.items():out[exp]+=coef
        out={exp:sp.rem(coef,d*d-n*d-1,d) for exp,coef in out.items()}
        out={exp:coef for exp,coef in out.items() if coef!=0}
        if not out:return '0'
        mins=[min(exp[i] for exp in out) for i in range(m)]
        pieces=[]
        for exp,coef in sorted(out.items()):
            mon='*'.join(f'r{i+1}^{exp[i]-mins[i]}' for i in range(m) if exp[i]>mins[i])
            pieces.append('('+str(coef).replace('**','^')+')'+('*'+mon if mon else ''))
        return '+'.join(pieces)

    qpolys=set()
    for g in range(1,n):
        for h in range(1,n):
            q=polynomial([mul(B(g+j,h),B(h,j)) for j in range(n)])
            if q!='0':qpolys.add(q)
    ring=[f'r{i+1}' for i in range(m)]+['t']
    out=[f'ring R=(0,d),({",".join(ring)}),dp;',f'minpoly=d^2-{n}*d-1;','ideal I='+','.join(sorted(qpolys))+',t*'+'*'.join(ring[:-1])+'-1;','option(redSB);','ideal J=std(I);','print("ROW GROEBNER BASIS FINISHED");','print("basis_size="+string(size(J)));','print("scheme_length="+string(vdim(J)));','poly f;','int failures=0;']
    reps,_=beta_representatives(n)
    for g,h,k,l in reps:
        terms=[mul(B(j,g+h),B(g,j+k),B(h,j+l)) for j in range(n)]
        terms.append(mul({zero:1-d},B(g+l,k),B(h+k,l)))
        out+=['f='+polynomial(terms)+';','if(reduce(f,J)!=0){failures=failures+1;}']
    out += [f'print("beta_representatives={len(reps)}");', 'print("membership_failures="+string(failures));', 'if(failures==0){print("EXACT ROW IDEAL MEMBERSHIP PASSED");}', 'quit;']
    return "\n".join(out)+"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3,5,7,9])
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--source', type=Path)
    args = parser.parse_args()
    if args.source:
        if len(args.orders) != 1:
            parser.error('--source requires exactly one order')
        args.source.write_text(singular_source(args.orders[0]))
        return
    for n in args.orders:
        with tempfile.TemporaryDirectory(prefix='hi_row_ideal_') as tmp:
            path = Path(tmp) / f'order_{n}.sing'
            path.write_text(singular_source(n))
            try:
                result = subprocess.run(['Singular','-q',str(path)],
                                        capture_output=True,text=True,timeout=args.timeout)
            except subprocess.TimeoutExpired:
                raise SystemExit(f'n={n}: timeout; no row ideal implication certified')
        output = result.stdout + result.stderr
        print(f'CASE n={n}\n{output}', end='', flush=True)
        if result.returncode or '?' in output or 'EXACT ROW IDEAL MEMBERSHIP PASSED' not in output:
            raise SystemExit('The exact row ideal check did not pass')
    print('ALL REQUESTED ROW IDEAL CHECKS PASSED')


if __name__ == '__main__':
    main()
