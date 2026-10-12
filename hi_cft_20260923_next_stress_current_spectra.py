"""Exact characteristic polynomials for candidate stress zero modes on B1."""
import json,resource,signal,hashlib
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as Q
import sympy as sp
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_proof_general_modes_v2 as gen
from hi_cft_20260923_proof_pf13_ope import read

def charpoly(M):
    n=len(M);I=[[x.A(i==j) for j in range(n)] for i in range(n)]
    B=I;coeff=[x.ONE]
    for k in range(1,n+1):
        C=[[sum((M[i][r]*B[r][j] for r in range(n)),x.A(0)) for j in range(n)] for i in range(n)]
        a=-sum((C[i][i] for i in range(n)),x.A(0))/k;coeff.append(a)
        B=[[C[i][j]+a*I[i][j] for j in range(n)] for i in range(n)]
    assert all(not a for row in B for a in row)
    return coeff

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('180-second cap')));signal.alarm(180)
    gen.install(1);states=[(x.ZERO,(i,)) for i in range(8)]+[(a,()) for a in lat.ROOTS]
    blocks=defaultdict(list)
    for s in states:blocks[x.weight(s)].append(s)
    axes=json.loads(Path('hi_cft_20260923_proof_remaining_axes.json').read_text())
    pf13=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text())
    records={};t=sp.Symbol('t')
    for label,e in [('PF13_control',read(pf13['stress'])),('c32over19',read(axes['first_stress'])),('c182over95',read(axes['second_stress']))]:
        rows=[];irrational=[]
        for wt,block in sorted(blocks.items()):
            columns=[x.mode(e,1,{s:x.ONE}) for s in block]
            assert all(set(v)<=set(block) for v in columns)
            M=[[v.get(s,x.A(0)) for v in columns] for s in block];coeff=charpoly(M)
            rational=all(not any(a[1:]) for a in coeff)
            row={'Cartan_weight':list(wt),'dimension':len(block),'charpoly_coefficients':[list(map(str,a)) for a in coeff]}
            if rational:
                poly=sp.Poly.from_list([sp.Rational(a[0].numerator,a[0].denominator) for a in coeff],t)
                _,factors=sp.factor_list(poly);row['factorization']=str(sp.factor(poly.as_expr()))
                nonlin=[str(f.as_expr()) for f,m in factors if f.degree()>1]
                row['irreducible_non_linear_factors']=nonlin
                if nonlin:irrational.append({'Cartan_weight':list(wt),'factors':nonlin})
            rows.append(row)
        records[label]={'blocks':rows,'irrational_eigenvalue_blocks':irrational}
        print(json.dumps({'label':label,'irrational_eigenvalue_blocks':irrational}),flush=True)
    out={'records':records,'scope':'Exact ambient-current restrictions. Irreducible rational polynomial factors of degree >1 prove irrational stress eigenvalues and obstruct a regular rational extension with this stress and rational conformal module weights.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__),Path('hi_cft_20260923_proof_remaining_axes.json'),Path('hi_cft_20260923_proof_pf13_exact.json'))}}
    path=Path('hi_cft_20260923_next_stress_current_spectra.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
