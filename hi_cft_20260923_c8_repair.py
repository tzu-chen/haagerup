"""Reconstruct the stress from its exact current-annihilation space.

Four low-complexity coefficients determine it; exact OPEs, not closeness,
are the final acceptance test. Numerics are used only to compare the result.
"""
from fractions import Fraction as Q
import hashlib,json,resource,signal,math
from pathlib import Path
import hi_cft_20260923_c8_exact as x

def kernel(rows,n):
    work=[r[:] for r in rows if any(r)];rank=0;pivots=[]
    for col in range(n):
        found=next((j for j in range(rank,len(work)) if work[j][col]),None)
        if found is None:continue
        work[rank],work[found]=work[found],work[rank]
        p=work[rank][col];work[rank]=[a/p for a in work[rank]]
        for j in range(len(work)):
            if j!=rank and work[j][col]:
                a=work[j][col];work[j]=[b-a*c for b,c in zip(work[j],work[rank])]
        pivots.append(col);rank+=1
    free=[i for i in range(n) if i not in pivots];basis=[]
    for col in free:
        v=[Q(0)]*n;v[col]=Q(1)
        for i,p in enumerate(pivots):v[p]=-work[i][col]
        basis.append(v)
    return basis

def value(a):return float(a[0])+float(a[1])*math.sqrt(13)+1j*math.sqrt(3)*(float(a[2])+float(a[3])*math.sqrt(13))

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('120-second cap')));signal.alarm(120)
    source=Path('hi_cft_20260923_c8_exact_fields_seed_v3.json');data=json.loads(source.read_text())
    row=data['fields'][-1];e=x.read_field(row);states=list(e);positions={s:i for i,s in enumerate(states)};rows=[]
    for current in x.LEFT+x.RIGHT:
        for mode in (0,1):
            matrix={}
            for j,state in enumerate(states):
                out=x.mode(current,mode,{state:x.ONE})
                for s,a in out.items():
                    assert a[1:]==(0,0,0)
                    matrix.setdefault(s,[Q(0)]*len(states))[j]=a[0]
            rows.extend(matrix.values())
    basis=kernel(rows,len(states));assert len(basis)==4
    ordered=sorted(range(len(states)),key=lambda i:max([abs(c.numerator) for c in e[states[i]]]+[c.denominator for c in e[states[i]]]))
    selected=[];equations=[];remaining=4
    for i in ordered:
        equation=[v[i] for v in basis];nullity=len(kernel(equations+[equation],4))
        if nullity<remaining:
            equations.append(equation);selected.append(i);remaining=nullity
        if remaining==0:break
    inverse=x.inverse(equations);rhs=[e[states[i]] for i in selected]
    coefficients=[sum((x.A(a)*b for a,b in zip(row,rhs)),x.ZERO_A) for row in inverse]
    corrected={s:sum((coefficients[j]*basis[j][i] for j in range(4)),x.ZERO_A) for i,s in enumerate(states)}
    assert not x.vadd((1,x.mode(corrected,1,corrected)),(-2,corrected)),'exact stress reconstruction'
    assert x.mode(corrected,3,corrected)=={(x.ZERO,()):x.A(Q(1200,1271))}
    changes=[]
    for item in row['coefficients']:
        s=tuple(item['momentum']),tuple(item['oscillators']);a=corrected[s]
        numeric=complex(*item['numeric']);assert abs(value(a)-numeric)<1e-10
        if a!=e[s]:changes.append({'state':s,'old':list(map(str,e[s])),'new':list(map(str,a))})
        item['Qsqrt13_sqrtminus3']=[list(map(str,a[:2])),list(map(str,a[2:]))]
    row['exact_stress_reconstruction']=True
    data['stress_repair']={'commutant_dimension':4,'interpolation_indices':selected,'corrected_coefficients':changes,
                          'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=Path('hi_cft_20260923_c8_exact_fields.json');assert not path.exists()
    path.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data['stress_repair']))

if __name__=='__main__':main()
