"""Explore algebraic field coefficients in an integral principal gauge.

PSLQ recognition from floating values is a conjecture, never a certificate.
"""
from fractions import Fraction as Q
import hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
from itertools import product
from math import sqrt
import numpy as np
import mpmath as mp
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_fields as fields

INVERSE=np.linalg.inv(lat.ROOT_COORD)
SCALE=np.array([1/sqrt(c) for c in (5,8,9,8,5,1,2,2)])

def convert(v):
    out={}
    for i,c in lat.vector_dict(v).items():
        alpha,osc=lat.BASES[2][i]
        c=c*np.prod(SCALE**np.array(alpha))/lat.osc_norm(osc)
        if not osc:lat.add_term(out,(alpha,()),c);continue
        for js in product(range(8),repeat=len(osc)):
            coefficient=c
            for k,j in zip(osc,js):coefficient*=INVERSE[k%8,j]
            mon=tuple(sorted(j+8*(k//8) for k,j in zip(osc,js)))
            lat.add_term(out,(alpha,mon),coefficient)
    return {s:c for s,c in out.items() if abs(c)>1e-10*max(map(abs,out.values()))}

def recognize(x):
    if abs(x)<1e-10:return ['0','0']
    candidates=[]
    for root in (1.,sqrt(13)):
        q=Q(float(x/root)).limit_denominator(50000)
        if abs(float(q)*root-x)<5e-13:
            candidates.append((max(abs(q.numerator),q.denominator),q,Q(0)) if root==1 else (max(abs(q.numerator),q.denominator),Q(0),q))
    v=mp.mpf(float(x))
    for tol in ('2e-12','2e-11','2e-10','2e-9','2e-8'):
        rel=mp.pslq(mp.matrix([1,mp.sqrt(13),v]),tol=mp.mpf(tol),maxcoeff=1000000,maxsteps=1000)
        if rel is None or rel[2]==0:continue
        a,b=Q(-int(rel[0]),int(rel[2])),Q(-int(rel[1]),int(rel[2]))
        if abs(float(a)+float(b)*sqrt(13)-x)>5e-13:continue
        candidates.append((max(map(abs,rel)),a,b))
    if not candidates:return None
    _,a,b=min(candidates)
    return [str(a),str(b)]

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('120-second cap')));signal.alarm(120)
    mp.mp.dps=40;t=monotonic();path=Path('hi_cft_20260923_c8_fields_precise.npz');W=np.load(path)['W2']
    records=[];pos=24
    vectors=[]
    for n,m,h,_ in fields.SPECS:
        vectors.append((n,m,h,W[:,pos],True));pos+=n*m
    vectors.append((1,1,2542,np.load('hi_cft_20260923_c8_ope_control.npz')['stress'],False))
    for n,m,h,vector,normalize in vectors:
        z=convert(vector)
        key=max(z,key=lambda s:abs(z[s]));scale=z[key] if normalize else 1
        normalized={s:c/scale for s,c in z.items()}
        rows=[];misses=0;maxerr=0.;maxcoeff=0
        for state,c in normalized.items():
            recognized=[recognize(c.real),recognize(c.imag/sqrt(3))]
            for part,number in zip(recognized,(c.real,c.imag/sqrt(3))):
                if part is None:misses+=1
                else:
                    a,b=map(Q,part);maxerr=max(maxerr,abs(float(a)+float(b)*sqrt(13)-number))
                    maxcoeff=max(maxcoeff,abs(a.numerator),a.denominator,abs(b.numerator),b.denominator)
            rows.append({'momentum':state[0],'oscillators':state[1],'numeric':[c.real,c.imag],'Qsqrt13_sqrtminus3':recognized})
        record={'dimensions':[n,m],'e_weight':str(Q(h,1271)),'coefficient_count':len(rows),
                'unrecognized':misses,'max_recognition_error':maxerr,'max_rational_height':maxcoeff,'coefficients':rows}
        records.append(record);print({k:v for k,v in record.items() if k!='coefficients'},flush=True)
    out={'fields':records,'seconds':monotonic()-t,'scope':'Floating reconstruction conjectures, requiring subsequent exact verification.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (path,Path(__file__))}}
    target=Path('hi_cft_20260923_c8_exact_fields_seed_v3.json');assert not target.exists()
    target.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
