"""Exact small reverse-Weil theta audit, root safe-launcher only.

21*cosets*11^4 integer points, sparse scalar q-series only. Expected
peak<0.05GiB, no large matrices, AS cap1GiB. Not a categorification.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import hashlib
import json
from pathlib import Path
import resource
from time import monotonic


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    started=monotonic()
    # G-(1/4)I has positive leading determinants7/4,33/16,119/64,
    # 2209/256. Norm<=6 therefore implies each coordinate<sqrt24.
    # Representatives have coordinates in[-10/21,10/21], so box[-5,5]
    # is exhaustive for all series below through q^3.
    theta, harmonic={},{}
    for t in range(21):
        shift=tuple(((t*g+10)%21)-10 for g in (16,11,6,1))
        th,hh=defaultdict(F),defaultdict(F)
        for coords in product(range(-5,6),repeat=4):
            a,b,c,d=(21*n+s for n,s in zip(coords,shift))
            norm_num=2*a*a+2*b*b+2*c*c+6*d*d-2*a*b-2*b*c-2*c*d
            assert norm_num>=0 and norm_num%42==0
            exponent=norm_num//42
            if exponent<=63:
                th[exponent]+=1
                hh[exponent]+=F(norm_num-21*d*d,441)
        theta[t],harmonic[t]=dict(th),dict(hh)
    assert theta[4].get(2)==1 and theta[10].get(2,0)==0
    assert theta[0][21]==12 and harmonic[0][21]==24
    projected={}
    for t in range(21):
        other=13*t%21
        th={k:(theta[t].get(k,F(0))+theta[other].get(k,F(0)))/2
            for k in set(theta[t])|set(theta[other])}
        hh={k:(harmonic[t].get(k,F(0))+harmonic[other].get(k,F(0)))/2
            for k in set(harmonic[t])|set(harmonic[other])}
        ff={k:(1-F(6*k,21))*v for k,v in th.items()}
        for n in range(1,4):
            sigma=sum(j for j in range(1,n+1) if n%j==0)
            for k,v in th.items():
                if k+21*n<=63:
                    ff[k+21*n]=ff.get(k+21*n,F(0))-24*sigma*v
        projected[t]=(th,hh,ff)
    th,hh,ff=projected[4]
    assert (th[2],hh[2],ff[2])==(F(1,2),F(-2,7),F(3,14))
    assert projected[0][2][0]==1 and projected[0][2][21]==-84
    assert projected[0][1][21]==24
    # Evaluate the two affine coefficient equations at A=0 and1;
    # their linearity is explicit in the saved derivation.
    ns=[]
    for polar_top in (0,1):
        coupling=(-polar_top-ff[2])/hh[2]
        currents=(94+projected[0][2][21]+coupling*projected[0][1][21])/2
        assert currents==14+42*polar_top
        ns.append(str(currents))
    def ser(series):
        return [[k,str(v)] for k,v in sorted(series.items()) if v]
    result={'gram':[[2,-1,0,0],[-1,2,-1,0],[0,-1,2,-1],[0,0,-1,6]],
            'quadratic_form':'8t^2/21 = -r^2/7-s^2/3 at t=9r+7s',
            'projection':'t -> average(t,13t)',
            'quadratic_harmonic':'norm-21*x_last^2',
            'weight_four_reference':'F=-6D_2Theta',
            'series_exponent_unit':'q^(1/21)',
            'raw_polar_theta_counts_t4_t10':[str(theta[4][2]),str(theta[10].get(2,0))],
            'projected_polar_theta_H_F':[str(th[2]),str(hh[2]),str(ff[2])],
            'vacuum_H_F_q_coefficients':['24','-84'],
            'conditional_current_formula':'dimV1=14+42A, A>=0',
            'current_formula_at_A0_A1':ns,
            'projected_series':{str(t):[ser(v) for v in triple] for t,triple in projected.items()},
            'scope':'Exact theta coefficients and arithmetic identity; modular category/orientation identification is separate.',
            'seconds':monotonic()-started,
            'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output=Path('hi_cft_20260923_next_m3_reverse_theta_check.json')
    assert not output.exists()
    output.write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='projected_series'},flush=True)


if __name__=='__main__':
    main()
