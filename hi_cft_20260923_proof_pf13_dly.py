"""Translate DLY Appendix B.1--B.3 to the canonical W6 relation.

Source: https://arxiv.org/html/0809.3630 . No lattice calculation here.
DLY generators are primary; Linshaw generators are recursive.
Run numerical checks only through hi_cft_safe_run.py.
"""
from fractions import Fraction as Q


def coefficients(k=13):
    k=Q(k); c=2*(k-1)/(k+2)
    # A3=r*a, with a_5 a=c/3. A4=alpha*b+beta*:LL:+gamma*d2L.
    r2=12*k**3*(k-2)*(k-1)*(3*k+4)/(c/3)
    s=-162*k**3*(k-2)*(k+2)*(3*k+4)/(16*k+17)
    t=288*k**3*(k-2)*(k+2)**2*(3*k+4)/(16*k+17)
    h=36*k*(2*k+3)/(16*k+17)
    alpha,beta,gamma=r2/h,-t/h,-s/(2*h)
    # A5/r=delta*d+epsilon*:La:+zeta*d2a; d=a_1 b.
    d1=1248*k**2*(k-3)*(k+2)*(2*k+1)*(2*k+3)/(64*k+107)
    d2=-48*k**2*(k-3)*(2*k+1)*(2*k+3)*(2*k+7)/(64*k+107)
    d3=-12*k*(3*k+4)*(16*k+17)/(64*k+107)
    delta=alpha/d3
    epsilon=(6*beta-d1)/d3
    zeta=(Q(3,2)*beta+7*gamma-d2/2)/d3
    # DLY A3_1 A5, in order L_-5, L_-3 L, (L_-2)^2,
    # L_-1^3, A3_-1 A3, L_-1 A4, A4_-3.
    v=[-6480*k**4*(k+2)*(k+3)*(2*k+3)*(3*k+4)*(12*k**2+8*k-17)/(16*k+17),
       -360*k**4*(k+2)**2*(2*k+3)*(3*k+4)*(32*k**2+797*k+863)/(16*k+17),
       45*k**4*(k+2)**2*(2*k+3)*(3*k+4)*(1408*k**2+1315*k-977)/(16*k+17),
       240*k**4*(k+2)**3*(2*k+3)*(3*k+4)*(202*k-169)/(16*k+17),
       -15*k*(2*k+3)*(41*k+61),
       60*k**2*(k+2)*(404*k**2+1170*k+835)/(16*k+17),
       15*k**2*(2176*k**3+9481*k**2+13792*k+6708)/(2*(16*k+17))]
    # Canonical basis: :Lb:, :aa:, :L(:LL:):, :d2L L:,
    # :dL dL:, d2b, d4L. Normal ordering is not commutative:
    # :L d2L:=:d2L L:+d4L/6, d2:LL:=2:d2L L:+2:dL dL:+d4L/6.
    result=[v[5]*alpha, v[4]*r2, v[3]+v[5]*beta,
            v[1]/2+v[5]*gamma+v[6]*beta,
            v[2]+v[6]*beta, v[6]*alpha/2,
            v[0]/24+v[5]*gamma/6+v[6]*(beta/12+gamma/2)]
    # a_1 :La: = :Lb:+3:aa:; a_1 d2a=2d2b-d4L/6.
    result[0]-=r2*epsilon
    result[1]-=3*r2*epsilon
    result[5]-=2*r2*zeta
    result[6]+=r2*zeta/6
    result=[v/(r2*delta) for v in result]
    return result,dict(r_squared=r2,alpha=alpha,beta=beta,gamma=gamma,
                       delta=delta,epsilon=epsilon,zeta=zeta)


if __name__=='__main__':
    import json
    from pathlib import Path
    result,change=coefficients()
    data=json.loads(Path('hi_cft_20260923_proof_pf13_truncation.json').read_text())
    observed=[Q(a[0]) for a in data['coefficients']]
    assert all(a[1:]==['0','0','0'] for a in data['coefficients'])
    assert result==observed,(result,observed)
    out={'matches_DLY_Appendix_B_exactly':True,'level':13,
         'coefficients':list(map(str,result)),
         'change_of_generators':{k:str(v) for k,v in change.items()},
         'source':'https://arxiv.org/html/0809.3630#S8',
         'scope':'Independent published parafermion coefficients, transformed to the canonical normal-order convention.'}
    path=Path('hi_cft_20260923_proof_pf13_dly.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
