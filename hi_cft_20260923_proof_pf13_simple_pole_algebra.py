"""Derive the W3-W5 simple pole by Jacobi and self-skew symmetry.

This is independent of a large weight-seven lattice product. Its input
identities are (5.4), (5.7), and the upper poles in (A.2), each covered by
the separate exact lattice checks. All polynomial reordering corrections
are displayed in the accompanying mathematical note.
"""
from fractions import Fraction as Q
import json,hashlib
from pathlib import Path


def main():
    c=Q(8,5);l=Q(14,473);beta=Q(2,5)
    A=32*l/5;B=-48*l/5;C=Q(2,15)*(-5+2*l*(c-1))
    t=Q(8,3)*(5-2*l*(2+c));a0=31-16*l*(2+c)
    f2=[64*l,Q(75,2)-4*l*(13+5*c),Q(1,12)*(-25+8*l*(9+5*c))]
    f3=[95-16*l*(11+4*c),128*l,10+8*l*(c-1)]
    f4=110-32*l*(2+c);f5=-Q(4,3)*(-175+64*l*(2+c))
    # b_1 b in basis W6,:Lb:,:aa:,:d2L L:,:dL dL:,d2b,d4L.
    b1=[2*beta,2*A,6*B,beta*f2[0]+A,beta*f2[0]+B,
        -t/2+beta*f2[1]+2*A+9*C,t/12+beta*f2[2]-A/6+C/2]
    expected_b1=[Q(4,5),64*l/5,-288*l/5,32*l,16*l,
                 Q(1,15)*(35-4*l*(19+11*c)),Q(1,90)*(-5+4*l*(7+23*c))]
    assert b1==expected_b1,(b1,expected_b1)
    # b_3 b in basis b,:LL:,d2L; b_5 b is a multiple of L.
    b3=[a0+(4*beta-1)*f3[0]+12*A+8*B+24*C,
        (4*beta-1)*f3[1]+8*A,
        beta*f4+(4*beta-1)*f3[2]+6*A+60*C]
    assert b3==[72-48*l*(3+c),128*l,10+8*l*(c-1)]
    b5=(6*beta-1)*f5+A*(2*c+64)+20*B+240*C
    assert b5==-Q(4,3)*(-125+32*l*(2+c))
    # Weight-seven basis: dW6,:L db:,:dL b:,:d3L L:,
    # :d2L dL:,:da a:,d3b,d5L.
    a1R=[0,Q(3,2)*A,B,-A/12,0,3*A+5*B,A/4+Q(5,2)*C,-A/16-C/4]
    Db1=[b1[0],b1[1],b1[1],b1[3],b1[3]+2*b1[4],2*b1[2],
         b1[5]+b1[2]/12,b1[6]-b1[2]/60+b1[4]/60]
    D3b3=[0,0,0,2*b3[1],6*b3[1],0,b3[0],b3[1]/5+b3[2]]
    D5b5=[0,0,0,0,0,0,0,b5]
    DW6=[1,0,0,0,0,0,0,0]
    result=[(beta*a+r-Q(1,4)*s+Q(1,48)*t-Q(1,480)*u)/(1-beta)
            for a,r,s,t,u in zip(DW6,a1R,Db1,D3b3,D5b5)]
    expected=[Q(1,3),32*l/3,-64*l/3,-16*l/3,0,0,
              -Q(5,4)+Q(2,3)*l*(1+c),Q(5,72)-l*(13+5*c)/45]
    assert result==expected,(result,expected)
    out={'exact_A2_simple_pole_from_Jacobi_and_skew':True,
         'requires_exact_first_row_upper_poles':True,
         'c':str(c),'lambda':str(l),'coefficients':list(map(str,result)),
         'derived_b1b':list(map(str,b1)),'derived_b3b':list(map(str,b3)),'derived_b5b':str(b5),
         'scope':'Exact scalar verification of the displayed algebraic derivation, conditional only on the separately checked input OPEs.',
         'source_sha256':{str(Path(__file__)):hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
    path=Path('hi_cft_20260923_proof_pf13_simple_pole_algebra.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))


if __name__=='__main__':main()
