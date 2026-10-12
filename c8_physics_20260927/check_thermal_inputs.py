"""Verify the supplied100-digit pi enclosure by exact Machin alternating sums.

No floating arithmetic or generator imports; <30MiB, use512MiB guard.
"""
import ast
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent


def arctan_bounds(q,n):
    s=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0))
    remainder=F(1,(2*n+1)*q**(2*n+1))
    return (s,s+remainder) if n%2==0 else (s-remainder,s)


def main():
    source=HERE/'spectrum.py'
    tree=ast.parse(source.read_text())
    values=[node.value.value for node in tree.body if isinstance(node,ast.Assign)
            and any(isinstance(t,ast.Name) and t.id=='PI_LO' for t in node.targets)
            and isinstance(node.value,ast.Constant)]
    assert len(values)==1 and isinstance(values[0],str)
    declared_lo=F(values[0]);declared_hi=declared_lo+F(1,10**100)
    alo,ahi=arctan_bounds(5,80)
    blo,bhi=arctan_bounds(239,25)
    lower,upper=16*alo-4*bhi,16*ahi-4*blo
    assert declared_lo <= lower < upper <= declared_hi
    tangent2=2*F(1,5)/(1-F(1,5)**2)
    tangent4=2*tangent2/(1-tangent2**2)
    assert tangent2==F(5,12) < 1
    assert (tangent4-F(1,239))/(1+tangent4*F(1,239))==1
    report={'status':'PASS','identity':'pi=16 atan(1/5)-4 atan(1/239)',
            'method':'Alternating rational sums with remainder bounds. Tangent addition and the principal-angle range justify Machin identity.',
            'series_terms':{'atan_1_over_5':80,'atan_1_over_239':25},
            'declared_lower':str(declared_lo),'declared_upper':str(declared_hi),
            'proved_lower':str(lower),'proved_upper':str(upper),
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),source]},
            'scope':'Certifies the constant supplied to thermal intervals; does not formalize Decimal exp/log or the CFT analytic premises.'}
    (HERE/'thermal_input_check.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','pi_enclosure_decimal_digits':100,'rational_series_terms':105}))


if __name__=='__main__':
    main()
