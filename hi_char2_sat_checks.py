"""Exact checks of the SAT arithmetic on off-solution norm data.

The checker fixes all seed bits, then compares the encoded trace formula
against direct integer finite-field evaluation, including nonzero residuals.
Requires the same Python 3.9 pycryptosat installation as hi_char2_sat.py.
"""

from hi_char2_sat import Search
from hi_char2_frobenius import field_parameters

def coordinates(columns, value):
    pivots={}
    for j,col in enumerate(columns):
        mask=1<<j
        while col:
            b=col.bit_length()-1
            if b not in pivots:
                pivots[b]=(col,mask);break
            col^=pivots[b][0];mask^=pivots[b][1]
    answer=0
    while value:
        b=value.bit_length()-1
        value^=pivots[b][0];answer^=pivots[b][1]
    return answer

for n in [3,9,27,81]:
    s=Search(n); f=s.field
    _,(_,d,xi,factors)=field_parameters(n)
    order=(1<<(f.degree//2))+1
    vals=[f.power(d,2)]*n;vals[0]=1
    assumptions=[]
    for scale,variables in s.seed_positions:
        local_torus=(1<<(f.degree//(2*scale)))+1
        first=f.multiply(f.power(d,2),f.power(xi,order//local_torus*(1+scale)))
        cc=coordinates(s.normal,first)
        assert all(((cc>>j)&1)==((cc>>(j%len(variables)))&1) for j in range(f.degree))
        assumptions += [v if cc>>j&1 else -v for j,v in enumerate(variables)]
        a=scale;z=first
        for _ in range(2*n//(3*scale)):
            vals[a]=z;a=2*a%n;z=f.power(z,4)
        assert a==scale and z==first
    pairs=list(dict.fromkeys((g%n,h%n) for g,h in [(1,1),(2,1),(n//3,1),(1,n-1),(2,3),(4,7),(n//3,n//3)] if g%n and h%n))
    symbolic=[s.quadratic_value(g,h) for g,h in pairs]
    sat,model=s.circuit.solver.solve(assumptions=assumptions,time_limit=30)
    assert sat is True,(n,sat)
    assert [f.evaluate(w,model) for w in s.phases]==vals
    residuals=[]
    for value,(g,h) in zip(symbolic,pairs):
        direct=s.numeric_quadratic(vals,g,h)
        assert f.evaluate(value,model)==direct,(n,g,h)
        residuals.append(bool(direct))
    print('OFF-SOLUTION EXACT TRACE/CIRCUIT',n,'pairs',pairs,'nonzero',sum(residuals),'variables',s.circuit.count,flush=True)
print('ALL EXACT CIRCUIT CHECKS PASSED')
