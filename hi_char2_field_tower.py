"""Exact checks for the full-degree and cubic norm-lifting theorems in Section 65.

The uniform proofs are in the notes. These checks verify the off-solution
quadratic identity, the degrees of the saved row coordinates, and counts
of irreducible unitary cubics. No new HI existence claim is made.
Requires Python's standard library and PARI/GP.
"""

import json
from pathlib import Path
from random import Random
import subprocess

from hi_char2_small_field_obstruction import field_table, power, quadratic


def check_unit_period_identity():
    table = field_table(4, 0b10011)
    assert {power(table, 2, i) for i in range(15)} == set(range(1, 16))
    omega, xi = power(table, 2, 5), power(table, 2, 3)
    c, rng = omega ^ 1, Random(651)
    bottom_values = [table[c][power(table, xi, i)] for i in range(5)]
    for n in [9, 27, 81, 243]:
        g, checks, residuals = n//3, 0, set()
        for _ in range(4):
            lower = [1]*g
            for a in range(1, (g+1)//2):
                lower[a] = rng.randrange(1, 16)
                lower[-a] = table[omega][power(table, lower[a], 14)]
            phases = [1]*n
            for a in range(1, n):
                if a % 3:
                    phases[a] = lower[a % g]
            for a in range(3, (n+1)//2, 3):
                phases[a] = rng.randrange(1, 16)
                phases[-a] = table[omega][power(table, phases[a], 14)]
            for first in bottom_values:
                phases[g], phases[-g] = first, power(table, first, 4)
                assert all(table[phases[a]][phases[-a]] == omega
                           for a in range(1, n))
                assert all(phases[(a+g) % n] == phases[a]
                           for a in range(1, n) if a % 3)
                pair = phases[g] ^ phases[-g]
                expected = table[omega][power(table, pair, 2)] ^ c
                assert expected in [1, omega, c]
                residuals.add(expected)
                units = [a for a in range(1, n) if a % 3]
                if n > 81:
                    units = rng.sample(units, 12)
                for h in units:
                    assert quadratic(table, phases, g, h) == expected
                    checks += 1
        assert residuals == {1, omega, c}
        print(f'n={n}: {checks} off-solution unit-period identities passed; '
              'all three possible residual values are nonzero', flush=True)


def check_saved_degrees():
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    for n, branches in [(3, 1), (9, 2), (27, 3)]:
        degrees = []
        for j in range(branches):
            data = json.loads((directory / f'hi_finite_field_{n}_char2_{j}.json').read_text())
            assert data[:2] == [n, 2]
            encode = lambda v: sum(a << i for i, a in enumerate(v))
            degree, modulus = len(data[2])-1, encode(data[2])

            def multiply(a, b):
                result = 0
                while b:
                    if b & 1:
                        result ^= a
                    b >>= 1
                    a <<= 1
                    if a >> degree:
                        a ^= modulus
                return result

            first = encode(data[4][2])
            current, orbit = first, []
            while current not in orbit:
                orbit.append(current)
                square = multiply(current, current)
                current = multiply(square, square)
            assert current == first and len(orbit) == 2*n//3
            assert degree == 2*len(orbit)
            degrees.append(len(orbit))
        print(f'n={n}: saved R_2 degrees over F4 are {degrees}; '
              'each generates its entire saved coefficient field', flush=True)


CUBIC_GP = r'''
check_cubics(s)={
  my(q=4^s, base=ffgen(ffinit(2,4*s,'z)), primitive=ffprimroot(base),
     omega=primitive^((q^2-1)/3), c=omega^2,
     unit=primitive^((q^2-1)/(q+1)), number=if(s==1,q+1,3), count,P,T,Y,
     extension,root,om,YL,x0,zeta,normalized_trace,rootchecks=0);
  for(j=0,number-1,
    Y=c*unit^j;count=0;
    if(Y*Y^q!=omega,error("wrong normalized norm coset"));
    for(a=0,q^2-1,
      T=sum(b=0,4*s-1,bittest(a,b)*base^b);
      P=x^3+T*x^2+Y*T^q*x+omega*Y;
      if(polisirreducible(P),
        count++;
        if(s==1||count==1,
          extension=ffextend(base,P,'w);root=extension[1];
          om=ffmap(extension[2],omega);YL=ffmap(extension[2],Y);
          if(root^(q^3+1)!=om,error("wrong root norm"));
          if(om^2*root^(1+q^2+q^4)!=YL,error("wrong normalized relative norm"));
          if(root^(q^2)==root,error("root remained in the base field"));
          x0=om^2*(om*YL)^((q+2)/3);zeta=root/x0;
          if(zeta^(q^2-q+1)!=1||zeta==1,error("wrong norm-fiber parameter"));
          normalized_trace=ffmap(extension[2],T)/x0;
          if(normalized_trace!=zeta+zeta^(q^2)+zeta^(q^4),error("wrong cubic period"));
          rootchecks++
        )
      )
    );
    if(count!=q*(q-1)/3,error("wrong irreducible cubic count"));
    print("q=",q," normalized-norm exponent=",j,
          ": irreducible trace choices=",count," of ",q^2);
  );
  print("q=",q,": ",rootchecks," explicit cubic extensions passed both norm checks");
};
iferr(check_cubics(1);check_cubics(3),e,print(e);quit(1));
print("ALL CUBIC COUNTS PASSED");quit;
'''


def check_cubic_counts():
    result = subprocess.run(['gp', '-q', '-f'], input=CUBIC_GP, text=True,
                            capture_output=True, check=True)
    if 'ALL CUBIC COUNTS PASSED' not in result.stdout or '***' in result.stderr:
        raise ArithmeticError(result.stdout + result.stderr)
    print(result.stdout, end='', flush=True)


if __name__ == '__main__':
    check_unit_period_identity()
    check_saved_degrees()
    check_cubic_counts()
    print('ALL EXACT FIELD-TOWER CHECKS PASSED; additive existence remains unresolved.')
