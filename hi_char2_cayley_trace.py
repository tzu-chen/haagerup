"""Generate exact tests of field-trace pullback of Cayley phase functions.

For odd extension degree s, composing V with Tr(F_(q^s)/F_q)
preserves V(x+1)=V(x)+1 and V(x^2)=V(x)^4. Whether the additive
HI equations survive is checked separately, with no such assumption.
"""

import argparse
import json
from pathlib import Path


MAGMA = r'''
SetQuitOnError(true);
procedure Probe(r,s,modulus,delta_bits,generator_bits,points)
 assert IsOdd(r) and IsOdd(s);
 q := 2^r; n0 := q+1; n := q^s+1;
 E0<g> := GF(2,4*r); E<z> := GF(2,4*r*s); Embed(E0,E);
 Encode := func<x | &+[(Integers()!Eltseq(x)[i])*2^(i-1) : i in [1..4*r]]>;
 Decode := func<b | &+[(E0!((b div 2^j) mod 2))*g^j : j in [0..4*r-1]]>;
 assert &+[(Integers()!Coefficient(DefiningPolynomial(E0),j))*2^j : j in [0..4*r]] eq modulus;
 delta := Decode(delta_bits); gen0 := Decode(generator_bits);
 zeta0 := gen0^((#E0-1) div n0);
 index := AssociativeArray();
 for a in [1..n0-1] do index[E!(delta+1/(1+zeta0^a))] := a; end for;
 assert #Keys(index) eq q;
 zeta := PrimitiveElement(E)^((#E-1) div n);
 labels := [0]; power := E!1;
 for a in [1..n-1] do
  power *:= zeta;
  x := (E!delta)+1/(1+power);
  assert x^(q^s) eq x;
  y := &+[x^(q^j) : j in [0..s-1]];
  assert IsDefined(index,y);
  Append(~labels,index[y]);
 end for;
 for a in [1..n-1] do
  assert labels[n-a+1] eq n0-labels[a+1];
  assert labels[(2*a) mod n+1] eq (2*labels[a+1]) mod n0;
 end for;
 for b in [1..n0-1] do assert #[a : a in labels | a eq b] eq q^(s-1); end for;
 first := 0;
 for p in [1..#points] do
  W0 := [Decode(b) : b in points[p]];
  assert #W0 eq n0 and W0[1] eq 1;
  W := [W0[a+1] : a in labels];
  for a in [1..n-1] do
   assert W[a+1]*W[n-a+1] eq delta;
   assert W[a+1]^4 eq W[(2*a) mod n+1];
  end for;
  if s gt 1 then assert &+W eq 1; end if;
  residual := &+[W[m+1]^2*W[(1-m) mod n+1]*W[(-1-m) mod n+1] : m in [0..n-1]];
  if residual eq 0 then first +:= 1; end if;
  print "TRACE-PULLBACK POINT source",n0,"target",n,"index",p,
        "first-Q residual bits",Encode(residual);
 end for;
 print "COMPLETE TRACE-PULLBACK source",n0,"target",n,"candidates",#points,"first Q",first;
end procedure;
__CALLS__
quit;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path('/tmp/hi_char2_cayley_trace.m'))
    parser.add_argument('--extensions', type=int, nargs='+', default=[3])
    parser.add_argument('--orders', type=int, nargs='+', default=[9,33])
    args = parser.parse_args()
    calls = []
    for n in args.orders:
        r = (n-1).bit_length()-1
        assert n == (1 << r)+1 and r % 2
        data = json.loads(Path(f'hi_char2_cayley_degree{r-1}_{n}.json').read_text())
        points = []
        for path in [Path(f'hi_char2_cayley_degree{r-1}_{n}_results.txt'),
                     Path(f'hi_char2_cayley_boundary{n}_results.txt')]:
            points.extend(json.loads(line[7:])['W'] for line in path.read_text().splitlines()
                          if line.startswith('FULL_Q '))
        for s in args.extensions:
            calls.append(f'Probe({r},{s},{data["modulus"]},{data["delta"]},'
                         f'{data["generator"]},{json.dumps(points)});')
    args.source.write_text(MAGMA.replace('__CALLS__','\n'.join(calls)))


if __name__ == '__main__':
    main()
