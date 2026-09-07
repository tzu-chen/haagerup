"""Generate and export Cayley function spaces of bounded algebraic degree.

Magma solves only binary linear constraints on functions. The separate C++
search then checks the remaining HI quadratics; none is assumed here.
"""

import argparse
import json
from pathlib import Path
import re

from hi_char2_general_search import quadratic_representatives


MAGMA = r'''
SetQuitOnError(true);
procedure Export(r, maxdegree)
 assert IsOdd(r);
 q := 2^r; n := q+1;
 E<g> := GF(2,4*r); primitive := PrimitiveElement(E);
 delta := primitive^((#E-1) div 3);
 zeta := primitive^((#E-1) div n);
 P<T> := PolynomialRing(E); eta := Roots(T^4+T+1)[1][1];
 smallgen := primitive^((#E-1) div (q-1));
 halfgen := primitive^((#E-1) div (q^2-1));
 domain := [&+[(E!((mask div 2^j) mod 2))*smallgen^j : j in [0..r-1]]
            : mask in [0..q-1]];
 assert #SequenceToSet(domain) eq q;
 squares := [Index(domain,x^2) : x in domain];
 monomials := [mask : mask in [0..q-1] |
               &+[(mask div 2^i) mod 2 : i in [0..r-1]] le maxdegree];
 directions := [];
 for monomial in monomials, j in [0..2*r-1] do
  Append(~directions,[BitwiseAnd(mask,monomial) eq monomial select halfgen^j else E!0
                     : mask in [0..q-1]]);
 end for;
 equations := [];
 for f in directions do
  residuals := [f[BitwiseXor(mask,1)+1]+f[mask+1] : mask in [0..q-1]] cat
               [f[squares[mask+1]]+f[mask+1]^4 : mask in [0..q-1]];
  Append(~equations,&cat[[Integers()!b : b in Eltseq(x)] : x in residuals]);
 end for;
 equations := Matrix(GF(2),equations);
 rhsvalues := [E!1 : mask in [0..q-1]] cat [E!0 : mask in [0..q-1]];
 rhs := Vector(GF(2),&cat[[Integers()!b : b in Eltseq(x)] : x in rhsvalues]);
 particular := Solution(equations,rhs);
 kernel := Basis(Nullspace(equations));
 values := func<row | [&+[(E!row[i])*directions[i][j] : i in [1..#directions]] : j in [1..q]]>;
 origin := values(particular);
 basis := [values(row) : row in kernel];
 assert forall{mask : mask in [0..q-1] | origin[BitwiseXor(mask,1)+1]+origin[mask+1] eq 1};
 assert forall{mask : mask in [0..q-1] | origin[squares[mask+1]] eq origin[mask+1]^4};
 for f in basis do
  assert forall{mask : mask in [0..q-1] | f[BitwiseXor(mask,1)+1] eq f[mask+1]};
  assert forall{mask : mask in [0..q-1] | f[squares[mask+1]] eq f[mask+1]^4};
 end for;
 Encode := func<x | &+[(Integers()!Eltseq(x)[i])*2^(i-1) : i in [1..4*r]]>;
 modulus := &+[(Integers()!Coefficient(DefiningPolynomial(E),i))*2^i : i in [0..4*r]];
 indices := [Index(domain,1/(1+zeta^a)+delta)-1 : a in [1..n-1]];
 assert Min(indices) ge 0 and #SequenceToSet(indices) eq n-1;
 half := [E!0] cat [halfgen^i : i in [0..q^2-2]];
 table := [[Encode(x),Encode(delta^2*(x+eta)/(x+eta+1))] : x in half];
 printf "BEGIN DATA n %o dimension %o\n",n,#basis;
 printf "{\"n\":%o,\"maxdegree\":%o,\"modulus\":%o,\"delta\":%o,\"generator\":%o,\"particular\":%o,\"basis\":%o,\"indices\":%o,\"table\":%o}\n",
        n,maxdegree,modulus,Encode(delta),Encode(primitive),[Encode(x) : x in origin],
        [[Encode(x) : x in f] : f in basis],indices,table;
 print "END DATA";
end procedure;
for r in [3,5] do Export(r,2); end for;
quit;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    generate = sub.add_parser('generate')
    generate.add_argument('source', type=Path)
    generate.add_argument('--r', nargs='+', type=int, default=[3, 5])
    generate.add_argument('--degree', type=int, default=2)
    prepare = sub.add_parser('prepare')
    prepare.add_argument('log', type=Path)
    prepare.add_argument('--directory', type=Path, default=Path('.'))
    args = parser.parse_args()
    if args.command == 'generate':
        calls = '\n'.join(f'Export({r},{args.degree});' for r in args.r)
        args.source.write_text(MAGMA.replace('for r in [3,5] do Export(r,2); end for;', calls))
        return
    matches = re.findall(r'BEGIN DATA n (\d+) dimension (\d+)\s*(\{.*?\})\s*END DATA',
                         args.log.read_text(), re.S)
    if not matches:
        raise ValueError('No complete exports; inspect Magma output')
    for order, dimension, encoded in matches:
        # Magma wraps long string tokens with a backslash and physical newline.
        data = json.loads(re.sub(r'\\\r?\n', '', encoded))
        data.setdefault('maxdegree', 2)  # The first degree-two exports predate this key.
        n, dim = int(order), int(dimension)
        assert data['n'] == n and len(data['basis']) == dim
        assert len(data['particular']) == n-1
        assert len(data['table']) == (n-1)**2
        pairs = quadratic_representatives(n)
        assert pairs[0] == (1, 1)
        prefix = args.directory/f'hi_char2_cayley_degree{data["maxdegree"]}_{n}'
        prefix.with_suffix('.json').write_text(json.dumps(data)+'\n')
        rows = [[n, data['modulus'], data['delta'], data['generator'], dim, len(pairs)],
                data['particular'], data['indices'], *data['basis'], *data['table'],
                *[list(pair) for pair in pairs]]
        prefix.with_suffix('.txt').write_text('\n'.join(' '.join(map(str, row)) for row in rows)+'\n')
        print(f'n={n}: binary dimension {dim}, {1 << dim} candidates, {len(pairs)} Q representatives.')


if __name__ == '__main__':
    main()
