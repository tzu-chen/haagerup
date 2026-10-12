"""Independent small lattice and stress checks for a human reviewer.

Only the Python standard library is used. No research mode engine is imported.
The formulas are printed in the input guide. Run through hi_cft_safe_run.py
with 512 MiB AS; estimated peak <0.12 GiB, one job, no workers.
This is a bounded low-grade checker, not a general lattice-VOA implementation.
"""
import argparse
import csv
from fractions import Fraction as Q
import hashlib
from itertools import permutations
import json
from pathlib import Path


class K(tuple):
    """a+b*s+c*t+d*s*t, s^2=13, t^2=-3, with exact rational entries."""
    def __new__(cls, value=0):
        if isinstance(value, (tuple, list)):
            if len(value) != 4:
                raise ValueError('a field element has four coefficients')
            return tuple.__new__(cls, map(Q, value))
        return tuple.__new__(cls, (Q(value), Q(0), Q(0), Q(0)))

    def __bool__(self):
        return any(value != 0 for value in self)

    def __add__(self, other):
        return K([x+y for x, y in zip(self, K(other))])
    __radd__ = __add__

    def __neg__(self):
        return K([-x for x in self])

    def __sub__(self, other):
        return self + (-K(other))

    def __mul__(self, other):
        a, b, c, d = self
        e, f, g, h = K(other)
        return K([a*e+13*b*f-3*c*g-39*d*h,
                  a*f+b*e-3*c*h-3*d*g,
                  a*g+c*e+13*b*h+13*d*f,
                  a*h+d*e+b*g+c*f])
    __rmul__ = __mul__

    def __truediv__(self, rational):
        return K([x/Q(rational) for x in self])

    def conjugate(self):
        a, b, c, d = self
        return K([a, b, -c, -d])


Z = (0,)*8
EDGES = [(0,1),(1,2),(2,3),(3,4),(2,5),(6,7)]
G = [[2*int(i == j) for j in range(8)] for i in range(8)]
for i, j in EDGES:
    G[i][j] = G[j][i] = -1
SIMPLE = [tuple(int(i == j) for j in range(8)) for i in range(8)]
LEFT = (-1,-2,-3,-2,-1,-2,0,0)
RIGHT = (5,8,9,8,5,0,2,2)
GAUGE = (5,8,9,8,5,1,2,2)
MOMENTA = [(0,0,0,0,0,-1,1,1), (0,0,0,1,1,-1,0,0),
           (1,1,0,0,0,-1,0,0)]
U_COEFF = [K(1), K([0,'1/20','3/20',0]), K([0,'1/20','-3/20',0])]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def dot(a, b):
    return sum(a[i]*G[i][j]*b[j] for i in range(8) for j in range(8))


def eps(a, b):
    exponent = sum(a[i]*b[i] for i in range(8))
    exponent += sum(a[i]*b[j]*G[i][j] for i in range(8) for j in range(i))
    return 1 if exponent % 2 == 0 else -1


def put(result, state, coefficient):
    value = result.get(state, K()) + coefficient
    if value:
        result[state] = value
    else:
        result.pop(state, None)


def linear(*terms):
    result = {}
    for coefficient, vector in terms:
        for state, value in vector.items():
            put(result, state, K(coefficient)*value)
    return result


def h(vector):
    return {(Z,(i,)):K(value) for i, value in enumerate(vector) if value}


def exponential(momentum, coefficient=1):
    return {(tuple(momentum),()):K(coefficient)}


def expansion(alpha, degree):
    """Coefficients of exp(sum alpha(-n) z^n/n), only degrees 0,1,2."""
    if degree < 0:
        return []
    require(degree <= 2, 'outside the reviewed grade-two truncation')
    if degree == 0:
        return [((),Q(1))]
    if degree == 1:
        return [((i,),Q(a)) for i, a in enumerate(alpha) if a]
    terms = [((8+i,),Q(a,2)) for i, a in enumerate(alpha) if a]
    # The ordered sum deliberately combines off-diagonal terms in put().
    terms += [(tuple(sorted((i,j))),Q(a*b,2))
              for i,a in enumerate(alpha) for j,b in enumerate(alpha) if a*b]
    return terms


def current_product(a, n, b):
    """Only current-current singular products and equal-type normal products."""
    require(n in (-1,0,1), 'unsupported current product')
    result = {}
    for (alpha, oa), ca in a.items():
        for (beta, ob), cb in b.items():
            if not oa and not ob:
                total = tuple(x+y for x,y in zip(alpha,beta))
                for oscillators, coefficient in expansion(alpha, -n-1-dot(alpha,beta)):
                    put(result, (total,oscillators), ca*cb*eps(alpha,beta)*coefficient)
            elif oa and ob:
                require(alpha == beta == Z and len(oa) == len(ob) == 1,
                        'expected Heisenberg currents')
                i, j = oa[0], ob[0]
                if n == 1:
                    put(result, (Z,()), ca*cb*G[i][j])
                elif n == -1:
                    put(result, (Z,tuple(sorted((i,j)))), ca*cb)
            else:
                require(n >= 0, 'mixed normal current product is not implemented')
                if n == 0:
                    if oa:
                        put(result, (beta,()), ca*cb*dot(SIMPLE[oa[0]],beta))
                    else:
                        put(result, (alpha,()), -ca*cb*dot(alpha,SIMPLE[ob[0]]))
    return result


def inverse(matrix):
    n = len(matrix)
    rows = [[Q(x) for x in row]+[Q(i == j) for j in range(n)]
            for i,row in enumerate(matrix)]
    for col in range(n):
        pivot = next(i for i in range(col,n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        rows[col] = [x/rows[col][col] for x in rows[col]]
        for i in range(n):
            if i != col:
                factor = rows[i][col]
                rows[i] = [x-factor*y for x,y in zip(rows[i],rows[col])]
    return [row[n:] for row in rows]


def ambient_stress():
    result = {}
    gi = inverse(G)
    for i in range(8):
        for j in range(8):
            put(result, (Z,tuple(sorted((i,j)))), K(gi[i][j]/2))
    return result


def sugawara(triple, level):
    H, E, F = triple
    return linear((Q(1,4*(level+2)),current_product(H,-1,H)),
                  (Q(1,2*(level+2)),current_product(E,-1,F)),
                  (Q(1,2*(level+2)),current_product(F,-1,E)))


def gauge(alpha):
    value = Q(1)
    for base, exponent in zip(GAUGE,alpha):
        value *= Q(base)**exponent
    return value


def oscillator_pairing(a, b):
    if len(a) != len(b):
        return Q(0)
    result = 0
    for ordered_b in permutations(b):
        term = 1
        for i,j in zip(a,ordered_b):
            if i//8 != j//8:
                term = 0
                break
            term *= (1+i//8)*G[i%8][j%8]
        result += term
    return Q(result)


def inner(a, b):
    result = K()
    by_momentum = {}
    for (beta,ob), cb in b.items():
        by_momentum.setdefault(beta,[]).append((ob,cb))
    for (alpha,oa), ca in a.items():
        for ob,cb in by_momentum.get(alpha,[]):
            result += ca.conjugate()*cb*gauge(alpha)*oscillator_pairing(oa,ob)
    return result


def read_field(rows, recognized=False, grade=2):
    result = {}
    require(len(rows) <= 2000, 'too many field terms')
    for row in rows:
        alpha, osc = tuple(row['momentum']), tuple(row['oscillators'])
        require(len(alpha) == 8 and all(type(x) is int and abs(x) <= 20 for x in alpha),
                'invalid momentum')
        require(grade in (2,3) and osc == tuple(sorted(osc)) and len(osc) <= grade and
                all(type(i) is int and 0 <= i < 8*grade for i in osc), 'invalid low-grade oscillators')
        require(dot(alpha,alpha)+2*sum(1+i//8 for i in osc) == 2*grade, 'incorrect field grade')
        coeffs = row['Qsqrt13_sqrtminus3'] if recognized else row['coefficient']
        if recognized:
            coeffs = coeffs[0]+coeffs[1]
        value = K(coeffs)
        require(all(x.numerator.bit_length() < 4096 and x.denominator.bit_length() < 4096
                    for x in value), 'coefficient exceeds reviewed bound')
        require((alpha,osc) not in result, 'duplicate field monomial')
        if value:
            result[alpha,osc] = value
    return result


def rational(value):
    require(value[1:] == (0,0,0), 'expected rational answer')
    return value[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    sources = {}
    def read(name):
        path = args.sources/name
        require(path.stat().st_size < 1024**2, 'source exceeds 1 MiB cap')
        raw = path.read_bytes()
        sources[name] = hashlib.sha256(raw).hexdigest()
        return json.loads(raw)
    fields = read('hi_cft_20260923_c8_exact_fields.json')
    potts = read('hi_cft_20260923_proof_potts_exact.json')
    pf13 = read('hi_cft_20260923_proof_pf13_exact.json')
    L = [h(LEFT),exponential(LEFT),exponential(tuple(-x for x in LEFT),-1)]
    R = [h(RIGHT),linear(*[(1,exponential(SIMPLE[i])) for i,c in enumerate(RIGHT) if c]),
         linear(*[(-c,exponential(tuple(-x for x in SIMPLE[i]))) for i,c in enumerate(RIGHT) if c])]
    vac = exponential(Z)
    expected_brackets = {(0,1):(1,2),(1,0):(1,-2),(0,2):(2,-2),
                         (2,0):(2,2),(1,2):(0,1),(2,1):(0,-1)}
    bracket_checks = 0
    for axis,level in [(L,1),(R,39)]:
        for i in range(3):
            for j in range(3):
                term = expected_brackets.get((i,j))
                expected = {} if term is None else linear((term[1],axis[term[0]]))
                require(current_product(axis[i],0,axis[j]) == expected, 'affine simple pole')
                scale = 2*level if i == j == 0 else level if {i,j} == {1,2} else 0
                require(current_product(axis[i],1,axis[j]) == linear((scale,vac)), 'affine double pole')
                bracket_checks += 2
    for a in L:
        for b in R:
            for n in [0,1]:
                require(not current_product(a,n,b) and not current_product(b,n,a), 'mixed current product')
                bracket_checks += 2
    u = linear(*[(c,exponential(alpha)) for c,alpha in zip(U_COEFF,MOMENTA)])
    require(u == read_field(fields['fields'][-2]['coefficients'],True), 'three-term u differs from saved field')
    momentum_rows = []
    for alpha,coefficient in zip(MOMENTA,U_COEFF):
        require((dot(alpha,alpha),dot(LEFT,alpha),dot(RIGHT,alpha)) == (4,1,13), 'u norm/charge')
        require(dot(LEFT,alpha) >= 0, 'left highest condition')
        # Every summand is killed separately. No cancellation is inferred.
        require(all(dot(SIMPLE[i],alpha) >= 0 for i,c in enumerate(RIGHT) if c), 'right highest condition')
        require(abs(dot(LEFT,alpha)) <= 1 and
                all(abs(dot(SIMPLE[i],alpha)) <= 1 for i,c in enumerate(RIGHT) if c), 'positive root-current modes')
        momentum_rows.append({'momentum':alpha,'norm_squared':4,'left_charge':1,'right_charge':13,
                              'gauge_norm':str(gauge(alpha)),
                              'coefficient_norm':str(rational(coefficient.conjugate()*coefficient))})
    require(inner(u,u) == K(12), 'u gauge norm')
    omega = ambient_stress()
    omegaL,omegaR = sugawara(L,1),sugawara(R,39)
    e = read_field(fields['fields'][-1]['coefficients'],True)
    f = linear((1,omega),(-1,omegaL),(-1,omegaR),(-1,e))
    p,z = read_field(potts['potts_stress']),read_field(pf13['stress'])
    # Independently expand both short Potts formulas from the reader guide.
    alpha,beta = (0,0,0,1,1,0,-1,-1),(1,1,0,-1,-1,0,0,0)
    gamma = tuple(x+y for x,y in zip(alpha,beta))
    require((dot(alpha,alpha),dot(beta,beta),dot(alpha,beta)) == (4,4,-2), 'Potts plane')
    root_coefficients = [K([0,'-1/100','-3/100',0]), K([0,'-1/10','3/10',0]),
                         K(['7/100',0,0,'3/100']), K(['7/100',0,0,'-3/100']),
                         K([0,'-1/100','3/100',0]), K([0,'-1/10','-3/10',0])]
    roots = [alpha,tuple(-x for x in alpha),beta,tuple(-x for x in beta),
             gamma,tuple(-x for x in gamma)]
    pc = linear((Q(1,15),current_product(h(alpha),-1,h(alpha))),
                (Q(1,15),current_product(h(beta),-1,h(beta))),
                (Q(1,15),current_product(h(alpha),-1,h(beta))),
                *[(c,exponential(a)) for a,c in zip(roots,root_coefficients)])
    require(pc == p, 'complete compact Potts stress formula')
    A = tuple(x-y for x,y in zip(alpha,beta))
    C = tuple(x+2*y for x,y in zip(alpha,beta))
    E = tuple(-2*x-y for x,y in zip(alpha,beta))
    wp = {}
    for i,a in enumerate(A):
        for j,b in enumerate(C):
            for k,c in enumerate(E):
                put(wp,(Z,tuple(sorted((i,j,k)))),K(a*b*c))
    for cartan,indices in [(A,[4,5]),(C,[0,1]),(E,[2,3])]:
        for index in indices:
            for i,value in enumerate(cartan):
                put(wp,(roots[index],(i,)), -45*value*root_coefficients[index])
    require(wp == read_field(potts['weight_three_primary'],grade=3), 'complete compact Potts primary formula')
    axes = [omegaL,omegaR,e,f]
    norms = list(map(Q,['1/2','117/82','1200/1271','35/31']))
    for i,a in enumerate(axes):
        for j,b in enumerate(axes):
            require(inner(a,b) == K(norms[i] if i == j else 0), 'stress Gram matrix')
    require(inner(omega,omega) == K(4), 'ambient central charge norm')
    require(inner(p,p) == K(Q(2,5)) and inner(z,z) == K(Q(4,5)), 'factor stress norms')
    expected = [list(map(Q,['0','13/205','108/1271','39/155'])),
                list(map(Q,['0','21/205','780/1271','13/155']))]
    overlaps = [[rational(inner(a,v)) for a in axes] for v in [p,z]]
    require(overlaps == expected, 'factor stress overlaps')
    projections = [[value/norm for value,norm in zip(row,norms)] for row in overlaps]
    avp,avz = [linear(*zip(row,axes)) for row in projections]
    positive = linear((1,omegaL),(Q(3403,4563),omegaR),(Q(25,6),avp),(Q(25,26),avz))
    require(positive == omega, 'positive identity as an exact vector')
    primary_rows = []
    fweights = ['38/31','42/31','10/31','20/31','49/31','3/31','24/31','13/31']
    for row,hf in zip(fields['fields'][:-1],fweights):
        n,m = row['dimensions']
        he = Q(row['e_weight'])
        require(Q(n*n-1,12)+Q(m*m-1,164)+he+Q(hf) == 2, 'primary total energy')
        primary_rows.append({'dimensions':[n,m],'e_weight':str(he),'f_weight':hf})
    require(len(primary_rows) == 8 and sum(n*m for n,m in [r['dimensions'] for r in primary_rows]) == 96,
            'primary dimension sum')
    result = {'status':'pass','arithmetic':'stdlib fractions.Fraction; no research engine imports',
              'current_products_checked':bracket_checks, 'gram_matrix':G,
              'u_momentum_rows':momentum_rows,'u_norm_squared':'12',
              'stress_axis_order':['omegaL','omegaR','e','f'],'stress_norms':list(map(str,norms)),
              'factor_order':['p','z'],'stress_overlaps':[[str(x) for x in row] for row in overlaps],
              'stress_projections':[[str(x) for x in row] for row in projections],
              'positive_identity_full_vector':True, 'primary_energy_rows':primary_rows,
              'compact_Potts_formulas_match_saved_fields':True,
              'source_sha256':sources,
              'scope':'Full current singular products, u highest/primary conditions, compact Potts field formulas, grade-two Fock pairings and projected stress identity only. '
              'No Virasoro OPE, membership, invariant-space exhaustion, rationality, higher gate or category theorem is inferred.'}
    with (args.output_dir/'readable_checks.json').open('w') as stream:
        json.dump(result,stream,indent=2)
        stream.write('\n')
    with (args.output_dir/'grade2_fields.tsv').open('w',newline='') as stream:
        writer = csv.writer(stream,delimiter='\t')
        writer.writerow(['field','momentum','oscillators','q0','qs','qt','qst'])
        for name,vector in zip(['u','omega','omegaL','omegaR','e','f','p','z'],[u,omega,*axes,p,z]):
            for (alpha,osc),coefficient in sorted(vector.items()):
                writer.writerow([name,','.join(map(str,alpha)),','.join(map(str,osc)),*map(str,coefficient)])
    print(json.dumps({'status':'pass','current_products_checked':bracket_checks,
                      'stress_overlaps':result['stress_overlaps'],
                      'positive_identity_full_vector':True,
                      'exported_field_terms':sum(len(v) for v in [u,omega,*axes,p,z])}))


if __name__ == '__main__':
    main()
