"""Exact twelve-variable Haagerup c8 weight-two current-trace check.

Pure standard library. No tensor, basis enumeration or floating linear algebra.
Published data: Evans--Gannon arXiv:1006.1326, equations(1.24),(2.7).
The accompanying note derives the elliptic residue and current-neutrality tests.
Run only in ROOT's coordinated numerical slot, under128MiB address limit.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

N = 12
NAMES = ('0','b','a','c0','c1','c2','d1','d2','d3','d4','d5','d6')
LAMBDA = tuple(F(x) for x in ('2/3','2/3','2/3','2/3','0','1/3',
    '5/39','20/39','32/39','2/39','8/39','11/39'))
CHI = tuple(tuple(F(x) for x in row) for row in (
    (6,80,81,81,8748,1215,3549,273,13,5538,2275,1378),
    (80,6,81,81,8748,1215,-3549,-273,-13,-5538,-2275,-1378),
    (81,81,167,-81,-8748,-1215,0,0,0,0,0,0),
    (81,81,-81,167,-8748,-1215,0,0,0,0,0,0),
    (3,3,-3,-3,-12,18,0,0,0,0,0,0),
    (27,27,-27,-27,1458,-152,0,0,0,0,0,0),
    (7,-7,0,0,0,0,-88,-14,-1,50,63,64),
    (42,-42,0,0,0,0,-1484,92,16,2940,-192,-1041),
    (119,-119,0,0,0,0,-2142,987,11,-24990,-6035,4641),
    (5,-5,0,0,0,0,17,13,-3,-2,35,-14),
    (13,-13,0,0,0,0,174,-1,-5,294,-147,51),
    (14,-14,0,0,0,0,448,-77,7,-343,125,-24)))


def shift(A, scalar):
    return [[A[i][j]+(scalar if i == j else 0) for j in range(N)] for i in range(N)]


def matmul(A, B):
    return [[sum((A[i][k]*B[k][j] for k in range(N)), F(0))
             for j in range(N)] for i in range(N)]


def matvec(A, v):
    return [sum((a*b for a,b in zip(row,v)), F(0)) for row in A]


def B_at(J):
    return [[(J-240)*(LAMBDA[i]-1)*(i == j)
             +(1+LAMBDA[i]-LAMBDA[j])*CHI[i][j]
             for j in range(N)] for i in range(N)]


def solve(rows, rhs):
    """Exact RREF, a particular solution, and the complete homogeneous basis."""
    if len(rows) != len(rhs) or any(len(row) != N for row in rows):
        raise ValueError('Expected a bounded twelve-column system')
    A = [[F(x) for x in row]+[F(y)] for row,y in zip(rows,rhs)]
    pivots = []
    for col in range(N):
        selected = next((r for r in range(len(pivots),len(A)) if A[r][col]), None)
        if selected is None:
            continue
        r = len(pivots)
        A[r], A[selected] = A[selected], A[r]
        pivot = A[r][col]
        A[r] = [x/pivot for x in A[r]]
        for other in range(len(A)):
            if other != r and A[other][col]:
                scale = A[other][col]
                A[other] = [x-scale*y for x,y in zip(A[other],A[r])]
        pivots.append(col)
    inconsistent = any(not any(row[:N]) and row[N] for row in A)
    if inconsistent:
        return {'consistent': False, 'rank': len(pivots),
                'augmented_rank': len(pivots)+1, 'rref': A}
    free = [j for j in range(N) if j not in pivots]
    particular = [F(0)]*N
    for r,col in enumerate(pivots):
        particular[col] = A[r][N]
    basis = []
    for col in free:
        vector = [F(0)]*N
        vector[col] = F(1)
        for r,pivot in enumerate(pivots):
            vector[pivot] = -A[r][col]
        basis.append(vector)
    if matvec(rows, particular) != list(map(F,rhs)) or any(any(matvec(rows,v)) for v in basis):
        raise AssertionError('Independent substitution failed')
    return {'consistent': True, 'rank': len(pivots), 'dimension': len(free),
            'particular': particular, 'basis': basis, 'rref': A}


def unit_row(index):
    return [F(i == index) for i in range(N)]


def coefficient_base():
    # Coefficients at q^Lambda, NOT the separate polar coefficients.
    gamma0 = list(CHI[i][0] for i in range(N))
    delta = list(CHI[i][8] for i in range(N))
    answer = []
    for i in range(N):
        polar = F(i in (0,8))
        answer.append((gamma0[i]+delta[i])/12-2*polar
            +LAMBDA[i]*(gamma0[i]/4+F(13,28)*delta[i]))
    return answer


def certificate():
    Bi, Bw = B_at(984), B_at(-744)
    polynomial_i = matmul(Bi, shift(Bi,864))
    polynomial_w = matmul(Bw,matmul(shift(Bw,-576),shift(Bw,-1152)))
    if any(any(row) for row in polynomial_i+polynomial_w):
        raise AssertionError('Published-matrix elliptic residue polynomial failed')
    rows = shift(Bi,864)+matmul(shift(Bw,-576),shift(Bw,-1152))
    zero = [F(0)]*len(rows)
    space = solve(rows,zero)
    if not space['consistent'] or space['dimension'] != 3 or sum(LAMBDA) != 5:
        raise AssertionError('Weight-two dimension or exponent-sum control failed')
    base = coefficient_base()
    expected = {0:F(129,28),4:F(1,4),6:F(121,182),9:F(29,182)}
    if any(base[i] != value for i,value in expected.items()):
        raise AssertionError('Independent particular-trace coefficient control failed')
    neutral_indices = (4,6,9)
    nr = rows+[unit_row(i) for i in neutral_indices]
    ny = zero+[-base[i] for i in neutral_indices]
    neutral = solve(nr,ny)
    full = solve(nr+[unit_row(0)],ny+[F(8)-base[0]])
    predicted = None
    if neutral['consistent'] and all(v[0] == 0 for v in neutral['basis']):
        predicted = base[0]+neutral['particular'][0]
    leading = None
    if neutral['consistent'] and not neutral['basis']:
        leading = dict(zip(NAMES,[a+b for a,b in zip(base,neutral['particular'])]))
    return {'coefficient_convention': 'Normalized trace Q_u/kappa_u; leading nonpolar q^Lambda coefficient.',
        'basis_order': NAMES, 'Lambda': LAMBDA, 'characteristic_matrix_chi': CHI,
        'elliptic_polynomial_controls': {'Bi(Bi+864I)': True,
            'Bw(Bw-576I)(Bw-1152I)': True},
        'weight_two_space': space, 'particular_Q_leading_coefficients': dict(zip(NAMES,base)),
        'A3_neutral_ground_modules': [NAMES[i] for i in neutral_indices],
        'neutral_system': neutral, 'forced_vacuum_grade_one_trace': predicted,
        'required_A3_level_one_trace': F(8), 'full_A3_system': full,
        'unique_neutral_solution_leading_Q': leading,
        'scope': 'Exact rational coefficient test conditional on the stated gamma1 character, actual Haagerup modular representation, Jacobi transformation law, and the justified A3-neutral lowest spaces. Matrix consistency alone is not VOA existence.'}


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {key:encode(item) for key,item in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    limit = resource.getrlimit(resource.RLIMIT_AS)[0]
    if limit == resource.RLIM_INFINITY or limit > 128*1024**2:
        raise RuntimeError('Use the coordinated launcher with at most128MiB AS')
    output = args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists():
        raise ValueError('Use a new .json output')
    source = Path(__file__).resolve()
    payload = source.read_bytes()
    source_hash = hashlib.sha256(payload).hexdigest()
    started = monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Thirty-second exact algebra limit')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,30)
    try:
        result = certificate()
        result.update(source_sha256=source_hash,seconds=monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if source.read_bytes() != payload:
            raise RuntimeError('Source changed during certificate')
        with pending.open('x') as handle:
            json.dump(encode(result),handle,indent=2,allow_nan=False)
            handle.write('\n')
        if output.exists() or source.read_bytes() != payload:
            raise RuntimeError('Output/source changed before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps({'output':str(output),'seconds':result['seconds'],
        'neutral_consistent':result['neutral_system']['consistent'],
        'A3_consistent':result['full_A3_system']['consistent'],
        'forced_vacuum_grade_one_trace':encode(result['forced_vacuum_grade_one_trace'])},indent=2))


if __name__ == '__main__':
    main()
