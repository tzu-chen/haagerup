"""Exact necessary gamma0 A1_k x A1_l ground-representation constraints.

Standard library only; no numerical job is authorized by this source.
ROOT must execute under the coordinated128MiB launcher. Affine-energy
filtering explicitly assumes unitary physical modules/nonnegative coset L0.
All Frobenius--Schur parity restrictions are omitted, keeping a safe superset.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


GROUND = (('c1',3,F(1,3),9),('d1',7,F(6,13),1),('d4',5,F(5,13),3))
MAX_LEVEL_SUM = 40


def index(n):
    if not isinstance(n,int) or not 1 <= n <= 7:
        raise ValueError('Finite SU2 dimensions must lie1..7')
    return n*(n*n-1)//6


def irreps(dimension):
    return [(n,m) for n in range(1,dimension+1)
            for m in range(1,dimension+1) if n*m <= dimension]


def decompositions(dimension):
    """All unordered finite SU2xSU2 sums, including arbitrary singlets."""
    types = irreps(dimension)
    answer = []
    def visit(i, remaining, terms, tleft, tright):
        if remaining == 0:
            answer.append({'terms':tuple(terms),'indices':(tleft,tright)})
            return
        if i == len(types):
            return
        n,m = types[i]
        size = n*m
        for count in range(remaining//size+1):
            tail = terms+[(n,m,count)] if count else terms
            visit(i+1,remaining-count*size,tail,
                  tleft+count*m*index(n),tright+count*n*index(m))
    visit(0,dimension,[],0,0)
    if len(answer) > 10000:
        raise RuntimeError('Unexpected decomposition count exceeds reviewed domain')
    return answer


def allowed(row,k,l,height,energy_filter):
    for n,m,count in row['terms']:
        if n > k+1 or m > l+1:
            return False
        if energy_filter and F(n*n-1,4*(k+2))+F(m*m-1,4*(l+2)) > height:
            return False
    return True


def describe(row,k,l,height):
    terms = [{'left_dimension':n,'right_dimension':m,'multiplicity':count,
        'affine_ground_weight':F(n*n-1,4*(k+2))+F(m*m-1,4*(l+2)),
        'available_coset_ground_weight':height-F(n*n-1,4*(k+2))-F(m*m-1,4*(l+2))}
        for n,m,count in row['terms']]
    return {'irreducible_summands':terms,
        'dimension':sum(n*m*count for n,m,count in row['terms']),
        'left_Dynkin_index':row['indices'][0],
        'right_Dynkin_index':row['indices'][1]}


def enumerate_levels(energy_filter=True):
    decomposed = {d:decompositions(d) for _,d,_,_ in GROUND}
    # An arbitrary reducible d-dimensional representation cannot exceed the
    # full d-dimensional SU2 index, even after summing both commuting factors.
    for d,rows in decomposed.items():
        if any(sum(row['indices']) > index(d) for row in rows):
            raise AssertionError('Finite-only total-index level bound failed')
    finite_bound = F(8+9*index(3)+index(7)+3*index(5),4)
    if finite_bound != MAX_LEVEL_SUM:
        raise AssertionError('Exact finite-only level-sum bound disagrees')
    # Each triple of decompositions determines k,l uniquely through the two
    # trace equations, so this is also a global bound across every level pair.
    witness_limit = 1
    for rows in decomposed.values():
        witness_limit *= len(rows)
    if witness_limit > 4420:
        raise RuntimeError('Unexpected decomposition product exceeds4420')
    levels = []
    witness_count = 0
    considered = 0
    for k in range(1,MAX_LEVEL_SUM//2+1):
        for l in range(k,MAX_LEVEL_SUM-k+1):
            considered += 1
            permitted = {name:[row for row in decomposed[d]
                if allowed(row,k,l,h,energy_filter)] for name,d,h,_ in GROUND}
            by_seven = {}
            for row in permitted['d1']:
                by_seven.setdefault(row['indices'],[]).append(row)
            witnesses = []
            for three in permitted['c1']:
                for five in permitted['d4']:
                    target = tuple(4*level-4-9*t3-3*t5 for level,t3,t5
                        in zip((k,l),three['indices'],five['indices']))
                    for seven in by_seven.get(target,[]):
                        raw = {'c1':three,'d1':seven,'d4':five}
                        actual = tuple(4+sum(coef*raw[name]['indices'][side]
                            for name,_,_,coef in GROUND) for side in (0,1))
                        if actual != (4*k,4*l):
                            raise AssertionError('Independent witness trace substitution failed')
                        witness = {name:describe(raw[name],k,l,h) for name,_,h,_ in GROUND}
                        if any(witness[name]['dimension'] != d for name,d,_,_ in GROUND):
                            raise AssertionError('Witness dimension substitution failed')
                        witnesses.append(witness)
            if witnesses:
                witness_count += len(witnesses)
                if witness_count > witness_limit:
                    raise RuntimeError('Unexpected witness output exceeds reviewed bound')
                levels.append({'levels':[k,l], 'level_sum':k+l,
                    'affine_central_charge':F(3*k,k+2)+F(3*l,l+2),
                    'residual_central_charge':F(2)+F(6,k+2)+F(6,l+2),
                    'witness_count':len(witnesses),'witnesses':witnesses})
    lower = min((row['residual_central_charge'] for row in levels),default=None)
    minimizers = [row['levels'] for row in levels if row['residual_central_charge'] == lower]
    return {'affine_energy_filter_applied':energy_filter,
        'decomposition_counts':{str(d):len(rows) for d,rows in decomposed.items()},
        'unordered_level_pairs_considered':considered,
        'finite_only_level_sum_upper_bound':finite_bound,
        'finite_only_Jensen_residual_lower_bound':F(28,11),
        'feasible_level_pair_count':len(levels),'total_representation_witness_count':witness_count,
        'residual_lower_bound_with_these_filters':lower,
        'residual_minimizing_level_pairs':minimizers,'feasible_levels':levels,
        'scope':'Necessary joint finite-ground constraints only. Every permitted decomposition witness is retained. No parity, fusion, branching or higher-character consistency is imposed; surviving witnesses do not construct a VOA.'}


def selftest():
    expected = {1:0,2:1,3:4,4:10,5:20,6:35,7:56}
    if any(index(n) != value for n,value in expected.items()):
        raise AssertionError('SU2 Dynkin index convention failed')
    rows = decompositions(3)
    signatures = {row['terms'] for row in rows}
    wanted = {((1,1,3),),((1,1,1),(1,2,1)),((1,1,1),(2,1,1)),
              ((1,3,1),),((3,1,1),)}
    if signatures != wanted:
        raise AssertionError('Complete dimension3 list failed')
    for d in (3,5,7):
        rows = decompositions(d)
        if len(rows) != {3:5,5:17,7:52}[d]:
            raise AssertionError('Colored-partition decomposition count failed')
        for row in rows:
            if sum(n*m*count for n,m,count in row['terms']) != d:
                raise AssertionError('Decomposition dimension failed')
        if len({row['terms'] for row in rows}) != len(rows):
            raise AssertionError('Duplicate decomposition generated')
        lookup = {(tuple(sorted(row['terms'])),row['indices']) for row in rows}
        for row in rows:
            flipped = tuple(sorted((m,n,count) for n,m,count in row['terms']))
            if (flipped,row['indices'][::-1]) not in lookup:
                raise AssertionError('Left/right enumeration symmetry failed')
    example = {'terms':((3,1,1),),'indices':(4,0)}
    if allowed(example,1,4,F(1,3),False):
        raise AssertionError('Nonintegrable affine highest weight accepted')
    if not allowed(example,4,1,F(1,3),True) or allowed(example,3,1,F(1,3),True):
        raise AssertionError('Exact affine-energy boundary test failed')
    # Check the tensor-product index directly from integer SU2 weight lists.
    for n,m in irreps(7):
        wl = range(1-n,n,2)
        wr = range(1-m,m,2)
        if F(m*sum(x*x for x in wl),2) != m*index(n) or F(n*sum(x*x for x in wr),2) != n*index(m):
            raise AssertionError('Independent Cartan-weight trace normalization failed')
    return {'indices_and_Cartan_weight_sums_checked':True,
        'complete_dimension3_and_flip_symmetry_checked':True,
        'integrability_and_exact_energy_boundary_checked':True}


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {key:encode(item) for key,item in value.items()}
    if isinstance(value,(tuple,list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--finite-only',action='store_true',
        help='Omit affine-energy filtering; integrable-level restrictions remain')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap == resource.RLIM_INFINITY or cap > 128*1024**2:
        raise RuntimeError('Use ROOT coordinated launcher with at most128MiB AS')
    output = args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists():
        raise ValueError('Choose a new .json output')
    source = Path(__file__).resolve()
    payload = source.read_bytes()
    source_hash = hashlib.sha256(payload).hexdigest()
    started = monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Thirty-second exact enumeration limit')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,30)
    try:
        result = enumerate_levels(not args.finite_only)
        result.update(selftest=selftest(),source_sha256=source_hash,
            ground_data=[{'module':name,'dimension':d,'weight':h,'trace_coefficient':coef}
                for name,d,h,coef in GROUND],
            trace_identity_each_factor='4+9*t(c1)+t(d1)+3*t(d4)=4*level',
            energy_premise=('No nonvacuum affine-energy inequality used.' if args.finite_only else
                'Each relevant nonvacuum physical module is unitary, or separately has nonnegative affine-commutant L0. This is NOT inferred merely from unitarity of the VOA.'),
            parity_scope='All Frobenius-Schur parity restrictions omitted; the enumerated set is a safe superset.',
            seconds=monotonic()-started,
            peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if source.read_bytes() != payload:
            raise RuntimeError('Source changed during enumeration')
        with pending.open('x') as stream:
            json.dump(encode(result),stream,indent=2,allow_nan=False)
            stream.write('\n')
        if source.read_bytes() != payload or output.exists():
            raise RuntimeError('Source/output changed before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps(encode({'output':str(output),'seconds':result['seconds'],
        'feasible_level_pairs':[row['levels'] for row in result['feasible_levels']],
        'residual_lower_bound':result['residual_lower_bound_with_these_filters']})),flush=True)


if __name__ == '__main__':
    main()
