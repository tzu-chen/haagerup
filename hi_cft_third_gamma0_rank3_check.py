"""Exact followup to the frozen universal current-trace certificate.

Pure stdlib; ROOT alone executes in the coordinated128MiB slot.
The rank-saturation representation premise is proved in the adjacent note.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


def solve(matrix, target):
    a = [list(map(F,row))+[F(value)] for row,value in zip(matrix,target)]
    n = len(a)
    if n != 3 or any(len(row) != n+1 for row in a):
        raise ValueError('Exactly three trace coordinates required')
    for j in range(n):
        pivot = next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None:
            raise AssertionError('Ground-neutrality chart is not unique')
        a[j],a[pivot] = a[pivot],a[j]
        scale = a[j][j]
        a[j] = [x/scale for x in a[j]]
        for i in range(n):
            if i != j:
                scale = a[i][j]
                a[i] = [x-scale*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]


def check(universal,trace):
    names = ['0','b','a','c0','c1','c2','d1','d2','d3','d4','d5','d6']
    if trace['basis_order'] != names:
        raise ValueError('Unexpected modular coordinates')
    if not universal['M2_functionals_annihilate_every_basis_vector']:
        raise ValueError('Prior modular functionals were not certified')
    constants = universal['identity_constants']['gamma0']
    if {key:F(value) for key,value in constants.items()} != {'minus':0,'plus':4,'third':2}:
        raise ValueError('Unexpected gamma0 identity constants')
    space = trace['weight_two_space']
    if not space['consistent'] or space['dimension'] != 3 or len(space['basis']) != 3:
        raise ValueError('The complete three-dimensional trace space is required')
    basis = [list(map(F,row)) for row in space['basis']]
    if any(len(row) != 12 for row in basis):
        raise ValueError('Unexpected homogeneous vector shape')
    base = [F(universal['gamma0_particular_coefficients'][name]) for name in names]
    chi = [[F(x) for x in row] for row in trace['characteristic_matrix_chi']]
    lam = list(map(F,trace['Lambda']))
    derived = [chi[i][0]*(F(1,12)+lam[i]/4)-2*(i==0) for i in range(12)]
    if base != derived:
        raise AssertionError('Independent particular-coefficient reconstruction failed')
    # s=1/k is a formal variable: uniqueness makes every trace affine in s.
    constraints = (0,4,9)
    matrix = [[vector[i] for vector in basis] for i in constraints]
    values = []
    for s in (F(0),F(1),F(2)):
        targets = (4*s,F(0),F(0))
        v = solve(matrix,[value-base[i] for value,i in zip(targets,constraints)])
        q = [base[i]+sum(v[j]*basis[j][i] for j in range(3)) for i in range(12)]
        if tuple(q[i] for i in constraints) != targets:
            raise AssertionError('Ground-neutrality substitution failed')
        if q[6] != 4-4*s or q[11] != 4*s-2:
            raise AssertionError('Direct modular coefficient crosscheck failed')
        values.append(q)
    if any(values[2][i] != 2*values[1][i]-values[0][i] for i in range(12)):
        raise AssertionError('Affine dependence check failed')
    # The third identity gives ordinary index t6=k Q6=4-2k.
    coarse = list(map(F,universal['gamma0_A1_plus_radical3_necessary_levels_without_module_energy_bounds']))
    levels = [int(k) for k in coarse if 4-2*k >= 0]
    if coarse != [1,2,3,6,15] or levels != [1,2]:
        raise AssertionError('Prior level set or sharpened nonnegativity bound failed')
    rank3_floor = min(8-3-F(3*k,k+2) for k in levels)
    pair_floor = F(universal['gamma0_A1_pair_minimum_full_current_coset_c'])
    if rank3_floor != F(7,2) or pair_floor != F(28,11):
        raise AssertionError('Exact current-coset floor check failed')
    return {'prior_gamma0_identities_checked':True,
        'independent_complete_M2_ground_neutrality_solution_checked':True,
        'normalized_d6_trace_affine_in_inverse_level':{'intercept':values[0][11],
            'slope':values[1][11]-values[0][11]},
        'ordinary_d1_index':'4*(k-1)', 'ordinary_d6_index':'4-2*k',
        'rank_three_necessary_levels_without_module_energy_bounds':levels,
        'rank_three_full_current_coset_c_lower_bound':rank3_floor,
        'two_A1_previous_full_current_coset_c_lower_bound':pair_floor,
        'global_current_generated_coset_c_lower_bound':min(rank3_floor,pair_floor),
        'additional_each_A1_joint_witness_constraint':'t_d6=2*k-t_d1+2*t_d4=4-2*k+9*t_c1+5*t_d4 >= 0',
        'scope':'Finite current-representation and real charge-trace positivity only, under the parent universal VOA/modular assumptions. The rank-saturation neutrality argument is analytical and is not proved by this arithmetic helper. No nonvacuum affine-energy bound, new q-series or physical-chain identification.'}


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(x) for x in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--universal',type=Path,default=Path('hi_cft_third_flavoured_universal_results.json'))
    parser.add_argument('--trace',type=Path,default=Path('hi_cft_third_flavoured_trace_results.json'))
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap == resource.RLIM_INFINITY or cap > 128*1024**2:
        raise RuntimeError('Use ROOT coordinated128MiB launcher')
    inputs = (args.universal.resolve(),args.trace.resolve())
    output = args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists() or output in inputs:
        raise ValueError('Choose a new .json output')
    source = Path(__file__).resolve()
    producers = (source.with_name('hi_cft_third_flavoured_universal_check.py'),
                 source.with_name('hi_cft_third_flavoured_trace_check.py'))
    snapshots = {}
    for path in (*inputs,source,*producers):
        if path.stat().st_size > 128*1024:
            raise ValueError('Input/source exceeds128KiB')
        payload = path.read_bytes()
        if len(payload) > 128*1024:
            raise ValueError('Input/source grew beyond128KiB')
        snapshots[path] = payload
    hashes = {str(p):hashlib.sha256(raw).hexdigest() for p,raw in snapshots.items()}
    universal,trace = (json.loads(snapshots[p]) for p in inputs)
    binding = universal['input_and_source_hashes']
    for p in (inputs[1],*producers):
        if binding.get(str(p)) != hashes[str(p)]:
            raise ValueError('Prior universal input/producer binding differs')
    if trace['source_sha256'] != hashes[str(producers[1])]:
        raise ValueError('Original trace producer differs')
    started = monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Ten-second exact followup limit')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,10)
    try:
        result = check(universal,trace)
        result.update(input_and_source_hashes=hashes,seconds=monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(p.read_bytes()!=raw for p,raw in snapshots.items()):
            raise RuntimeError('An input/source changed')
        with pending.open('x') as stream:
            json.dump(encode(result),stream,indent=2,allow_nan=False)
            stream.write('\n')
        if output.exists() or any(p.read_bytes()!=raw for p,raw in snapshots.items()):
            raise RuntimeError('Input/source/output changed before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps(encode({'output':str(output),'seconds':result['seconds'],
        'rank_three_levels':result['rank_three_necessary_levels_without_module_energy_bounds'],
        'current_coset_lower_bound':result['global_current_generated_coset_c_lower_bound']})),flush=True)


if __name__ == '__main__':
    main()
