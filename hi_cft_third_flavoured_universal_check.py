"""Bounded exact trace identities, gamma0 level bound and gamma1 Lie count.

No tensors, q-series, floating linear algebra, workers or extra numerical job.
Prepared for ROOT's128MiB coordinated slot; proof assumptions live in the note.
"""
import argparse
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import resource
import signal
from time import monotonic


def check(saved):
    expected_names = ['0','b','a','c0','c1','c2','d1','d2','d3','d4','d5','d6']
    if saved['basis_order'] != expected_names:
        raise ValueError('Unexpected modular coordinate basis')
    space = saved['weight_two_space']
    if not space['consistent'] or space['dimension'] != 3 or len(space['basis']) != 3:
        raise ValueError('Missing complete exact M2 basis')
    minus = lambda v:F(v[0])+9*F(v[4])-F(v[10])
    plus = lambda v:F(v[0])+9*F(v[4])+F(v[6])+3*F(v[9])
    third = lambda v:F(v[11])+F(v[6])-2*F(v[9])
    if any(minus(v) or plus(v) or third(v) for v in space['basis']):
        raise AssertionError('Universal functionals fail on M2 basis')
    chi = [[F(x) for x in row] for row in saved['characteristic_matrix_chi']]
    lam = list(map(F,saved['Lambda']))
    # gamma0 has only its vacuum polar part; particular trace is
    # E2 chi_gamma0/12 + D chi_gamma0/4.
    base0 = [chi[i][0]*(F(1,12)+lam[i]/4)-2*(i == 0) for i in range(12)]
    base1 = [F(saved['particular_Q_leading_coefficients'][name]) for name in expected_names]
    constants = {'gamma0':{'minus':minus(base0),'plus':plus(base0),'third':third(base0)},
                 'gamma1':{'minus':minus(base1),'plus':plus(base1),'third':third(base1)}}
    if constants != {'gamma0':{'minus':0,'plus':4,'third':2},
                     'gamma1':{'minus':6,'plus':8,'third':4}}:
        raise AssertionError('Universal identity constants failed')
    max_index = lambda d:F(d*(d*d-1),6)
    maxima = {d:max_index(d) for d in (3,7,5)}
    level_bound = (4+9*maxima[3]+maxima[7]+3*maxima[5])/4
    if maxima != {3:4,7:56,5:20} or level_bound != 39:
        raise AssertionError('Gamma0 dimension-index bound failed')
    rows = []
    for a,b,c,d,e,r in itertools.product(range(7),range(3),range(2),range(2),range(2),range(2)):
        if 3*a+8*b+10*c+14*d+15*e+r != 19:
            continue
        if a >= 2:
            reason = 'Each A1 must act nontrivially on the same3D c1 ground, whose multiplicity commutant is abelian'
        elif b and c:
            reason = 'A2_1 forces d1=3+3bar; commuting B2 then has zero d1 trace, contradicting6=8k'
        elif b >= 2:
            reason = 'Two A2_1 factors each require full3+3bar action on the same6D d1 ground'
        elif a and r:
            reason = 'A1 action on3D c1 has abelian multiplicity commutant; selfduality kills all radical charges'
        else:
            reason = None
        rows.append({'A1':a,'A2':b,'B2':c,'G2':d,'A3':e,'radical_rank':r,'obstruction':reason})
    expected = {(3,0,1,0,0,0),(1,2,0,0,0,0),(6,0,0,0,0,1),
                (0,1,1,0,0,1),(1,0,0,0,1,1)}
    actual = {tuple(row[name] for name in ('A1','A2','B2','G2','A3','radical_rank')) for row in rows}
    if actual != expected or any(row['obstruction'] is None for row in rows):
        raise AssertionError('Small reductive Lie enumeration or obstruction coverage failed')
    def partitions(total,largest):
        if largest == 0:
            return [()] if total == 0 else []
        return [prefix+(count,) for count in range(total//largest+1)
            for prefix in partitions(total-count*largest,largest-1)]
    real7 = [counts for counts in partitions(7,7)
             if all(counts[n-1] % 2 == 0 for n in (2,4,6))]
    indices7 = sorted({sum(counts[n-1]*max_index(n) for n in range(1,8)) for counts in real7})
    all_indices7 = sorted({sum(counts[n-1]*max_index(n) for n in range(1,8)) for counts in partitions(7,7)})
    possible_levels = sorted({1+index/4 for index in indices7 if index % 4 == 0})
    if indices7 != [0,2,4,6,8,20,56] or possible_levels != [1,2,3,6,15]:
        raise AssertionError('Seven-dimensional symmetric SU2 representation check failed')
    if sorted({1+index/4 for index in all_indices7 if index % 4 == 0}) != possible_levels:
        raise AssertionError('The unrestricted seven-dimensional partition bound differs')
    sum_level_bound = (8+9*maxima[3]+maxima[7]+3*maxima[5])/4
    a1_residual = lambda k:8-3-F(3*k,k+2)
    pair_residual = lambda k1,k2:8-F(3*k1,k1+2)-F(3*k2,k2+2)
    smallest_single = min(a1_residual(int(k)) for k in possible_levels)
    smallest_pair = min(pair_residual(k1,k2) for k1 in range(1,40)
                        for k2 in range(1,41-k1))
    if sum_level_bound != 40 or smallest_single != F(40,17) or smallest_pair != F(28,11):
        raise AssertionError('Current central-charge extremum check failed')
    return {'M2_functionals_annihilate_every_basis_vector':True,
        'identity_minus': 'Q_vac_grade1+9 Q_c1_ground-Q_d5_ground=constant*kappa',
        'identity_plus': 'Q_vac_grade1+9 Q_c1_ground+Q_d1_ground+3 Q_d4_ground=constant*kappa',
        'identity_third': 'Q_d6_ground+Q_d1_ground-2 Q_d4_ground=constant*kappa',
        'identity_constants':constants,'gamma0_particular_coefficients':dict(zip(expected_names,base0)),
        'gamma0_A1_ground_dimension_index_maxima':maxima,'gamma0_A1_level_upper_bound':level_bound,
        'gamma0_A1_level60_excluded':60 > level_bound,
        'gamma1_reductive_Lie_dimension19_radical_at_most1_cases':rows,
        'gamma1_all_cases_covered':True,
        'gamma0_seven_dimensional_symmetric_SU2_indices':indices7,
        'gamma0_seven_dimensional_all_SU2_indices':all_indices7,
        'gamma0_A1_plus_radical3_necessary_levels_without_module_energy_bounds':possible_levels,
        'gamma0_A1_pair_sum_level_upper_bound':sum_level_bound,
        'gamma0_A1_plus_radical3_minimum_full_current_coset_c':smallest_single,
        'gamma0_A1_pair_minimum_full_current_coset_c':smallest_pair,
        'global_current_generated_coset_c_lower_bound':min(smallest_single,smallest_pair),
        'scope': 'Exact finite algebra bookkeeping for the separate proof. Analytic inputs are Jacobi modularity, strong regularity/unitarity, real positive Cartan rational form, selfcontragredience of the actual Haagerup modules, affine integrability and the stated low character grounds. No module/coset energy bound enters global gamma1 exhaustion. The executable does not prove those analytic premises or identify the chain CFT.'}


def encode(x):
    if isinstance(x,F):
        return str(x)
    if isinstance(x,dict):
        return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [encode(v) for v in x]
    return x


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=Path('hi_cft_third_flavoured_trace_results.json'))
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    limit = resource.getrlimit(resource.RLIMIT_AS)[0]
    if limit == resource.RLIM_INFINITY or limit > 128*1024**2:
        raise RuntimeError('Use the sole coordinated launcher under128MiB AS')
    input_path,output = args.input.resolve(),args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists() or output == input_path:
        raise ValueError('Use a new .json output')
    if input_path.stat().st_size > 128*1024:
        raise ValueError('Input certificate exceeds128KiB')
    source = Path(__file__).resolve()
    producer = source.with_name('hi_cft_third_flavoured_trace_check.py')
    snapshots = {path:path.read_bytes() for path in (input_path,source,producer)}
    hashes = {str(path):hashlib.sha256(payload).hexdigest() for path,payload in snapshots.items()}
    saved = json.loads(snapshots[input_path])
    if saved['source_sha256'] != hashes[str(producer)]:
        raise ValueError('Original producer hash mismatch')
    started = monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Ten-second exact algebra deadline')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,10)
    try:
        result = check(saved)
        result.update(input_and_source_hashes=hashes,seconds=monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(path.read_bytes() != payload for path,payload in snapshots.items()):
            raise RuntimeError('Input/source changed during certificate')
        with pending.open('x') as handle:
            json.dump(encode(result),handle,indent=2,allow_nan=False)
            handle.write('\n')
        if output.exists() or any(path.read_bytes() != payload for path,payload in snapshots.items()):
            raise RuntimeError('Input/source/output changed before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps({'output':str(output),'seconds':result['seconds'],
        'gamma0_A1_bound':encode(result['gamma0_A1_level_upper_bound']),
        'gamma1_Lie_cases':len(result['gamma1_reductive_Lie_dimension19_radical_at_most1_cases']),
        'gamma1_all_cases_covered':result['gamma1_all_cases_covered']},indent=2))


if __name__ == '__main__':
    main()
