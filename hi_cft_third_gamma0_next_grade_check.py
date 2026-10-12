"""Exact necessary next-grade current tests on immutable pair witnesses.

Standard library; ROOT alone executes under128MiB. Known small-ground
decompositions are tested exactly. Other grounds use proven universal
lower bounds, never a single arbitrary stored existence witness.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
import math
from pathlib import Path
import resource
import signal
from time import monotonic

from hi_cft_third_gamma0_next_grade import (
    coefficient_forms,evaluate,index,affine_grade_one,vacuum_grade_two,selftest)


def sha(path):
    with Path(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {key:encode(item) for key,item in value.items()}
    if isinstance(value,(tuple,list)):return [encode(item) for item in value]
    return value


def terms(row):
    return [(r['left_dimension'],r['right_dimension'],r['multiplicity'])
        for r in row['irreducible_summands']]


def universal_affine_minimum(d,tleft,tright,k,l):
    """Relax boundary-null supports independently, giving safe lower bounds."""
    bl = d >= k+1 and tleft >= index(k+1)
    br = d >= l+1 and tright >= index(l+1)
    dim = F(6*d)-(F(d*(k+3),k+1) if bl else 0)-(F(d*(l+3),l+1) if br else 0)
    left = F(6*tleft+4*d)-(F(tleft*index(k+3),index(k+1)) if bl else 0)-(F(tleft*(l+3),l+1) if br else 0)
    right = F(6*tright+4*d)-(F(tright*index(l+3),index(l+1)) if br else 0)-(F(tright*(k+3),k+1) if bl else 0)
    return {'dimension':max(0,math.ceil(dim)),
        'left_index':max(0,math.ceil(left)),'right_index':max(0,math.ceil(right)),
        'left_boundary_null_possible':bl,'right_boundary_null_possible':br,
        'exact_if_neither_boundary_possible':not bl and not br,
        'scope':'A universal lower bound over every possible ground decomposition with these dimension/indices. Independent maximal null subtractions relax correlations; no stored large-ground witness is treated as exhaustive.'}


def minimum_selftest():
    cases = 0
    for k in range(1,8):
        for l in range(1,8):
            for n in range(1,min(7,k+1)+1):
                for m in range(1,min(7,l+1)+1):
                    d,tl,tr = n*m,m*index(n),n*index(m)
                    bound = universal_affine_minimum(d,tl,tr,k,l)
                    actual = affine_grade_one([(n,m,1)],k,l)
                    if any(bound[key] > actual[key] for key in ('dimension','left_index','right_index')):
                        raise AssertionError('Universal null relaxation exceeded exact generated module')
                    if bound['exact_if_neither_boundary_possible'] and any(bound[key] != actual[key] for key in ('dimension','left_index','right_index')):
                        raise AssertionError('No-boundary exactness failed')
                    cases += 1
    return {'universal_minimum_irrep_controls':cases}


def certificate(data):
    if not data.get('d6_dimension_filter_applied') or not data.get('d5_dimension_filter_applied'):
        raise ValueError('Use the completed d5/d6 support report')
    rows = data['d6_dimension_levels']
    if len(rows) > 400 or sum(len(r['witnesses']) for r in rows) > 1000:
        raise ValueError('Input exceeds reviewed witness domain')
    if len(rows) != data['d6_dimension_summary']['level_pair_count'] or sum(len(r['witnesses']) for r in rows) != data['d6_dimension_summary']['witness_count']:
        raise ValueError('Input support-summary counts disagree')
    forms = coefficient_forms()
    allrows,survivors = [],[]
    seen = set()
    for row in rows:
        k,l = row['levels']
        if type(k) is not int or type(l) is not int or not 1 <= k <= l or k+l > 40 or (k,l) in seen:
            raise ValueError('Invalid level pair')
        seen.add((k,l))
        if len(row['witnesses']) != row['witness_count']:
            raise ValueError('Input per-level witness count disagrees')
        retained = []
        results = []
        for item in row['witnesses']:
            ground = item['small_ground_witness']
            parameters = [(lev,ground['c1'][side+'_Dynkin_index'],
                ground['d1'][side+'_Dynkin_index'],ground['d4'][side+'_Dynkin_index'])
                for lev,side in ((k,'left'),(l,'right'))]
            next_indices = {name:tuple(evaluate(form,*p) for p in parameters)
                for name,form in forms['next_forms'].items()}
            ground_indices = {name:tuple(evaluate(form,*p) for p in parameters)
                for name,form in forms['leading_forms'].items()}
            if ground_indices['0'] != (4,4):
                raise ValueError('Original ground trace equations failed')
            if any(tuple(map(F,item['all_ground_indices'][name])) != pair for name,pair in ground_indices.items()):
                raise ValueError('Inherited full ground-trace table disagrees')
            failures = []
            comparisons = {}
            for name,pair in next_indices.items():
                if any(value.denominator != 1 or value < 0 for value in pair):
                    failures.append({'module':name,'reason':'next-grade index negative or nonintegral','indices':pair})
                if name == '0':
                    minimum = vacuum_grade_two(k,l)
                elif name in ground:
                    chosen = terms(ground[name])
                    if sum(n*m*count for n,m,count in chosen) != forms['leading_nonpolar_dimensions'][name]:
                        raise ValueError('Known small-ground dimension disagrees')
                    if tuple(sum(count*(m*index(n) if side == 0 else n*index(m)) for n,m,count in chosen) for side in (0,1)) != ground_indices[name]:
                        raise ValueError('Known small-ground index disagrees')
                    minimum = affine_grade_one(chosen,k,l)
                else:
                    minimum = universal_affine_minimum(forms['leading_nonpolar_dimensions'][name],
                        *ground_indices[name],k,l)
                remaining = {'dimension':forms['next_dimensions'][name]-minimum['dimension'],
                    'left_index':pair[0]-minimum['left_index'],
                    'right_index':pair[1]-minimum['right_index']}
                if min(remaining.values()) < 0:
                    failures.append({'module':name,'reason':'mandatory affine contribution exceeds available next grade',
                        'available_after_minimum':remaining})
                comparisons[name] = {'next_grade_dimension':forms['next_dimensions'][name],
                    'next_grade_indices':pair,'mandatory_affine_minimum':minimum,
                    'available_after_minimum':remaining}
            result = {'original_witness_index':item['original_witness_index'],
                'small_ground_witness':ground,'all_next_grade_comparisons':comparisons,
                'passes_necessary_tests':not failures,'failures':failures}
            results.append(result)
            if not failures:retained.append(result)
        common = {'levels':[k,l],'residual_central_charge':F(row['residual_central_charge'])}
        allrows.append(dict(common,witnesses=results))
        if retained:survivors.append(dict(common,witness_count=len(retained),witnesses=retained))
    lower = min((row['residual_central_charge'] for row in survivors),default=None)
    return {'coefficient_certificate':forms,'input_energy_filter_applied':data['affine_energy_filter_applied'],
        'input_bilinear_filter_applied':data['bilinear_parity_filter_applied'],
        'input_energy_premise':data['energy_premise'],
        'all_tested_levels':allrows,'surviving_levels':survivors,
        'surviving_level_pair_count':len(survivors),
        'surviving_witness_count':sum(row['witness_count'] for row in survivors),
        'residual_lower_bound':lower,
        'residual_minimizers':[row['levels'] for row in survivors if row['residual_central_charge'] == lower],
        'scope':'The additional next-grade tests use no nonvacuum affine-energy bound. Any original energy filter is retained explicitly. Exact affine descendants are used only for completely specified small grounds; all other grounds receive universal minima. Nonnegative leftovers need not be actual representations. No larger-grade DP, fusion or VOA existence claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap == resource.RLIM_INFINITY or cap > 128*1024**2:
        raise RuntimeError('Use ROOT coordinated128MiB launcher')
    input_path,output = args.input.resolve(),args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists() or output == input_path:
        raise ValueError('Choose a new noncolliding.json output')
    if input_path.stat().st_size > 2*1024**2:raise ValueError('Input exceeds2MiB')
    payload = input_path.read_bytes()
    if len(payload) > 2*1024**2:raise ValueError('Input grew beyond2MiB')
    data = json.loads(payload)
    source = Path(__file__).resolve()
    source_paths = [source,source.with_name('hi_cft_third_gamma0_next_grade.py'),
        source.with_name('hi_cft_third_flavoured_trace_check.py')]
    hashes = {str(p):sha(p) for p in source_paths}
    inherited = data.get('producer_source_hashes',{})
    required = {str(source.with_name(name)) for name in (
        'hi_cft_third_gamma0_d6_check.py','hi_cft_third_gamma0_joint_ground_check.py')}
    if not required <= inherited.keys() or any(sha(path) != value for path,value in inherited.items()):
        raise ValueError('Input was not produced by unchanged audited ground-support sources')
    hashes.update(inherited)
    input_hash = hashlib.sha256(payload).hexdigest()
    started = monotonic()
    def timeout(signum,frame):raise TimeoutError('Thirty-second exact next-grade limit')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,30)
    def unchanged():
        if sha(input_path) != input_hash or any(sha(path) != value for path,value in hashes.items()):
            raise RuntimeError('An input or producer changed during checking')
    try:
        result = certificate(data)
        result.update(selftest=selftest(),minimum_selftest=minimum_selftest(),
            input_record={'path':str(input_path),'sha256':input_hash},producer_source_hashes=hashes,
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        unchanged()
        with pending.open('x') as stream:
            json.dump(encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        unchanged()
        if output.exists():raise RuntimeError('Output appeared before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():pending.unlink()
    print(json.dumps(encode({'output':str(output),'surviving_pairs':result['surviving_level_pair_count'],
        'residual_lower_bound':result['residual_lower_bound'],'seconds':result['seconds']})),flush=True)


if __name__ == '__main__':main()
