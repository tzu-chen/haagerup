"""Exact all-trace/dimension13,14 filters of immutable gamma0 witnesses.

Pure stdlib, no common-source edits. ROOT owns all execution under128MiB.
Preserves every surviving small-ground witness and one existence witness
for its d6 ground. The original record controls the affine-energy premise.
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
ENTRY_CAP = 20000
MAX_INPUT_WITNESSES = 1000


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def index(n):
    if type(n) is not int or not 1 <= n <= 14:
        raise ValueError('SU2 dimension outside reviewed1..14')
    return n*(n*n-1)//6


def energy(n,m,k,l):
    return F(n*n-1,4*(k+2))+F(m*m-1,4*(l+2))


def checked_ground(row,d,h,k,l,energy_filter):
    dimension,tleft,tright = 0,0,0
    seen = set()
    for term in row['irreducible_summands']:
        n,m,count = (term[key] for key in ('left_dimension','right_dimension','multiplicity'))
        if type(count) is not int or not 1 <= count <= d or (n,m) in seen:
            raise ValueError('Malformed repeated or nonpositive summand')
        seen.add((n,m))
        if n*m > d or n > k+1 or m > l+1:
            raise ValueError('Small-ground integrability/dimension failed')
        e = energy(n,m,k,l)
        if energy_filter and e > h:
            raise ValueError('Saved energy-filtered ground violates its premise')
        if F(term['affine_ground_weight']) != e or F(term['available_coset_ground_weight']) != h-e:
            raise ValueError('Saved affine energy metadata disagree')
        dimension += n*m*count
        tleft += count*m*index(n)
        tright += count*n*index(m)
    if (dimension,tleft,tright) != (d,row['left_Dynkin_index'],row['right_Dynkin_index']) or row['dimension'] != d:
        raise ValueError('Saved ground dimensions or indices disagree')
    return (tleft,tright)


def realize(d,k,l,targets,energy_filter,entry_cap=ENTRY_CAP,height=F(8,13),form_sign=None):
    """Unbounded-coin support DP; stores one decomposition per exact index pair."""
    if not targets:
        return {}, {'states':0,'allowed_irrep_types':0}
    if any(len(pair) != 2 or any(type(x) is not int or x < 0 for x in pair) for pair in targets):
        raise ValueError('Invalid nonnegative target indices')
    maxleft = max(a for a,b in targets)
    maxright = max(b for a,b in targets)
    maxsum = max(a+b for a,b in targets)
    if maxsum > 2*index(d):
        raise ValueError('Target bound outside reviewed finite representation domain')
    if form_sign not in (None,1,-1):
        raise ValueError('Invariant form sign must be symmetric, alternating or unrestricted')
    types = [(n,m) for n in range(1,min(d,k+1)+1)
             for m in range(1,min(d//n,l+1)+1)
             if not energy_filter or energy(n,m,k,l) <= height]
    dp = [{} for _ in range(d+1)]
    dp[0][(0,0)] = ()
    states = 1
    for n,m in types:
        sign = -1 if (n+m)%2 else 1
        copies = 2 if form_sign is not None and form_sign != sign else 1
        size,dl,dr = copies*n*m,copies*m*index(n),copies*n*index(m)
        for current in range(size,d+1):
            for (a,b),terms in dp[current-size].items():
                target = (a+dl,b+dr)
                if target[0] > maxleft or target[1] > maxright or sum(target) > maxsum:
                    continue
                if target not in dp[current]:
                    states += 1
                    if states > entry_cap:
                        raise RuntimeError('DP resource bound exceeded; no exclusion result may be inferred')
                    dp[current][target] = terms+((n,m),)*copies
    return {target:dp[d][target] for target in targets if target in dp[d]}, {
        'states':states,'allowed_irrep_types':len(types),'entry_cap':entry_cap,
        'invariant_form_sign':form_sign}


def describe(terms,k,l,height=F(8,13)):
    counts = {}
    for pair in terms:
        counts[pair] = counts.get(pair,0)+1
    return {'dimension':sum(n*m*count for (n,m),count in counts.items()),
        'left_Dynkin_index':sum(count*m*index(n) for (n,m),count in counts.items()),
        'right_Dynkin_index':sum(count*n*index(m) for (n,m),count in counts.items()),
        'irreducible_summands':[{'left_dimension':n,'right_dimension':m,'multiplicity':count,
            'affine_ground_weight':energy(n,m,k,l),
            'available_coset_ground_weight':height-energy(n,m,k,l)}
            for (n,m),count in sorted(counts.items())]}


def symmetric_ground(row):
    return all((term['left_dimension']+term['right_dimension'])%2 == 0 or term['multiplicity']%2 == 0
        for term in row['irreducible_summands'])


def all_trace_targets(traces,k,l):
    a,b,c = (traces[name] for name in ('c1','d1','d4'))
    result = {name:[] for name in ('0','b','a','c0','c1','c2','d1','d2','d3','d4','d5','d6')}
    for side,lev in enumerate((k,l)):
        A,B,C = a[side],b[side],c[side]
        values = (4*lev-9*A-B-3*C,20*lev-9*A+B+3*C,
            18*lev+9*A,18*lev+9*A,A,6*lev-6*A,B,10*lev+B-4*C,
            30*lev+9*C,C,4*lev-B-3*C,2*lev-B+2*C)
        for name,value in zip(result,values):result[name].append(value)
    return {name:tuple(value) for name,value in result.items()}


def summary(rows):
    minimum = min((row['residual_central_charge'] for row in rows),default=None)
    return {'level_pair_count':len(rows),
        'witness_count':sum(row['witness_count'] for row in rows),
        'residual_lower_bound':minimum,
        'minimizing_level_pairs':[row['levels'] for row in rows if row['residual_central_charge'] == minimum]}


def filter_record(data,third_only=False,include_d5=False,bilinear_parity=False):
    if type(data.get('affine_energy_filter_applied')) is not bool or data.get('trace_identity_each_factor') != '4+9*t(c1)+t(d1)+3*t(d4)=4*level':
        raise ValueError('Expected the audited joint-ground enumeration schema')
    energy_filter = data['affine_energy_filter_applied']
    if F(data['finite_only_level_sum_upper_bound']) != 40:
        raise ValueError('Original level domain must be the proved sum40 domain')
    levels = data['feasible_levels']
    if len(levels) > 400 or sum(len(row['witnesses']) for row in levels) > MAX_INPUT_WITNESSES:
        raise ValueError('Input exceeds the reviewed400-level/1000-witness domain')
    nonnegative_rows, full_rows = [],[]
    rejected_negative, rejected_dimension = [],[]
    rejected_parity, rejected_other_trace = [],[]
    seen_levels = set()
    total_input = 0
    peak_states = 0
    for level in levels:
        k,l = level['levels']
        if type(k) is not int or type(l) is not int or not 1 <= k <= l or k+l > 40 or (k,l) in seen_levels:
            raise ValueError('Invalid or repeated level pair')
        seen_levels.add((k,l))
        residual = F(2)+F(6,k+2)+F(6,l+2)
        if F(level['residual_central_charge']) != residual or len(level['witnesses']) != level['witness_count']:
            raise ValueError('Original residual/witness count metadata disagree')
        positive = []
        targets,target5s = set(),set()
        for wi,witness in enumerate(level['witnesses']):
            total_input += 1
            traces = {name:checked_ground(witness[name],d,h,k,l,energy_filter) for name,d,h,_ in GROUND}
            if any(4+sum(coef*traces[name][side] for name,_,_,coef in GROUND) != 4*lev for side,lev in enumerate((k,l))):
                raise ValueError('Original positive trace identity failed')
            if bilinear_parity and not all(symmetric_ground(witness[name]) for name,_,_,_ in GROUND):
                rejected_parity.append({'levels':[k,l],'original_witness_index':wi})
                continue
            full_targets = all_trace_targets(traces,k,l)
            if full_targets['0'] != (4,4):
                raise AssertionError('Full trace table vacuum normalization failed')
            target = tuple(2*lev-traces['d1'][side]+2*traces['d4'][side] for side,lev in enumerate((k,l)))
            if any(target[side] != 4-2*lev+9*traces['c1'][side]+5*traces['d4'][side] for side,lev in enumerate((k,l))):
                raise AssertionError('Independent third-index expression disagrees')
            if min(target) < 0:
                rejected_negative.append({'levels':[k,l],'original_witness_index':wi,'required_d6_indices':target})
                continue
            negative = {name:pair for name,pair in full_targets.items() if min(pair) < 0}
            if negative:
                rejected_other_trace.append({'levels':[k,l],'original_witness_index':wi,'negative_ground_indices':negative})
                continue
            targets.add(target)
            target5s.add(full_targets['d5'])
            positive.append({'original_witness_index':wi,'required_d6_indices':target,
                'required_d5_indices':full_targets['d5'],'all_ground_indices':full_targets,
                'small_ground_witness':witness})
        if not positive:
            continue
        base = {'levels':[k,l],'residual_central_charge':residual,'witness_count':len(positive)}
        nonnegative_rows.append(dict(base,witnesses=positive))
        if third_only:
            continue
        found = {}
        # EG gamma0 d6 has grade-one dimension441. Its module form is
        # therefore symmetric even though its ground dimension is14.
        signs = (1,) if bilinear_parity else (None,)
        stat_list = []
        for sign in signs:
            one,stats = realize(14,k,l,targets,energy_filter,form_sign=sign)
            peak_states = max(peak_states,stats['states'])
            stat_list.append(stats)
            for target,terms in one.items():found.setdefault(target,(terms,sign))
        if include_d5:
            found5,stats5 = realize(13,k,l,target5s,energy_filter,height=F(7,13),
                form_sign=1 if bilinear_parity else None)
            peak_states = max(peak_states,stats5['states'])
            stat_list.append(dict(stats5,module='d5'))
        survivors = []
        for item in positive:
            target = item['required_d6_indices']
            target5 = item['required_d5_indices']
            if target not in found or include_d5 and target5 not in found5:
                rejected_dimension.append({'levels':[k,l],
                    'original_witness_index':item['original_witness_index'],
                    'required_d6_indices':target,'required_d5_indices':target5,
                    'd6_supported':target in found,
                    'd5_supported':target5 in found5 if include_d5 else None})
                continue
            terms,sign = found[target]
            d6 = describe(terms,k,l)
            if d6['dimension'] != 14 or (d6['left_Dynkin_index'],d6['right_Dynkin_index']) != target:
                raise AssertionError('Independent d6 witness substitution failed')
            entry = dict(item,d6_witness=d6,d6_invariant_form_sign=sign)
            if include_d5:
                d5 = describe(found5[target5],k,l,F(7,13))
                if d5['dimension'] != 13 or (d5['left_Dynkin_index'],d5['right_Dynkin_index']) != target5:
                    raise AssertionError('Independent d5 witness substitution failed')
                entry['d5_witness'] = d5
            survivors.append(entry)
        if survivors:
            full_rows.append(dict(base,witness_count=len(survivors),witnesses=survivors,DP_statistics=stat_list))
    if total_input != data['total_representation_witness_count'] or len(levels) != data['feasible_level_pair_count']:
        raise ValueError('Original enumeration totals disagree')
    return {'affine_energy_filter_applied':energy_filter,'energy_premise':data['energy_premise'],
        'third_identity_each_factor':'t(d6)+t(d1)-2*t(d4)=2*level',
        'd6_ground':{'dimension':14,'weight':F(8,13)},
        'd5_ground':{'dimension':13,'weight':F(7,13)},
        'all_ground_nonnegative_indices_required':True,
        'pre_DP_filters':['d6_index_nonnegative','every_ground_index_nonnegative']+
            (['odd_small_ground_symmetric_form'] if bilinear_parity else []),
        'bilinear_parity_filter_applied':bilinear_parity,
        'bilinear_scope':'Odd3/7/5/13 grounds force a symmetric nondegenerate module form. The d6 ground has dimension14, but its odd grade-one dimension441 forces the same symmetric form on every grade. No categorical Frobenius-Schur indicator is assumed.',
        'original_summary':{'level_pair_count':len(levels),'witness_count':total_input,
            'residual_lower_bound':data['residual_lower_bound_with_these_filters']},
        'third_nonnegative_summary':summary(nonnegative_rows),
        'third_nonnegative_levels':nonnegative_rows,'negative_index_rejections':rejected_negative,
        'odd_ground_parity_rejections':rejected_parity,
        'other_negative_ground_index_rejections':rejected_other_trace,
        'd6_dimension_filter_applied':not third_only,
        'd5_dimension_filter_applied':include_d5 and not third_only,
        'd6_dimension_summary':summary(full_rows) if not third_only else None,
        'd6_dimension_levels':full_rows,'d6_nonrealizable_index_rejections':rejected_dimension,
        'peak_DP_states':peak_states,
        'scope':'All surviving original small-ground witnesses are retained. For each, one supported d6/d5 existence witness is saved; this is not an enumeration of every large-ground decomposition. Only the explicitly selected bilinear parity conditions are imposed. No fusion or higher-character constraints are imposed. Resource failure raises an error and is never reported as nonexistence.'}


def selftest():
    # Independent exhaustive small decompositions, with no DP recurrence.
    def literal(d,form_sign=None):
        types = [(n,m) for n in range(1,d+1) for m in range(1,d//n+1)]
        answer = set()
        def visit(i,left,a,b):
            if left == 0:
                answer.add((a,b));return
            if i == len(types):
                return
            n,m = types[i]
            for count in range(left//(n*m)+1):
                sign = -1 if (n+m)%2 else 1
                if form_sign is not None and form_sign != sign and count%2:
                    continue
                visit(i+1,left-count*n*m,a+count*m*index(n),b+count*n*index(m))
        visit(0,d,0,0)
        return answer
    cases = []
    for d in (3,4,5,7):
        for sign in (None,1,-1):
            expected = literal(d,sign)
            # Add unattainable index pairs as well, so refusal is tested.
            targets = {(a,b) for a in range(index(d)+1) for b in range(index(d)+1) if a+b <= index(d)}
            actual,stats = realize(d,14,14,targets,False,form_sign=sign)
            if set(actual) != expected:
                raise AssertionError('DP support differs from exhaustive small decomposition')
            for target,terms in actual.items():
                row = describe(terms,14,14)
                if row['dimension'] != d or (row['left_Dynkin_index'],row['right_Dynkin_index']) != target:
                    raise AssertionError('Small DP reconstruction failed')
            cases.append({'dimension':d,'form_sign':sign,'distinct_index_pairs':len(expected),'DP_states':stats['states']})
    try:
        realize(3,14,14,{(4,0)},False,entry_cap=1)
    except RuntimeError:
        pass
    else:
        raise AssertionError('DP resource failure was not explicit')
    return {'literal_support_comparisons':cases,'resource_failure_is_not_exclusion':True}


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {key:encode(item) for key,item in value.items()}
    if isinstance(value,(list,tuple)):return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--third-only',action='store_true')
    parser.add_argument('--include-d5',action='store_true')
    parser.add_argument('--bilinear-parity',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap == resource.RLIM_INFINITY or cap > 128*1024**2:
        raise RuntimeError('Use ROOT coordinated128MiB launcher')
    source = Path(__file__).resolve()
    original = source.with_name('hi_cft_third_gamma0_joint_ground_check.py')
    input_path,output = args.input.resolve(),args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists() or output in (input_path,source,original):
        raise ValueError('Choose a new noncolliding.json output')
    if input_path.stat().st_size > 2*1024**2:
        raise ValueError('Input JSON exceeds2MiB')
    payload = input_path.read_bytes()
    if len(payload) > 2*1024**2:
        raise ValueError('Input grew beyond2MiB')
    data = json.loads(payload)
    hashes = {str(source):sha(source),str(original):sha(original)}
    if data.get('source_sha256') != hashes[str(original)]:
        raise ValueError('Input was not produced by the unchanged audited base enumeration')
    input_hash = hashlib.sha256(payload).hexdigest()
    started = monotonic()
    def timeout(signum,frame):raise TimeoutError('Sixty-second exact DP limit')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,60)
    def unchanged():
        if sha(input_path) != input_hash or any(sha(path) != value for path,value in hashes.items()):
            raise RuntimeError('Input or producer source changed during filtering')
    try:
        result = filter_record(data,args.third_only,args.include_d5,args.bilinear_parity)
        result.update(selftest=selftest(),input_record={'path':str(input_path),'sha256':input_hash},
            producer_source_hashes=hashes,seconds=monotonic()-started,
            peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
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
    print(json.dumps(encode({'output':str(output),'seconds':result['seconds'],
        'nonnegative_summary':result['third_nonnegative_summary'],
        'dimension_summary':result['d6_dimension_summary']})),flush=True)


if __name__ == '__main__':main()
