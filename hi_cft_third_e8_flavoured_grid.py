"""Property-based exact current-host filter from flavoured characters.

All prior producer/output files remain unchanged. Standard library only;
ROOT alone may execute this under the coordinated128MiB launcher.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import resource
import signal
from time import monotonic


PRIOR = frozenset({0,372,379,483,496,514,579,600,613,614,615,617})
RANK3_LEVELS = frozenset({1,2,3,6,15})
DESCRIPTION = re.compile(r'A1_(\d+)(?: x A1_(\d+))? \+ U1\^(\d+)')


def read(path):
    raw=path.read_bytes()
    if len(raw)>2*1024**2:
        raise ValueError('Unexpectedly large exact catalog input')
    return json.loads(raw),raw


def host_reasons(host, module_energy):
    reasons=[]
    number=host['semisimple_database_number']
    dimension=host['W1_dimension']
    radical=host['abelian_rank']
    if number in PRIOR:
        reasons.append('previous_twelve_host_exact_exclusion')
    if dimension == 19:
        reasons.append('gamma1_reductive_current_algebra_exhaustion')
        return reasons
    if dimension != 6:
        raise ValueError('Unexpected full current dimension')
    if radical>3:
        reasons.append('gamma0_positive_trace_radical_rank_at_most_three')
        return reasons
    match=DESCRIPTION.fullmatch(host['factor_description'])
    if match is None:
        raise ValueError('Unreviewed six-current factor description')
    levels=[int(x) for x in match.group(1,2) if x is not None]
    if int(match.group(3)) != radical or 3*len(levels)+radical != 6:
        raise ValueError('Current type/rank/dimension mismatch')
    if any(k>39 for k in levels):
        reasons.append('gamma0_individual_A1_level_above_39')
    if radical == 3 and len(levels) == 1:
        if levels[0] not in RANK3_LEVELS:
            reasons.append('gamma0_rank_three_charge_support_and_finite_index_partition')
        if module_energy and levels[0] not in (1,3):
            reasons.append('gamma0_unitary_module_energy_refinement')
    elif radical == 0 and len(levels) == 2:
        if sum(levels)>40:
            reasons.append('gamma0_two_A1_total_level_above_40')
    else:
        raise ValueError('Unreviewed reductive six-current type')
    return reasons


def calculate(catalog,characters,certificate,module_energy):
    if not certificate['gamma1_all_cases_covered'] or not certificate['M2_functionals_annihilate_every_basis_vector']:
        raise ValueError('Universal character certificate did not pass')
    if F(certificate['gamma0_A1_level_upper_bound']) != 39:
        raise ValueError('Unexpected certified individual level bound')
    if set(map(F,certificate['gamma0_A1_plus_radical3_necessary_levels_without_module_energy_bounds'])) != RANK3_LEVELS:
        raise ValueError('Unexpected certified rank-three level set')
    total_bound=(8+9*4+56+3*20)//4
    if total_bound != 40:
        raise AssertionError('Two-factor total-index arithmetic failed')
    if F(certificate['gamma0_A1_pair_sum_level_upper_bound']) != total_bound:
        raise ValueError('Unexpected certified two-factor level bound')
    hosts=[r for r in characters['candidate_rows'] if r['passes_all_including_small_residual_field']]
    by_number={r['semisimple_database_number']:r for r in hosts}
    if len(by_number) != len(hosts):
        raise ValueError('Host database numbers are not unique in this input')
    reasons={number:host_reasons(row,module_energy) for number,row in by_number.items()}
    kept_hosts=[r for r in hosts if not reasons[r['semisimple_database_number']]]
    rows=[]
    removed_pairs=Counter()
    for source in catalog['candidate_rows']:
        support=[]
        for witness in source['possible_full_W1_hosts']:
            number=witness['host_semisimple_database_number']
            if number not in by_number or witness['W1_dimension'] != by_number[number]['W1_dimension']:
                raise ValueError('Denominator witness has no matching certified host')
            if reasons[number]:
                removed_pairs[number]+=1
            else:
                support.append(witness)
        if support:
            row=dict(source)
            row['possible_full_W1_hosts']=support
            rows.append(row)
    lower_bound=F(28,11) if module_energy else F(40,17)
    by_charge=defaultdict(list)
    for row in rows:
        by_charge[F(row['coset_c'])].append({'denominator_database_number':row['semisimple_database_number'],
            'denominator_radical_rank':row['abelian_rank'],
            'hosts':sorted(w['host_semisimple_database_number'] for w in row['possible_full_W1_hosts'])})
    full_min=min((F(r['residual_c']) for r in kept_hosts),default=None)
    checks={
        'all_prior_excluded_hosts_present':PRIOR <= set(by_number),
        'no_gamma1_host_retained':all(r['W1_dimension']==6 for r in kept_hosts),
        'no_radical_rank_above_three_retained':all(r['abelian_rank']<=3 for r in kept_hosts),
        'all_retained_host_properties_pass':all(not host_reasons(r,module_energy) for r in kept_hosts),
        'all_retained_full_current_charges_above_theorem_bound':all(F(r['residual_c'])>=lower_bound for r in kept_hosts),
        'all_retained_denominator_charges_above_theorem_bound':all(F(r['coset_c'])>=lower_bound for r in rows),
        'no_rejected_host_in_denominator_witnesses':all(not reasons[w['host_semisimple_database_number']]
            for r in rows for w in r['possible_full_W1_hosts']),
        'no_c_equal_two':F(2) not in by_charge,
        'no_c_equal_65_over_31':F(65,31) not in by_charge,
        'no_c_equal_13_over_7':F(13,7) not in by_charge,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return {'mode':'additional_unitary_module_energy' if module_energy else 'finite_representation_and_PSD_only',
        'input_denominator_rows':len(catalog['candidate_rows']),
        'remaining_denominator_rows':len(rows),
        'input_full_current_hosts':len(hosts),'remaining_full_current_hosts_count':len(kept_hosts),
        'theorem_current_coset_lower_bound':str(lower_bound),
        'minimum_retained_full_current_residual_c':str(full_min) if full_min is not None else None,
        'host_decisions':[{'database_number':r['semisimple_database_number'],
            'W1_dimension':r['W1_dimension'],'radical_rank':r['abelian_rank'],
            'factor_description':r['factor_description'],
            'excluded_reasons':reasons[r['semisimple_database_number']]} for r in hosts],
        'removed_witness_pairs_by_host':dict(sorted(removed_pairs.items())),
        'checks':checks,
        'retained_charge_grid':{str(c):by_charge[c] for c in sorted(by_charge)},
        'candidate_rows':rows,'remaining_full_current_hosts':kept_hosts,
        'scope':'Filters a saved necessary E8 current-denominator catalog by actual full-current properties. The default modular/Lie/PSD rules require the stated strongly regular unitary Haagerup-character setup, not rationality of the host33 coset. Optional energy rules additionally require nonnegative module commutant energy. Empty saved-range output does not mean every denominator at every central charge is excluded. No chain-to-current-coset map is proved.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog',type=Path,default=Path('hi_cft_sixhour_e8_proper_current_results.json'))
    parser.add_argument('--characters',type=Path,default=Path('hi_cft_sixhour_e8_character_results.json'))
    parser.add_argument('--certificate',type=Path,default=Path('hi_cft_third_flavoured_universal_results.json'))
    parser.add_argument('--with-unitary-module-energy',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:
        raise RuntimeError('Use ROOT coordinated128MiB launcher')
    output=args.output.resolve()
    pending=output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists():
        raise ValueError('Use a new JSON output')
    source=Path(__file__).resolve()
    snapshots={source:source.read_bytes()}
    inputs=[]
    for path in (args.catalog,args.characters,args.certificate):
        resolved=path.resolve()
        if resolved==output:
            raise ValueError('Output must differ from each input')
        data,raw=read(resolved)
        snapshots[resolved]=raw
        inputs.append(data)
    proof_source=source.with_name('hi_cft_third_flavoured_universal_check.py')
    proof_bytes=proof_source.read_bytes()
    if inputs[2]['input_and_source_hashes'].get(str(proof_source)) != hashlib.sha256(proof_bytes).hexdigest():
        raise ValueError('Universal certificate producer hash mismatch')
    snapshots[proof_source]=proof_bytes
    started=monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Thirty-second exact catalog limit')
    previous=signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,30)
    try:
        result=calculate(*inputs,args.with_unitary_module_energy)
        result.update(input_and_source_hashes={str(p):hashlib.sha256(raw).hexdigest() for p,raw in snapshots.items()},
            seconds=monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(p.read_bytes()!=raw for p,raw in snapshots.items()):
            raise RuntimeError('Input or source changed')
        with pending.open('x') as handle:
            json.dump(result,handle,indent=2,allow_nan=False)
            handle.write('\n')
        if output.exists() or any(p.read_bytes()!=raw for p,raw in snapshots.items()):
            raise RuntimeError('Input/source/output changed before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps({key:result[key] for key in ('mode','remaining_denominator_rows',
        'remaining_full_current_hosts_count','minimum_retained_full_current_residual_c','checks')},indent=2))


if __name__=='__main__':
    main()
