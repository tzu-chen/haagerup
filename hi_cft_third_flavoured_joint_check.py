"""Exact simultaneous A3_1/A1_5 obstruction from the saved weight-two test.

Standard library only, fixed tiny integer partitions and rational identities.
No Frobenius--Schur sign assumption, no q-series or tensor computation.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def su2_partitions(dimension):
    # Only total multiplicity dimensions<=3 are used. Every finite SU2 irrep
    # then has label<=2 and index ell(ell+1)(ell+2)/6.
    if dimension not in (0,1,2,3):
        raise ValueError('Unreviewed representation dimension')
    result = []
    for triplets in range(dimension//3+1):
        for doublets in range(dimension//2+1):
            singlets = dimension-3*triplets-2*doublets
            if singlets >= 0:
                result.append({'singlets':singlets,'doublets':doublets,
                    'triplets':triplets,'Dynkin_index':doublets+4*triplets})
    return result


def check(saved):
    names = saved['basis_order']
    if names != ['0','b','a','c0','c1','c2','d1','d2','d3','d4','d5','d6']:
        raise ValueError('Unexpected modular basis')
    space = saved['weight_two_space']
    neutral = saved['neutral_system']
    if not space['consistent'] or space['dimension'] != 3 or len(space['basis']) != 3:
        raise ValueError('Missing validated complete weight-two basis')
    if not neutral['consistent'] or neutral['dimension'] != 0 or neutral['basis']:
        raise ValueError('A3 current trace was not uniquely fixed')
    functional = lambda v:F(v[0])+9*F(v[4])-F(v[10])
    if any(functional(v) for v in space['basis']):
        raise AssertionError('Universal trace functional does not annihilate M2')
    base = saved['particular_Q_leading_coefficients']
    constant = F(base['0'])+9*F(base['c1'])-F(base['d5'])
    if constant != 6:
        raise AssertionError('Universal trace constant differs from6')
    unique = saved['unique_neutral_solution_leading_Q']
    if F(unique['0']) != 8 or F(unique['d5']) != 2:
        raise AssertionError('Unexpected A3 current trace coefficients')
    a3 = []
    for pairs in range(2):
        for sixes in range(2):
            singlets = 8-8*pairs-6*sixes
            index = 2*pairs+2*sixes
            if singlets >= 0 and index == 2:
                # Each nontrivial A3 type has multiplicity one, so its
                # commuting SU2 action is trivial. Only singlets can carry it.
                if singlets > 2:
                    raise AssertionError('Unexpected A3 multiplicity dimension')
                a3.append({'four_plus_conjugate_four_pairs':pairs,
                    'sixes':sixes,'singlets':singlets,
                    'commuting_SU2_possibilities':su2_partitions(singlets)})
    if len(a3) != 2:
        raise AssertionError('A3 ground representation enumeration failed')
    c1 = su2_partitions(3)
    ci = sorted({item['Dynkin_index'] for item in c1})
    di = sorted({item['Dynkin_index'] for row in a3
                 for item in row['commuting_SU2_possibilities']})
    target = 5*constant-4  # level5 times6 minus the adjoint index4
    values = [{'c1_index':a,'d5_index':b,'nine_c1_minus_d5':9*a-b}
              for a in ci for b in di]
    feasible = [row for row in values if row['nine_c1_minus_d5'] == target]
    if ci != [0,1,4] or di != [0,1] or target != 26:
        raise AssertionError('Independent small-index controls failed')
    return {'exact_universal_identity': 'Q_vacuum_grade1/kappa +9 Q_c1_ground/kappa -Q_d5_ground/kappa =6',
        'functional_vanishes_on_complete_M2_basis':True,
        'universal_constant':str(constant), 'A3_d5_ground_representations':a3,
        'A1_c1_ground_representations':c1,'A1_c1_indices':ci,'A1_d5_indices':di,
        'required_nine_c1_minus_d5':int(target),'all_index_pairs':values,
        'feasible_pairs':feasible, 'simultaneous_A3_level1_A1_level5_excluded':not feasible,
        'scope': 'Conditional obstruction for a strongly regular unitary c8 VOA with actual Haagerup-center modular representation and gamma1 character, containing commuting A3_1 and A1_5 current factors. Uses selfcontragredience and positive affine/coset energies; no FS sign or retained commutant factor is assumed. Does not determine the chain continuum central charge.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=Path('hi_cft_third_flavoured_trace_results.json'))
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    limit = resource.getrlimit(resource.RLIMIT_AS)[0]
    if limit == resource.RLIM_INFINITY or limit > 128*1024**2:
        raise RuntimeError('Use the sole coordinated launcher with at most128MiB AS')
    input_path,output = args.input.resolve(),args.output.resolve()
    pending = output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists() or output == input_path:
        raise ValueError('Use a new .json output')
    if input_path.stat().st_size > 128*1024:
        raise ValueError('Exact input certificate exceeds128KiB')
    raw = input_path.read_bytes()
    saved = json.loads(raw)
    source = Path(__file__).resolve()
    producer = source.with_name('hi_cft_third_flavoured_trace_check.py')
    source_bytes,producer_bytes = source.read_bytes(),producer.read_bytes()
    if saved['source_sha256'] != sha(producer_bytes):
        raise ValueError('Original exact certificate producer hash mismatch')
    started = monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Ten-second exact algebra deadline')
    previous = signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,10)
    try:
        result = check(saved)
        result.update(input_record={'path':str(input_path),'sha256':sha(raw)},
            source_sha256=sha(source_bytes),original_producer_sha256=sha(producer_bytes),
            seconds=monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if input_path.read_bytes() != raw or source.read_bytes() != source_bytes or producer.read_bytes() != producer_bytes:
            raise RuntimeError('Input or source changed')
        with pending.open('x') as handle:
            json.dump(result,handle,indent=2,allow_nan=False)
            handle.write('\n')
        if output.exists():
            raise ValueError('Output appeared before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps({'output':str(output),'seconds':result['seconds'],
        'excluded':result['simultaneous_A3_level1_A1_level5_excluded']},indent=2))


if __name__ == '__main__':
    main()
