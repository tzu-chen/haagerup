"""Exact necessary gamma0 A1_k plus U1^3 ground-charge bounds.

No tensor or numerical linear algebra. Root alone may run this under128MiB.
The energy-capacity stage explicitly assumes nonnegative joint affine/coset
energy on the irreducible modules; the charge-rank stage does not use it.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic


GROUND = ((3, F(1,3), 9), (7, F(6,13), 1), (5, F(5,13), 3))


def partitions(total, maximum=None):
    if total == 0:
        yield ()
        return
    for first in range(min(total, maximum or total), 0, -1):
        for tail in partitions(total-first, first):
            yield (first,)+tail


def index(partition):
    return sum(n*(n*n-1)//6 for n in partition)


def pairs(partition):
    return sum(m//2 for m in Counter(partition).values())


def energy_data(partition, level, weight, coefficient):
    gaps = {n:weight-F(n*n-1, 4*(level+2)) for n in set(partition)}
    allowed = all(n <= level+1 and gap >= 0 for n,gap in gaps.items())
    positive_pairs = sum(m//2 for n,m in Counter(partition).items() if gaps[n] > 0)
    capacity = sum((4*coefficient*n*(m//2)*gaps[n]
                    for n,m in Counter(partition).items()), F(0))
    return allowed, positive_pairs, capacity


def check():
    choices = [list(partitions(dimension)) for dimension,_,_ in GROUND]
    if list(map(len,choices)) != [3,15,7]:
        raise AssertionError('Integer-partition exhaustion control failed')
    if [max(map(index,c)) for c in choices] != [4,56,20]:
        raise AssertionError('Finite SU2 index maximum control failed')
    levels = []
    for level in range(1,40):
        trace_count = rank_count = energy_count = 0
        witnesses = []
        best_capacity = None
        for c in choices[0]:
            for d1 in choices[1]:
                for d4 in choices[2]:
                    selected = (c,d1,d4)
                    if 4+sum(weight*index(p) for p,(_,_,weight) in zip(selected,GROUND)) != 4*level:
                        continue
                    trace_count += 1
                    rank_upper = sum(map(pairs,selected))
                    if rank_upper < 3:
                        continue
                    rank_count += 1
                    data = [energy_data(p,level,h,w) for p,(_,h,w) in zip(selected,GROUND)]
                    if not all(item[0] for item in data):
                        continue
                    energy_count += 1
                    capacity = sum((item[2] for item in data),F(0))
                    best_capacity = capacity if best_capacity is None else max(best_capacity,capacity)
                    if sum(item[1] for item in data) < 3 or capacity < 12:
                        continue
                    witnesses.append({'c1_SU2_dimensions':c,'d1_SU2_dimensions':d1,
                        'd4_SU2_dimensions':d4,'Dynkin_indices':list(map(index,selected)),
                        'charge_pair_rank_upper_bound':rank_upper,
                        'positive_energy_charge_pairs':sum(item[1] for item in data),
                        'weighted_charge_covariance_trace_capacity':capacity})
        levels.append({'level':level,'trace_partition_count':trace_count,
            'trace_and_rank_partition_count':rank_count,
            'trace_rank_and_affine_energy_partition_count':energy_count,
            'maximum_capacity_after_trace_rank_energy':best_capacity,
            'remaining_witnesses':witnesses})
    return {'ground_dimensions_weights_coefficients':GROUND,
        'partition_counts':list(map(len,choices)),
        'universal_trace_identity':'4+9 t_c1+t_d1+3 t_d4=4k',
        'radical_identity':'9 Q_c1+Q_d1+3 Q_d4=4 kappa on U1^3',
        'required_radical_covariance_trace':12,
        'universal_level_bound':39,
        'levels_surviving_trace_only':[r['level'] for r in levels if r['trace_partition_count']],
        'levels_surviving_trace_and_charge_rank':[r['level'] for r in levels if r['trace_and_rank_partition_count']],
        'levels_surviving_all_necessary_tests':[r['level'] for r in levels if r['remaining_witnesses']],
        'levels':levels,
        'scope':'Necessary conditions only for gamma0 W1=A1_k plus three abelian currents. Rank uses selfcontragredient charge pairing. Energy capacity additionally assumes unitary irreducible modules or nonnegative joint affine/Heisenberg commutant energy. Passing does not construct charges, a VOA, an E8 embedding or a chain continuum limit.'}


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {k:encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap == resource.RLIM_INFINITY or cap > 128*1024**2:
        raise RuntimeError('Use the sole root-coordinated launcher at128MiB AS or less')
    output=args.output.resolve()
    pending=output.with_name(output.name+'.pending')
    if output.suffix != '.json' or output.exists() or pending.exists():
        raise ValueError('Use a new .json output')
    source=Path(__file__).resolve()
    raw=source.read_bytes()
    started=monotonic()
    def timeout(signum,frame):
        raise TimeoutError('Thirty-second exact enumeration bound')
    previous=signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,30)
    try:
        result=check()
        result.update(source_sha256=hashlib.sha256(raw).hexdigest(),
            seconds=monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if source.read_bytes() != raw:
            raise RuntimeError('Source changed during bounded enumeration')
        with pending.open('x') as handle:
            json.dump(encode(result),handle,indent=2,allow_nan=False)
            handle.write('\n')
        if output.exists() or source.read_bytes() != raw:
            raise RuntimeError('Output or source changed before promotion')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,previous)
        if pending.exists():
            pending.unlink()
    print(json.dumps({'output':str(output),'seconds':result['seconds'],
        'rank_survivors':result['levels_surviving_trace_and_charge_rank'],
        'energy_survivors':result['levels_surviving_all_necessary_tests']}))


if __name__ == '__main__':
    main()
