"""Exact factored grade2 multiplicity enumeration; ROOT128MiB only.

The complete left dimension/quadratic/fourth moments are solved first.
Only small right-representation partitions remain. The original broad
DP and all its dependencies stay unchanged.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from math import gcd
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_third_gamma0_grade2_check as old


NODE_CAP=500000
BLOCK_SOLUTION_CAP=5000
COMBINATION_CAP=1000000
OUTPUT_CAP=2000


def allowed_caps(caps,k,l):
    return Counter({(n,m):count for (n,m),count in caps.items()
        if n<=k+1 and m<=l+1 and old.quartic.support.energy(n,m,k,l)<=2})


def left_dimensions(pair,target,caps):
    dimension,left,_,_,twice_fourth,_=target
    if pair==(1,39):
        if twice_fourth!=left:raise ValueError('Level-one left moment identity failed')
        candidates=[{1:dimension-2*left,2:left}]
    elif pair==(3,13):
        value=F(twice_fourth-left,12)
        if value.denominator!=1:raise ValueError('Left moment difference is not divisible by12')
        candidates=[]
        for a4 in range(dimension//4+1):
            a3=int(value)-6*a4
            a2=left-4*a3-10*a4
            a1=dimension-2*a2-3*a3-4*a4
            candidates.append({1:a1,2:a2,3:a3,4:a4})
    else:raise ValueError('Unreviewed pair')
    result=[]
    for values in candidates:
        if min(values.values())<0:continue
        good=True
        for n,total in values.items():
            sizes=[m for (a,m),count in caps.items() if a==n and count]
            divisor=0
            for m in sizes:divisor=gcd(divisor,m)
            capacity=sum(m*count for (a,m),count in caps.items() if a==n)
            if total>capacity or total and (not divisor or total%divisor):good=False
        if good:result.append(values)
    expected={(1,39):[{1:38,2:30}],(3,13):[{1:7,2:20,3:10,4:4}]}[pair]
    if result!=expected:raise AssertionError('Independent left-dimension reduction changed')
    return result


def right_partitions(n,dimension,caps,index_target,index_max,twice_fourth_max,budget):
    types=sorted([(m,count) for (a,m),count in caps.items() if a==n],reverse=True)
    result=[]
    def visit(position,d,ix,s4,terms):
        budget['nodes']+=1
        if budget['nodes']>NODE_CAP:raise RuntimeError('Factored partition node cap reached; no exclusion follows')
        if d>dimension or ix>index_max or s4>twice_fourth_max:return
        if index_target is not None and ix>index_target:return
        if position==len(types):
            if d!=dimension or index_target is not None and ix!=index_target:return
            if n==1 and dict(terms).get(1,0)<1:return
            if len(result)>=BLOCK_SOLUTION_CAP:raise RuntimeError('Block solution cap reached; no exclusion follows')
            result.append({'right_dimension':d,'right_index':ix,'twice_right_fourth':s4,
                'right_irreps':terms,'singlets':dict(terms).get(1,0) if n==1 else 0})
            return
        m,count=types[position]
        copies=2 if (n+m)%2 else 1
        maxcount=min(count,(dimension-d)//m)
        im=old.next_grade.index(m)
        sm=2*old.quartic.fourth(m)
        if sm.denominator!=1:raise AssertionError('Doubled fourth is not integral')
        for number in range(0,maxcount+1,copies):
            newterms=terms+((m,number),) if number else terms
            visit(position+1,d+number*m,ix+number*im,s4+number*int(sm),newterms)
    visit(0,0,0,0,())
    return result


def solve_pair(row):
    pair=tuple(row['levels'])
    k,l=pair
    if row['failures']:raise ValueError('Moment-only input already fails a necessary test')
    target=tuple(row['remaining_affine_primary_moments'])
    if len(target)!=6 or any(type(v) is not int or v<0 for v in target):raise ValueError('Invalid exact moment target')
    _,_,_,caps0=old.ambient(k,l)
    if old.describe(caps0)!=row['ambient_affine_primary_caps']:raise ValueError('Saved actual ambient caps differ')
    caps=allowed_caps(caps0,k,l)
    dimensions=left_dimensions(pair,target,caps)
    budget={'nodes':0,'combinations':0}
    answers=[]
    block_records=[]
    for split in dimensions:
        blocks={}
        for n,d in split.items():
            index_target=None
            if pair==(1,39):index_target=target[3] if n==2 else target[2]-2*target[3]
            maximum=target[2]//n
            il=old.next_grade.index(n)
            if il:maximum=min(maximum,target[3]//il)
            blocks[n]=right_partitions(n,d,caps,index_target,maximum,target[5]//n,budget)
        block_records.append({'left_dimensions':split,
            'block_solution_counts':{n:len(value) for n,value in blocks.items()},
            'block_solutions':blocks})
        keys=sorted(blocks)
        combination_count=1
        for values in blocks.values():combination_count*=len(values)
        if combination_count+budget['combinations']>COMBINATION_CAP:
            raise RuntimeError('Factored combination cap reached; no exclusion follows')
        for choices in product(*(blocks[n] for n in keys)):
            budget['combinations']+=1
            if sum(n*b['right_index'] for n,b in zip(keys,choices))!=target[2]:continue
            if sum(old.next_grade.index(n)*b['right_index'] for n,b in zip(keys,choices))!=target[3]:continue
            if sum(n*b['twice_right_fourth'] for n,b in zip(keys,choices))!=target[5]:continue
            rep=Counter({(n,m):count for n,block in zip(keys,choices) for m,count in block['right_irreps']})
            if old.moments(rep)!=target or any(rep[p]>caps[p] for p in rep):
                raise AssertionError('Independent combined support check failed')
            if len(answers)>=OUTPUT_CAP:raise RuntimeError('Output decomposition cap reached; no exclusion follows')
            answers.append({'affine_primary_irreps':old.describe(rep),
                'commutant_weight2_singlets':rep.get((1,1),0),'moments':old.moments(rep)})
    return {'levels':list(pair),'target':target,'left_dimension_solutions':dimensions,
        'right_block_enumerations':block_records,'all_feasible_decompositions':answers,
        'feasible_decomposition_count':len(answers),
        'possible_commutant_weight2_dimensions':sorted({r['commutant_weight2_singlets'] for r in answers}),
        'budget':budget,'scope':'All finite affine-primary decompositions obeying the exact moments, actual ambient caps, integrability and unitary-vacuum affine-energy bound. These remain necessary representation conditions, not OPE existence.'}


def selftest():
    budget={'nodes':0}
    caps=Counter({(2,14):3,(2,12):3,(2,10):5,(2,8):7,(2,6):8,(2,4):5,(2,2):4})
    rows=right_partitions(2,30,caps,575,575,161374//2,budget)
    expected={((14,1),(8,1),(6,1),(2,1)),((12,2),(2,3))}
    if {row['right_irreps'] for row in rows}!=expected:
        raise AssertionError('Independent host125 doublet partition control failed')
    # Test both parity pairing and mandatory-singlet refusal on tiny domains.
    paired=right_partitions(1,5,Counter({(1,2):2,(1,1):1}),2,2,2,{'nodes':0})
    if len(paired)!=1:raise AssertionError('Paired quaternionic control failed')
    refused=right_partitions(1,3,Counter({(1,3):1}),4,4,16,{'nodes':0})
    if refused:raise AssertionError('Mandatory coset stress refusal failed')
    return {'hand_doublet_partitions_checked':True,'parity_control':True,'mandatory_singlet_control':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('Use ROOT coordinated128MiB launcher')
    inp,out=args.input.resolve(),args.output.resolve();pending=out.with_name(out.name+'.pending')
    if out.suffix!='.json' or out.exists() or pending.exists() or out==inp:raise ValueError('Choose new noncolliding.json output')
    if inp.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
    raw=inp.read_bytes()
    if len(raw)>2*1024**2:raise ValueError('Input grew beyond2MiB')
    data=json.loads(raw)
    bindings=data.get('producer_source_hashes',{})
    if str(Path(old.__file__).resolve()) not in bindings:raise ValueError('Bound moment producer missing')
    paths={Path(__file__).resolve(),Path(old.__file__).resolve(),*map(Path,bindings)}
    if out in paths:raise ValueError('Output collides with source')
    snapshots={inp:raw}
    for path in paths:
        if path.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[path]=path.read_bytes()
        if len(snapshots[path])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(p):hashlib.sha256(v).hexdigest() for p,v in snapshots.items()}
    if any(hashes[p]!=h for p,h in bindings.items()):raise ValueError('A bound producer changed')
    if len(data['rows'])!=2 or {tuple(r['levels']) for r in data['rows']}!={(1,39),(3,13)}:
        raise ValueError('Require both exact moment-only rows')
    started=monotonic()
    def timeout(signum,frame):raise TimeoutError('Sixty-second factored certificate cap')
    previous=signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,60)
    try:
        rows=[solve_pair(row) for row in data['rows']]
        result={'rows':rows,'selftest':selftest(),'input_record':{'path':str(inp),'sha256':hashes[str(inp)]},
            'producer_source_hashes':{p:h for p,h in hashes.items() if p!=str(inp)},
            'limits':{'DFS_nodes':NODE_CAP,'block_solutions':BLOCK_SOLUTION_CAP,'combinations':COMBINATION_CAP,'output_decompositions':OUTPUT_CAP},
            'seconds':monotonic()-started,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'additional_embedding_premise':data['additional_premise']}
        if any(p.read_bytes()!=v for p,v in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(old.quartic.support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if out.exists() or any(p.read_bytes()!=v for p,v in snapshots.items()):raise RuntimeError('Input/source/output changed')
        pending.replace(out)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous)
        if pending.exists():pending.unlink()
    print(json.dumps({'output':str(out),'seconds':result['seconds'],'counts':[
        {'levels':r['levels'],'decompositions':r['feasible_decomposition_count'],'singlets':r['possible_commutant_weight2_dimensions']} for r in rows]}),flush=True)


if __name__=='__main__':main()
