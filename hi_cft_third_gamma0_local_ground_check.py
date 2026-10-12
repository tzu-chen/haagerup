"""Conditional diagonal-simple-current locality support for all grounds.

Pure stdlib, ROOT128MiB only. Additional premise: the bosonic extension
of A1_k times A1_l by its(k,l) simple current is a VOA subalgebra of W.
All W modules must then have n+m even. This is stronger than pairing
quaternionic representations; no nonvacuum energy assumption is added.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_third_gamma0_grade2_check as previous


NODE_CAP=1000000
BLOCK_CAP=10000
COMBINATION_CAP=1000000


def splits(k,target):
    d,t,_,_,s,_=target
    if k==1:
        candidates=[{1:d-2*t,2:t}] if s==t else []
    elif k==3:
        u=F(s-t,12)
        if u.denominator!=1:return []
        candidates=[]
        for a4 in range(d//4+1):
            a3=int(u)-6*a4;a2=t-4*a3-10*a4;a1=d-2*a2-3*a3-4*a4
            candidates.append({1:a1,2:a2,3:a3,4:a4})
    else:raise ValueError('Only left levels1/3 reviewed')
    return [a for a in candidates if min(a.values())>=0 and all(a[n]%2==0 for n in a if n%2==0)]


def partitions(n,d,k,l,height,use_energy,imax,smax,budget,itarget=None):
    types=[m for m in range(1,min(l+1,d)+1) if (n+m)%2==0 and
        (not use_energy or previous.quartic.support.energy(n,m,k,l)<=height)]
    types.reverse()
    output=[]
    def visit(position,size,ix,twice_s,terms):
        budget['nodes']+=1
        if budget['nodes']>NODE_CAP:raise RuntimeError('Local-ground DFS node cap; no exclusion follows')
        if size>d or ix>imax or twice_s>smax or itarget is not None and ix>itarget:return
        if position==len(types):
            if size!=d or itarget is not None and ix!=itarget:return
            if len(output)>=BLOCK_CAP:raise RuntimeError('Local-ground block cap; no exclusion follows')
            output.append({'dimension':size,'index':ix,'twice_fourth':twice_s,'irreps':terms})
            return
        m=types[position];im=previous.next_grade.index(m);sm=int(2*previous.quartic.fourth(m))
        for count in range((d-size)//m+1):
            visit(position+1,size+count*m,ix+count*im,twice_s+count*sm,
                terms+((m,count),) if count else terms)
    visit(0,0,0,0,())
    return output


def solve_ground(k,l,name,target,height,use_energy):
    if any(type(x) is not int or x<0 for x in target):raise ValueError('Invalid six-moment ground target')
    budget={'nodes':0,'combinations':0}
    attempts=[]
    found=None
    for dimensions in splits(k,target):
        blocks={}
        for n,d in dimensions.items():
            imax=target[2]//n
            left_index=previous.next_grade.index(n)
            if left_index:imax=min(imax,target[3]//left_index)
            itarget=None
            if k==1:itarget=target[3] if n==2 else target[2]-2*target[3]
            if itarget is not None and itarget<0:blocks[n]=[];continue
            blocks[n]=partitions(n,d,k,l,height,use_energy,imax,target[5]//n,budget,itarget)
        attempts.append({'left_dimensions':dimensions,'block_counts':{n:len(b) for n,b in blocks.items()}})
        # The n=1 block affects neither left moments nor the mixed moment.
        # Hash its two remaining moments instead of a large Cartesian product.
        index1={}
        for b in blocks[1]:index1.setdefault((b['index'],b['twice_fourth']),b)
        keys=sorted(n for n in blocks if n!=1)
        count=1
        for n in keys:count*=len(blocks[n])
        if budget['combinations']+count>COMBINATION_CAP:raise RuntimeError('Local-ground combination cap; no exclusion follows')
        for chosen in product(*(blocks[n] for n in keys)):
            budget['combinations']+=1
            if sum(previous.next_grade.index(n)*b['index'] for n,b in zip(keys,chosen))!=target[3]:continue
            needed=(target[2]-sum(n*b['index'] for n,b in zip(keys,chosen)),
                    target[5]-sum(n*b['twice_fourth'] for n,b in zip(keys,chosen)))
            first=index1.get(needed)
            if first is None:continue
            rep=Counter({(n,m):c for n,b in [(1,first),*zip(keys,chosen)] for m,c in b['irreps']})
            if previous.moments(rep)!=tuple(target) or any((n+m)%2 for n,m in rep):
                raise AssertionError('Local support witness failed full independent substitution')
            found=previous.describe(rep)
            break
        if found is not None:break
    return {'name':name,'ground_weight':height,'target':target,'support_found':found is not None,
        'support_witness':found,'attempts':attempts,'budget':budget,
        'scope':'One witness proves support only; all left splits and bounded right partitions are exhausted before a refusal.'}


def run(data,use_energy=False):
    results=[]
    names=previous.quartic.modular.NAMES
    dimensions={name:int(previous.quartic.modular.CHI[i][0]) for i,name in enumerate(names)}
    order=('d5','d6','c1','d1','d4','c2','d2','a','c0','b','d3')
    for row in data['surviving_levels']:
        k,l=row['levels']
        if (k,l) not in ((1,39),(3,13)) or len(row['witnesses'])!=1:raise ValueError('Unexpected quartic survivor')
        w=row['witnesses'][0];small=w['small_ground_witness']
        traces=previous.quartic.support.all_trace_targets({name:(small[name]['left_Dynkin_index'],small[name]['right_Dynkin_index'])
            for name in ('c1','d1','d4')},k,l)
        grounds=[];cache={}
        for name in order:
            moments=[F(w['quartic_predictions'][kind]['predicted_leading_moments'][name]) for kind in ('mixed','left','right')]
            target=(dimensions[name],*traces[name],moments[0],2*moments[1],2*moments[2])
            if any(F(x).denominator!=1 for x in target):raise ValueError('Predicted doubled moments must be integral')
            target=tuple(int(x) for x in target)
            height=previous.quartic.modular.LAMBDA[names.index(name)]+F(1,3)
            key=(target,height if use_energy else None)
            if key in cache:
                result=dict(cache[key]);result.update(name=name,ground_weight=height,reused_identical_target=True)
            else:
                result=solve_ground(k,l,name,target,height,use_energy);cache[key]=result
            grounds.append(result)
        results.append({'levels':[k,l],'all_ground_supports_exist':all(g['support_found'] for g in grounds),'grounds':grounds})
    if len(results)!=2 or {tuple(r['levels']) for r in results}!={(1,39),(3,13)}:raise ValueError('Both distinct quartic survivors required')
    return {'rows':results,'diagonal_simple_current_extension_premise':True,
        'locality_condition':'Every affine ground irrep has n+m even; odd types are forbidden, not merely paired.',
        'additional_affine_energy_filter':use_energy,
        'energy_premise':'Unitary nonvacuum W modules or nonnegative affine-commutant ground energy' if use_energy else None,
        'scope':'Necessary finite representation support under the stated S-extension premise; neither the extension premise nor VOA existence is proved by this arithmetic certificate.'}


def selftest():
    # The known local d5 ground is(1,5)+(2,4) for both pairs.
    known=Counter({(1,5):1,(2,4):1});target=previous.moments(known)
    for k,l in ((1,39),(3,13)):
        got=solve_ground(k,l,'control',target,F(7,13),False)
        if not got['support_found']:raise AssertionError('Known local d5 representation refused')
    # A2D left-doublet/right-singlet ground cannot be local, although
    # an unconstrained affine module at the same levels exists.
    refused=solve_ground(1,39,'charged_control',(2,1,0,0,1,0),F(1),False)
    if refused['support_found']:raise AssertionError('Nonlocal type was accepted')
    return {'local_d5_controls':2,'nonlocal_refusal':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--affine-energy',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('Use ROOT coordinated128MiB launcher')
    inp,out=args.input.resolve(),args.output.resolve();pending=out.with_name(out.name+'.pending')
    if out.suffix!='.json' or out.exists() or pending.exists() or out==inp:raise ValueError('Choose new noncolliding.json output')
    if inp.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
    raw=inp.read_bytes()
    if len(raw)>2*1024**2:raise ValueError('Input grew beyond2MiB')
    data=json.loads(raw);bindings=data.get('producer_source_hashes',{})
    if str(Path(previous.quartic.__file__).resolve()) not in bindings:raise ValueError('Quartic producer missing')
    paths={Path(__file__).resolve(),Path(previous.__file__).resolve(),Path(previous.next_grade.__file__).resolve(),*map(Path,bindings)}
    if out in paths:raise ValueError('Output collides with source')
    snapshots={inp:raw}
    for p in paths:
        if p.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[p]=p.read_bytes()
        if len(snapshots[p])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(p):hashlib.sha256(v).hexdigest() for p,v in snapshots.items()}
    if any(hashes[p]!=h for p,h in bindings.items()):raise ValueError('Upstream producer changed')
    started=monotonic()
    def timeout(signum,frame):raise TimeoutError('Sixty-second local-ground certificate cap')
    previous_handler=signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,60)
    try:
        result=run(data,args.affine_energy)
        result.update(selftest=selftest(),input_record={'path':str(inp),'sha256':hashes[str(inp)]},
            producer_source_hashes={p:h for p,h in hashes.items() if p!=str(inp)},
            limits={'nodes_per_ground':NODE_CAP,'solutions_per_block':BLOCK_CAP,'combined_nontrivial_blocks':COMBINATION_CAP},
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(p.read_bytes()!=v for p,v in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(previous.quartic.support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if out.exists() or any(p.read_bytes()!=v for p,v in snapshots.items()):raise RuntimeError('Input/source/output changed')
        pending.replace(out)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous_handler)
        if pending.exists():pending.unlink()
    print(json.dumps({'output':str(out),'seconds':result['seconds'],'all_supports':[
        {'levels':r['levels'],'pass':r['all_ground_supports_exist']} for r in result['rows']]}),flush=True)


if __name__=='__main__':main()
