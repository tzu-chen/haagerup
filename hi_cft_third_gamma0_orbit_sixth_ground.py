"""All-ground support for the retained H+ orbit and all fourth/sixth moments.

ROOT-only128MiB. Pure stdlib, bounded partitions; no tensor calculations.
Resource exhaustion aborts and never certifies an exclusion. The actual
E8 embedding and forced diagonal affine simple-current extension are premises.
"""
import argparse
from collections import Counter,defaultdict
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_third_gamma0_sixth_check as sixth


old=sixth.old
NODE_CAP=1000000
BLOCK_CAP=10000
COMBINATION_CAP=1000000
OUTPUT_CAP=2000


def moments(rep):
    return old.moments(rep)+tuple(sixth.sixth(rep,p)*mult for p,mult in ((6,4),(4,2),(2,2),(0,4)))


def left_dimensions(k,target):
    d,t,_,_,s,_,u,*_=target
    if k==1:
        if s!=t or u!=t:return None
        result={1:d-2*t,2:t}
    elif k==3:
        a4=F(u-5*s+4*t,360)
        a3=F(s-t,12)-6*a4
        a2=t-4*a3-10*a4
        result={1:d-2*a2-3*a3-4*a4,2:a2,3:a3,4:a4}
    else:raise ValueError('Only left levels1/3 reviewed')
    if any(F(x).denominator!=1 or x<0 for x in result.values()):return None
    result={n:int(x) for n,x in result.items()}
    if any(x%2 for n,x in result.items() if n%2==0):return None
    return result


def orbit_shift(n,m,k,l):return F(k+l,4)-F(n+m-2,2)


def orbit_matches(rep,k,l):
    for (n,m),count in rep.items():
        shift=orbit_shift(n,m,k,l)
        if (n+m)%2 or shift<0:return False
        if shift==0 and rep.get((k+2-n,l+2-m),0)!=count:return False
    return True


def partitions(n,d,k,l,target,budget):
    ix=old.next_grade.index(n);fourth2=int(2*old.quartic.fourth(n))
    imax=target[2]//n;smax=target[5]//n;umax=target[9]//n
    if ix:imax=min(imax,target[3]//ix);smax=min(smax,target[8]//ix)
    if fourth2:imax=min(imax,target[7]//fourth2)
    fixed_index=None
    if k==1:fixed_index=target[3] if n==2 else target[2]-2*target[3]
    if fixed_index is not None and fixed_index<0:return []
    types=[]
    for m in range(min(l+1,d),0,-1):
        if (n+m)%2 or orbit_shift(n,m,k,l)<0:continue
        types.append((m,old.next_grade.index(m),int(2*old.quartic.fourth(m)),int(4*sixth.power_trace(m,6))))
    output=[]
    def visit(position,size,i,s,u,terms,boundary_count):
        budget['nodes']+=1
        if budget['nodes']>NODE_CAP:raise RuntimeError('Orbit-sixth DFS cap; no exclusion follows')
        if size>d or i>imax or s>smax or u>umax or fixed_index is not None and i>fixed_index:return
        if position==len(types):
            if size!=d or fixed_index is not None and i!=fixed_index:return
            if len(output)>=BLOCK_CAP:raise RuntimeError('Orbit-sixth block cap; no exclusion follows')
            output.append({'index':i,'twice_fourth':s,'four_times_sixth':u,'irreps':terms,'boundary_count':boundary_count})
            return
        m,im,sm,um=types[position];boundary=orbit_shift(n,m,k,l)==0
        for count in range((d-size)//m+1):
            visit(position+1,size+count*m,i+count*im,s+count*sm,u+count*um,
                terms+((m,count),) if count else terms,boundary_count+count if boundary else boundary_count)
    visit(0,0,0,0,0,(),0)
    return output


def solve_ground(k,l,name,target):
    if len(target)!=10 or any(F(x).denominator!=1 or x<0 for x in target):
        return {'name':name,'support_found':False,'reason':'Negative or nonintegral quantized moment target','target':target}
    target=tuple(int(x) for x in target);dimensions=left_dimensions(k,target)
    if dimensions is None:
        return {'name':name,'support_found':False,'reason':'No nonnegative integral local left-multiplicity dimensions','target':target}
    budget={'nodes':0,'combinations':0};blocks={n:partitions(n,d,k,l,target,budget) for n,d in dimensions.items()}
    # Matching a boundary orbit can depend on the representation even at
    # identical three moments. Retain this extra signature in the hash.
    ones=defaultdict(list)
    for b in blocks[1]:ones[b['index'],b['twice_fourth'],b['four_times_sixth'],b['boundary_count']].append(b)
    found=[]
    def check(chosen):
        budget['combinations']+=1
        if budget['combinations']>COMBINATION_CAP:raise RuntimeError('Orbit-sixth join cap; no exclusion follows')
        if sum(old.next_grade.index(n)*b['index'] for n,b in chosen.items())!=target[3]:return
        if sum(2*old.quartic.fourth(n)*b['index'] for n,b in chosen.items())!=target[7]:return
        if sum(old.next_grade.index(n)*b['twice_fourth'] for n,b in chosen.items())!=target[8]:return
        need=(target[2]-sum(n*b['index'] for n,b in chosen.items()),
              target[5]-sum(n*b['twice_fourth'] for n,b in chosen.items()),
              target[9]-sum(n*b['four_times_sixth'] for n,b in chosen.items()),
              chosen[k+1]['boundary_count'])
        for first in ones.get(need,[]):
            budget['combinations']+=1
            if budget['combinations']>COMBINATION_CAP:raise RuntimeError('Orbit-sixth full join cap; no exclusion follows')
            rep=Counter({(n,m):c for n,b in [(1,first),*chosen.items()] for m,c in b['irreps']})
            if not orbit_matches(rep,k,l):continue
            if moments(rep)!=target:raise AssertionError('Independent full ten-moment substitution failed')
            if len(found)>=OUTPUT_CAP:raise RuntimeError('Orbit-sixth output cap; no exclusion follows')
            found.append(old.describe(rep))
    if k==1:
        for b2 in blocks[2]:
            check({2:b2})
    else:
        # Two mixed sixth/quartic equations determine the required index
        # of blocks2/3 once block4 is chosen; the other mixed sixth moment
        # also fixes block2's fourth moment. This avoids a broad product.
        twos=defaultdict(list);threes=defaultdict(list)
        for b2 in blocks[2]:twos[b2['index'],b2['twice_fourth']].append(b2)
        for b3 in blocks[3]:threes[b3['index']].append(b3)
        for b4 in blocks[4]:
            i3=F(target[7]-target[3],12)-6*b4['index']
            i2=target[3]-4*i3-10*b4['index']
            if i3.denominator!=1 or i2.denominator!=1 or min(i3,i2)<0:continue
            for b3 in threes.get(int(i3),[]):
                s2=target[8]-4*b3['twice_fourth']-10*b4['twice_fourth']
                for b2 in twos.get((int(i2),s2),[]):
                    check({2:b2,3:b3,4:b4})
    return {'name':name,'target':target,'left_multiplicity_dimensions':dimensions,
        'support_found':bool(found),'support_count':len(found),'unique_support':len(found)==1,
        'all_support_witnesses':found,
        'block_counts':{n:len(b) for n,b in blocks.items()},'budget':budget,
        'scope':'Every feasible representation in this finite moment/orbit relaxation is retained; passing is not OPE existence. Resource caps abort rather than certify exclusion or uniqueness.'}


def calculate(quartic,m6):
    names=old.quartic.modular.NAMES;output=[]
    order=('d5','d6','c1','d1','d4','c2','d2','a','c0','b','d3')
    if len(quartic['surviving_levels'])!=2 or len(m6['rows'])!=2:raise ValueError('Both survivors required')
    for row in quartic['surviving_levels']:
        k,l=row['levels']
        if (k,l) not in old.P27 or len(row['witnesses'])!=1:raise ValueError('Unexpected survivor')
        match=[r for r in m6['rows'] if r['levels']==[k,l]]
        if len(match)!=1 or not match[0]['all_polarizations_consistent']:raise ValueError('Consistent sixth record required')
        polarizations={tuple(r['powers']):r for r in match[0]['polarizations']}
        if set(polarizations)!={(6,0),(4,2),(2,4),(0,6)}:raise ValueError('All four polarizations required')
        if any(not r['solution']['consistent'] or r['solution']['dimension']!=0 for r in polarizations.values()):
            raise ValueError('Sixth coefficients must be uniquely fixed')
        w=row['witnesses'][0];small=w['small_ground_witness']
        traces=old.quartic.support.all_trace_targets({name:(small[name]['left_Dynkin_index'],small[name]['right_Dynkin_index'])
            for name in ('c1','d1','d4')},k,l)
        rows=[];cache={};retained_count=0
        for name in order:
            fourth=[F(w['quartic_predictions'][kind]['predicted_leading_moments'][name]) for kind in ('mixed','left','right')]
            sixth_values=[]
            for powers,multiplier in (((6,0),4),((4,2),2),((2,4),2),((0,6),4)):
                item=polarizations[powers]['all_ground_moment_affine_forms'][name]
                if item['free_coefficients']:raise ValueError('Unexpected free sixth coefficient')
                sixth_values.append(multiplier*F(item['constant']))
            target=(int(old.quartic.modular.CHI[names.index(name)][0]),*traces[name],fourth[0],2*fourth[1],2*fourth[2],*sixth_values)
            if target in cache:
                answer=dict(cache[target]);answer.update(name=name,reused_identical_target=True)
            else:answer=solve_ground(k,l,name,target);cache[target]=answer
            retained_count+=answer.get('support_count',0)
            if retained_count>OUTPUT_CAP:raise RuntimeError('Orbit-sixth combined output cap; no exclusion follows')
            rows.append(answer)
        output.append({'levels':[k,l],'all_ground_supports_exist':all(r['support_found'] for r in rows),'grounds':rows})
    if {tuple(r['levels']) for r in output}!={(1,39),(3,13)}:raise ValueError('Duplicate survivor')
    return {'rows':output,'scope':'Necessary ten-moment finite support under the actual E8/unique W2 premises and retained bosonic affine H+ extension. No nonvacuum affine-energy positivity is assumed. Passing is not OPE or VOA existence.',
        'orbit_condition':'n+m even; Delta=(k+l)/4-(n+m-2)/2 >=0, with equal partner multiplicities at Delta=0.'}


def selftest():
    for k,l in ((1,39),(3,13)):
        rep=Counter({(1,5):1,(2,4):1})
        if not solve_ground(k,l,'local_d5',moments(rep))['support_found']:raise AssertionError('Known local d5 refused')
    paired=Counter({(1,9):1,(4,6):1})
    if not solve_ground(3,13,'paired_boundary',moments(paired))['support_found']:raise AssertionError('Matched boundary orbit refused')
    unpaired=Counter({(4,6):1})
    if solve_ground(3,13,'unpaired_boundary',moments(unpaired))['support_found']:raise AssertionError('Unmatched boundary orbit accepted')
    negative=Counter({(1,23):1})
    if solve_ground(1,39,'negative_shift',moments(negative))['support_found']:raise AssertionError('Negative orbit shift accepted')
    return {'known_d5_cases':2,'paired_boundary':True,'unpaired_boundary_refused':True,'negative_shift_refused':True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quartic',type=Path,required=True);p.add_argument('--sixth',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('ROOT coordinated128MiB launcher required')
    inputs=[args.quartic.resolve(),args.sixth.resolve()];out=args.output.resolve();pending=out.with_name(out.name+'.pending')
    if out.suffix!='.json' or out.exists() or pending.exists() or out in inputs:raise ValueError('Choose new noncolliding output')
    snapshots={}
    def load(path):
        if path.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
        raw=path.read_bytes()
        if len(raw)>2*1024**2:raise ValueError('Input grew beyond2MiB')
        snapshots[path]=raw;return json.loads(raw)
    quartic,m6=(load(path) for path in inputs)
    inputs_all=set(inputs)
    upstream=m6.get('input_records',[])
    if len(upstream)!=3:raise ValueError('Complete three-record sixth ancestry required')
    for record in upstream:
        path=Path(record['path']).resolve()
        if path==out:raise ValueError('Output collides with ancestor')
        if path not in snapshots:load(path)
        if hashlib.sha256(snapshots[path]).hexdigest()!=record['sha256']:raise ValueError('Sixth input ancestor changed')
        inputs_all.add(path)
    if str(inputs[0]) not in {r['path'] for r in upstream}:raise ValueError('Sixth record does not bind supplied quartic')
    bindings={}
    for data in (quartic,m6):
        for path,h in data.get('producer_source_hashes',{}).items():
            if path in bindings and bindings[path]!=h:raise ValueError('Producer versions disagree')
            bindings[path]=h
    if str(Path(sixth.__file__).resolve()) not in bindings:raise ValueError('Sixth producer missing')
    paths={Path(__file__).resolve(),Path(sixth.__file__).resolve(),*map(Path,bindings)}
    if out in paths:raise ValueError('Output collides with source')
    for path in paths:
        if path.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[path]=path.read_bytes()
        if len(snapshots[path])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(path):hashlib.sha256(raw).hexdigest() for path,raw in snapshots.items()}
    if any(hashes[path]!=h for path,h in bindings.items()):raise ValueError('Producer changed')
    def timeout(signum,frame):raise TimeoutError('Sixty-second orbit-sixth support cap')
    handler=signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,60);started=monotonic()
    try:
        result=calculate(quartic,m6)
        result.update(selftest=selftest(),input_records=[{'path':str(path),'sha256':hashes[str(path)]} for path in sorted(inputs_all)],
            producer_source_hashes={path:h for path,h in hashes.items() if Path(path) not in inputs_all},
            limits={'nodes_per_ground':NODE_CAP,'partitions_per_block':BLOCK_CAP,'joins_per_ground':COMBINATION_CAP,'representations_per_pair':OUTPUT_CAP},
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(path.read_bytes()!=raw for path,raw in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(old.quartic.support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if out.exists() or any(path.read_bytes()!=raw for path,raw in snapshots.items()):raise RuntimeError('Input/source/output changed')
        pending.replace(out)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,handler)
        if pending.exists():pending.unlink()
    print(json.dumps({'output':str(out),'rows':[{'levels':r['levels'],'pass':r['all_ground_supports_exist']} for r in result['rows']]}),flush=True)


if __name__=='__main__':main()
