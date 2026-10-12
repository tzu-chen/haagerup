"""Bounded actual-E8 grade2 support test after the gamma0 quartic filter.

ROOT-only128MiB exact arithmetic. The embedding premise is additional to
the global quartic certificate. A capped support search never turns an
unfinished computation into an exclusion.
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

import hi_cft_third_gamma0_quartic_check as quartic
import hi_cft_third_gamma0_next_grade as next_grade


CAP=20000
P27={
    (1,39):Counter({(2,6):1,(1,9):1,(1,5):1,(1,1):1}),
    (3,13):Counter({(3,3):1,(2,4):1,(2,2):1,(1,5):1,(1,1):1})}
B80={
    (1,39):Counter({(1,3):1,(1,5):2,(1,7):1,(1,9):1,(1,11):1,(2,4):1,(2,6):1,(2,10):1}),
    (3,13):Counter({(1,3):2,(1,5):2,(4,2):1,(3,3):1,(3,5):1,(2,2):1,(2,4):2,(2,6):1})}


def tensor(left,right):
    result=Counter()
    for (n,m),a in left.items():
        for (p,q),b in right.items():
            for x in range(abs(n-p)+1,n+p,2):
                for y in range(abs(m-q)+1,m+q,2):result[x,y]+=a*b
    return result


def moments(rep):
    value=[F(0)]*6
    for (n,m),count in rep.items():
        term=(n*m,m*next_grade.index(n),n*next_grade.index(m),
            next_grade.index(n)*next_grade.index(m),
            2*m*quartic.fourth(n),2*n*quartic.fourth(m))
        value=[a+count*b for a,b in zip(value,term)]
    if any(x.denominator!=1 for x in value):raise AssertionError('Doubled moments must be integral')
    return tuple(int(x) for x in value)


def describe(rep):
    return [{'left_dimension':n,'right_dimension':m,'multiplicity':count}
            for (n,m),count in sorted(rep.items()) if count]


def subtract(left,right):
    result=Counter(left)
    result.subtract(right)
    if any(count<0 for count in result.values()):raise ValueError('Required subrepresentation exceeds ambient multiplicity')
    return +result


def first_affine_descendants(ground,k,l):
    generated=tensor(Counter({(3,1):1,(1,3):1}),ground)
    nulls=Counter()
    for (n,m),count in ground.items():
        if n==k+1:nulls[n+2,m]+=count
        if m==l+1:nulls[n,m+2]+=count
    return subtract(generated,nulls)


def ambient(k,l):
    pair=(k,l)
    if pair not in P27:raise ValueError('Only the independently identified125/187 embeddings are reviewed')
    currents=Counter({(3,1):1,(1,3):1})
    a8=Counter({(1,3):1,(1,5):1})
    e78=subtract(B80[pair]+currents,a8)
    p=P27[pair]
    if moments(p)[0]!=27 or moments(e78)[0]!=78 or moments(a8)[0]!=8 or moments(B80[pair])[0]!=80:
        raise AssertionError('Actual ground branching dimensions failed')
    b2=tensor(p,p)+tensor(e78,a8)+Counter({(1,1):1})+a8+a8
    if moments(b2)[0]!=1370:raise AssertionError('Actual B2 dimension is not W2+b_grade1=1370')
    affine=Counter({(3,1):1,(1,3):1,(1,1):2,(3,3):1})
    if k!=1:affine[5,1]+=1
    if l!=1:affine[1,5]+=1
    expected=(27-5*(k==1)-5*(l==1),36-20*(k==1),36-20*(l==1),16,
              2*(168-136*(k==1)),2*(168-136*(l==1)))
    if moments(affine)!=expected:raise AssertionError('Affine vacuum grade2 moments disagree with PBW')
    bdesc=first_affine_descendants(B80[pair],k,l)
    if moments(bdesc)[0]!={(1,39):400,(3,13):468}[pair]:
        raise AssertionError('Independent b affine-descendant dimension failed')
    caps=subtract(subtract(b2,affine),bdesc)
    if caps.get((1,1),0)!={(1,39):4,(3,13):5}[pair]:
        raise AssertionError('Independent ambient commutant weight2 dimension failed')
    return b2,affine,bdesc,caps


def next_moments(k,l,witness):
    small=witness['small_ground_witness']
    a,b,c=(small[name] for name in ('c1','d1','d4'))
    forms=next_grade.coefficient_forms()
    tnext=[next_grade.evaluate(forms['next_forms']['0'],level,
        a[side+'_Dynkin_index'],b[side+'_Dynkin_index'],c[side+'_Dynkin_index'])
        for level,side in ((k,'left'),(l,'right'))]
    # Vacuum grade2 coefficients, independently retaining polar cross terms.
    d2=F(5,3)*F(3,2)*120+4*F(2,3)*6+12*F(-1,3)
    e22=120-48*6+432
    if d2!=312 or e22!=264:raise AssertionError('Vacuum grade2 modular constants failed')
    cert=quartic.coefficient_certificate()
    values=[]
    records={}
    for kind in ('mixed','left','right'):
        saved=witness['quartic_predictions'][kind]
        coefficients=list(map(F,saved['holomorphic_M4_coefficients']))
        v=[sum((coefficients[j]*cert['basis'][j][i] for j in range(3)),F(0)) for i in range(12)]
        hnext=sum((quartic.modular.CHI[0][j]*v[j] for j in range(12)),F(0))-504*v[0]
        if kind=='mixed':
            part=F(k*l,24)*d2+F(k,12)*(tnext[1]-96)+F(l,12)*(tnext[0]-96)-F(k*l,144)*e22
        else:
            side=0 if kind=='left' else 1
            level=(k,l)[side]
            part=F(level*level,8)*d2+F(level,2)*(tnext[side]-96)-F(level*level,48)*e22
        values.append(part+hnext)
        records[kind]={'particular':part,'holomorphic_next':hnext,'total':part+hnext}
    target=(F(120),*tnext,values[0],2*values[1],2*values[2])
    if any(x<0 or x.denominator!=1 for x in target):raise ValueError('Predicted grade2 moments are not nonnegative integral')
    return tuple(int(x) for x in target),records


def support_search(caps,target,k,l,node_cap=CAP):
    """Bounded finite multiplicities; at most node_cap generated DP nodes."""
    if len(target)!=6 or any(type(x) is not int or x<0 for x in target):raise ValueError('Invalid six-moment target')
    # Mandatory nonzero coset stress has positive remaining central charge.
    if caps.get((1,1),0)<1 or target[0]<1:return None,{'reason':'no room for required coset stress'}
    caps=Counter(caps)
    caps[1,1]-=1
    target=(target[0]-1,*target[1:])
    # For every SU2 irrep, twiceS-I=n(n²-1)(n²-4)/10>=0.
    # These additional nonnegative coordinates safely tighten pruning.
    differences=(target[4]-target[1],target[5]-target[2])
    if min(differences)<0:return None,{'reason':'negative twice-fourth minus quadratic index'}
    types=[]
    for (n,m),count in sorted(caps.items()):
        if not count or n>k+1 or m>l+1:continue
        if quartic.support.energy(n,m,k,l)>2:continue
        copies=2 if (n+m)%2 else 1
        count//=copies
        if count:types.append((n,m,copies,count))
    # Bit j records existence with j additional affine-primary singlets.
    # Keep all attainable counts when different decompositions merge.
    dp={(0,0,0,0,0,0):(None,1)}
    generated=1
    for n,m,copies,limit in types:
        increment=moments(Counter({(n,m):copies}))
        updated=dict(dp)
        for state,(node,singlets) in dp.items():
            for count in range(1,limit+1):
                new=tuple(a+count*b for a,b in zip(state,increment))
                if any(a>b for a,b in zip(new,target)):break
                if new[4]-new[1]>differences[0] or new[5]-new[2]>differences[1]:break
                mask=singlets << (count*copies if (n,m)==(1,1) else 0)
                if new not in updated:
                    generated+=1
                    if generated>node_cap:raise RuntimeError('Grade2 DP resource cap reached; no exclusion follows')
                    updated[new]=((node,n,m,count*copies),mask)
                else:
                    saved_node,saved_mask=updated[new]
                    updated[new]=(saved_node,saved_mask|mask)
        dp=updated
    if target not in dp:return None,{'generated_nodes':generated,'final_states':len(dp),'types':len(types),'node_cap':node_cap}
    rep=Counter({(1,1):1})
    node,mask=dp[target]
    while node is not None:
        node,n,m,count=node
        rep[n,m]+=count
    original_target=(target[0]+1,*target[1:])
    if moments(rep)!=original_target:raise AssertionError('Returned grade2 support witness failed moment check')
    if any(rep[p]>caps[p]+(p==(1,1)) for p in rep):raise AssertionError('Returned grade2 support exceeds ambient')
    return describe(rep),{'generated_nodes':generated,'final_states':len(dp),'types':len(types),'node_cap':node_cap,
        'possible_affine_primary_singlet_multiplicities':[j+1 for j in range(target[0]+1) if mask & (1<<j)],
        'singlet_scope':'All counts allowed by this finite-moment/ambient-multiplicity relaxation. Affine-vacuum singlets are already subtracted; any actual commutant weight2 dimension must belong to this set.'}


def run(data,search=False):
    rows=data['surviving_levels']
    if len(rows)>2 or any(tuple(row['levels']) not in P27 for row in rows):raise ValueError('Expected at most the two audited quartic survivors')
    result=[]
    for row in rows:
        k,l=row['levels']
        if len(row['witnesses'])!=1:raise ValueError('Reviewed surviving embeddings have one small-ground witness each')
        w=row['witnesses'][0]
        target,next_record=next_moments(k,l,w)
        b2,affine,bdesc,caps=ambient(k,l)
        bm=moments(B80[k,l])
        predicted=(80,*quartic.support.all_trace_targets({name:(w['small_ground_witness'][name]['left_Dynkin_index'],
            w['small_ground_witness'][name]['right_Dynkin_index']) for name in ('c1','d1','d4')},k,l)['b'],
            F(w['quartic_predictions']['mixed']['predicted_leading_moments']['b']),
            2*F(w['quartic_predictions']['left']['predicted_leading_moments']['b']),
            2*F(w['quartic_predictions']['right']['predicted_leading_moments']['b']))
        if bm!=predicted:raise AssertionError('Actual btop fails independently predicted quadratic/quartic moments')
        mandatory=moments(affine)
        remaining=tuple(a-b for a,b in zip(target,mandatory))
        failures=[]
        if any(x<0 for x in remaining):failures.append('negative affine-primary remaining moment')
        if remaining[0]*remaining[4]<2*remaining[1]**2 or remaining[0]*remaining[5]<2*remaining[2]**2:
            failures.append('affine-primary one-axis moment Cauchy inequality')
        if remaining[4]*remaining[5]<4*remaining[3]**2:
            failures.append('affine-primary mixed moment Cauchy inequality')
        if any(a>b for a,b in zip(target,moments(b2))):failures.append('W2 moment exceeds actual B2')
        found,stats=None,None
        if search and not failures:
            found,stats=support_search(caps,remaining,k,l)
            if found is None:failures.append('no bounded ambient affine-primary representation has the required moments')
        result.append({'levels':[k,l],'b_ground_actual_moments':bm,'b_ground_prediction_agrees':True,
            'vacuum_grade2_moments':target,'quartic_next_contributions':next_record,
            'affine_vacuum_grade2_moments':mandatory,'remaining_affine_primary_moments':remaining,
            'ambient_B2_moments':moments(b2),'ambient_B2_irreps':describe(b2),
            'b_ground_affine_descendant_moments':moments(bdesc),
            'b_ground_affine_descendants':describe(bdesc),
            'ambient_affine_primary_caps':describe(caps),'support_search_applied':search,
            'support_witness':found,'support_statistics':stats,'failures':failures})
    return {'moment_order':['dimension','left_index','right_index','mixed','twice_left_fourth','twice_right_fourth'],
        'rows':result,'additional_premise':'Actual E8 extension B=E6_1 times A2_1 with B|W=0 plus b, and the independently identified host125/187 branching.',
        'scope':'Necessary finite grade2 subrepresentation and moment tests. Passing supplies no VOA or OPE. The affine-primary energy bound uses unitarity of the vacuum VOA only, not unitary nonvacuum modules. Resource exhaustion yields no exclusion.'}


def selftest():
    for pair in P27:ambient(*pair)
    for n in range(1,6):
        for m in range(1,6):
            if moments(tensor(Counter({(n,1):1}),Counter({(m,1):1})))[0]!=n*m:
                raise AssertionError('Clebsch-Gordan dimension control failed')
    known,stats=support_search(Counter({(1,1):1,(2,2):1}),(5,2,2,1,2,2),1,1)
    if known is None:raise AssertionError('Known singlet plus(2,2) support refused')
    if stats['possible_affine_primary_singlet_multiplicities']!=[1]:raise AssertionError('Singlet support bitset failed')
    absent,_=support_search(Counter({(1,1):1,(2,2):1}),(5,2,2,0,2,2),1,1)
    if absent is not None:raise AssertionError('Impossible mixed moment accepted')
    return {'actual_embedding_dimensions_checked':True,'affine_PBW_moments_checked':True,
        'CG_dimension_controls':25,'bounded_support_controls':2}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--support',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('Use ROOT coordinated128MiB launcher')
    inp,out=args.input.resolve(),args.output.resolve()
    pending=out.with_name(out.name+'.pending')
    if out.suffix!='.json' or out.exists() or pending.exists() or out==inp:raise ValueError('Choose new noncolliding.json output')
    if inp.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
    raw=inp.read_bytes()
    if len(raw)>2*1024**2:raise ValueError('Input grew beyond2MiB')
    data=json.loads(raw)
    bindings=data.get('producer_source_hashes',{})
    if str(Path(quartic.__file__).resolve()) not in bindings:raise ValueError('Quartic producer identity missing')
    paths={Path(__file__).resolve(),Path(quartic.__file__).resolve(),Path(next_grade.__file__).resolve(),*map(Path,bindings)}
    if out in paths:raise ValueError('Output collides with source')
    snapshots={inp:raw}
    for path in paths:
        if path.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[path]=path.read_bytes()
        if len(snapshots[path])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(path):hashlib.sha256(payload).hexdigest() for path,payload in snapshots.items()}
    if any(hashes[path]!=value for path,value in bindings.items()):raise ValueError('Input producer source differs')
    started=monotonic()
    def timeout(signum,frame):raise TimeoutError('Sixty-second bounded grade2 certificate limit')
    previous=signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,60)
    try:
        result=run(data,args.support)
        result.update(selftest=selftest(),input_record={'path':str(inp),'sha256':hashes[str(inp)]},
            producer_source_hashes={path:value for path,value in hashes.items() if path!=str(inp)},
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(path.read_bytes()!=payload for path,payload in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(quartic.support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if out.exists() or any(path.read_bytes()!=payload for path,payload in snapshots.items()):raise RuntimeError('Input/source/output changed before promotion')
        pending.replace(out)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous)
        if pending.exists():pending.unlink()
    print(json.dumps({'output':str(out),'seconds':result['seconds'],'pairs':len(result['rows'])}),flush=True)


if __name__=='__main__':main()
