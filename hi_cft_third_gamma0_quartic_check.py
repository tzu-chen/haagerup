"""Exact mixed and same-axis current Jacobi filters; ROOT-only128MiB job.

No tensor imports. Every input small-ground witness is retained or explicitly
rejected. Large-ground decomposition support is recomputed, never inferred
from one earlier d5/d6 witness. Resource exhaustion aborts the certificate.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_third_flavoured_trace_check as modular
import hi_cft_third_gamma0_d6_check as support


ENTRY_CAP = 20000
FUNCTIONAL = (1,0,0,0,-27,0,-13,0,0,-13,0,0)
EXPECTED_BASIS = (
    ('9/2','9/2','-9/2','-9/2','1/6','1',0,0,0,0,0,0),
    (13,-13,0,0,0,0,'2/5','18/5','-153/5','3/5',1,0),
    (0,0,0,0,0,0,'1/5','-21/5','51/5','-1/5',0,1))


def functional(vector):
    return sum((F(a)*b for a,b in zip(FUNCTIONAL,vector)),F(0))


def fourth(n):
    return F(n*(n*n-1)*(3*n*n-7),60)


def ground_moments(row):
    mixed,left,right = F(0),F(0),F(0)
    for term in row['irreducible_summands']:
        n,m,count = (term[key] for key in ('left_dimension','right_dimension','multiplicity'))
        mixed += count*support.index(n)*support.index(m)
        left += count*m*fourth(n)
        right += count*n*fourth(m)
    return (mixed,left,right)


def coefficient_certificate():
    equation = modular.shift(modular.B_at(-744),-1152)
    solved = modular.solve(equation,[F(0)]*12)
    expected = [list(map(F,row)) for row in EXPECTED_BASIS]
    if not solved['consistent'] or solved['dimension'] != 3 or solved['basis'] != expected:
        raise AssertionError('Audited three-dimensional M4 basis changed')
    if any(functional(row) for row in expected):
        raise AssertionError('M4 functional does not vanish')
    dims = [row[0] for row in modular.CHI]
    # At the first nonpolar coefficient, D_2 D_0 chi and E2^2 chi.
    d2 = [lam*(lam-F(1,6))*dim-F(4,3)*(i==0)
          for i,(lam,dim) in enumerate(zip(modular.LAMBDA,dims))]
    e22 = [dim-48*(i==0) for i,dim in enumerate(dims)]
    if functional(d2) != F(3,2) or functional(e22) != -279:
        raise AssertionError('Independent M4 functional constants failed')
    if F(-1,3)*(F(-1,3)-F(1,6)) != F(1,6):
        raise AssertionError('Serre derivative vacuum pole failed')
    return {'basis':expected,'functional':FUNCTIONAL,'D2Dchi_leading':d2,
        'E2_squared_chi_leading':e22,'D2Dchi_functional':F(3,2),
        'E2_squared_chi_functional':-279,
        'normalized_mixed_identity':'F(R_LR)=2+(F(Q_L)+F(Q_R))/12',
        'normalized_same_axis_identity':'F(R_LL)=6+F(Q_L)/2',
        'normalization':'Q=Tr u0^2/kappa; R_LR=Tr u0^2 v0^2/(kappa_u*kappa_v); R_LL=Tr u0^4/kappa^2',
        'scope':'Orthogonal commuting Cartans. Vacuum pole only; actual Haagerup modular representation and gamma0 character.'}


def predict(kind,k,l,traces,known,certificate):
    """Match three known grounds; test the independent vacuum coefficient."""
    d2,e22,basis = (certificate[key] for key in ('D2Dchi_leading','E2_squared_chi_leading','basis'))
    if kind == 'mixed':
        part = [F(k*l,24)*d2[i]+F(k*traces[name][1]+l*traces[name][0],12)
                -F(k*l,144)*e22[i] for i,name in enumerate(modular.NAMES)]
        expected_vacuum = F(0)
        moment_index = 0
    else:
        side = 0 if kind == 'left' else 1
        level = (k,l)[side]
        part = [F(level*level,8)*d2[i]+F(level,2)*traces[name][side]
                -F(level*level,48)*e22[i] for i,name in enumerate(modular.NAMES)]
        expected_vacuum = F(8)
        moment_index = side+1
    rhs = {name:known[name][moment_index]-part[modular.NAMES.index(name)] for name in ('c1','d1','d4')}
    coefficients = [6*rhs['c1'],rhs['d1']+rhs['d4'],3*rhs['d1']-2*rhs['d4']]
    values = [part[i]+sum((coefficients[j]*basis[j][i] for j in range(3)),F(0)) for i in range(12)]
    if any(values[modular.NAMES.index(name)] != known[name][moment_index] for name in rhs):
        raise AssertionError('Independent ground coefficient substitution failed')
    polynomial = None
    a,c = traces['c1'],traces['d4']
    if kind == 'mixed':
        polynomial = 40*k*l-28*(k+l)-45*(k*a[1]+l*a[0])-13*(k*c[1]+l*c[0])
        polynomial -= 162*known['c1'][0]+78*known['d1'][0]+78*known['d4'][0]
    else:
        side = 0 if kind == 'left' else 1
        level = (k,l)[side]
        polynomial = 40*level*level-56*level+16-90*level*a[side]-26*level*c[side]
        polynomial -= 54*known['c1'][side+1]+26*known['d1'][side+1]+26*known['d4'][side+1]
    # The polynomial is6 or2 times the residual (actual - predicted).
    factor = 6 if kind == 'mixed' else 2
    if polynomial != factor*(expected_vacuum-values[0]):
        raise AssertionError('Independent simplified quartic identity disagrees')
    return {'kind':kind,'holomorphic_M4_coefficients':coefficients,
        'predicted_leading_moments':dict(zip(modular.NAMES,values)),
        'vacuum_expected':expected_vacuum,'vacuum_predicted':values[0],
        'identity_polynomial':polynomial,'identity_passes':polynomial==0}


def realize_quartic(d,k,l,target,energy_filter,height,symmetric,entry_cap=ENTRY_CAP):
    """DP with dimension and five moments; stores one support witness."""
    if len(target)!=5 or any(type(x) is not int or x<0 for x in target):
        raise ValueError('Expected nonnegative integer ordinary indices and doubled fourth moments')
    types = [(n,m) for n in range(1,min(d,k+1)+1)
             for m in range(1,min(d//n,l+1)+1)
             if not energy_filter or support.energy(n,m,k,l)<=height]
    dp=[{} for _ in range(d+1)]
    dp[0][(0,0,0,0,0)]=()
    states=1
    for n,m in types:
        copies=2 if symmetric and (n+m)%2 else 1
        size=copies*n*m
        increment=(copies*m*support.index(n),copies*n*support.index(m),
            copies*support.index(n)*support.index(m),
            int(2*copies*m*fourth(n)),int(2*copies*n*fourth(m)))
        for current in range(size,d+1):
            for old,terms in dp[current-size].items():
                new=tuple(a+b for a,b in zip(old,increment))
                if any(a>b for a,b in zip(new,target)):continue
                if new not in dp[current]:
                    states+=1
                    if states>entry_cap:
                        raise RuntimeError('Quartic support DP cap exceeded; no exclusion may be inferred')
                    dp[current][new]=terms+((n,m),)*copies
    terms=dp[d].get(tuple(target))
    description=None if terms is None else support.describe(terms,k,l,height)
    if description is not None:
        moments=ground_moments(description)
        recomputed=(description['left_Dynkin_index'],description['right_Dynkin_index'],
            moments[0],2*moments[1],2*moments[2])
        if tuple(target)!=recomputed:raise AssertionError('Quartic support witness failed substitution')
    return description,{'states':states,'entry_cap':entry_cap,'types':len(types)}


def run(data,large_support=True):
    if not data.get('d6_dimension_filter_applied') or not data.get('d5_dimension_filter_applied'):
        raise ValueError('Completed d5/d6 support input required')
    energy=data['affine_energy_filter_applied']
    parity=data['bilinear_parity_filter_applied']
    if type(energy) is not bool or type(parity) is not bool:raise ValueError('Explicit inherited premise flags required')
    levels=data['d6_dimension_levels']
    if len(levels)>400 or sum(len(row['witnesses']) for row in levels)>1000:
        raise ValueError('Input exceeds400 pairs/1000 witnesses')
    cert=coefficient_certificate()
    output,survivors=[],[]
    seen=set()
    for row in levels:
        k,l=row['levels']
        if type(k) is not int or type(l) is not int or not 1<=k<=l or k+l>40 or (k,l) in seen:
            raise ValueError('Invalid or repeated level pair')
        seen.add((k,l))
        residual=F(2)+F(6,k+2)+F(6,l+2)
        if F(row['residual_central_charge'])!=residual or len(row['witnesses'])!=row['witness_count']:
            raise ValueError('Input count or central charge disagrees')
        records,kept=[],[]
        for wi,w in enumerate(row['witnesses']):
            small=w['small_ground_witness']
            t={name:support.checked_ground(small[name],d,h,k,l,energy) for name,d,h,_ in support.GROUND}
            if parity and not all(support.symmetric_ground(small[name]) for name in t):
                raise ValueError('Inherited symmetric-ground filter disagrees')
            full=support.all_trace_targets(t,k,l)
            if full['0']!=(4,4) or full!={name:tuple(pair) for name,pair in w['all_ground_indices'].items()}:
                raise ValueError('Input all-ground trace table disagrees')
            known={name:ground_moments(small[name]) for name in t}
            predictions={kind:predict(kind,k,l,full,known,cert) for kind in ('mixed','left','right')}
            failures=[kind+'_vacuum_identity' for kind,result in predictions.items() if not result['identity_passes']]
            all_moments={name:[predictions[kind]['predicted_leading_moments'][name] for kind in ('mixed','left','right')]
                         for name in modular.NAMES}
            if not failures:
                for name,(mixed,left,right) in all_moments.items():
                    if mixed<0 or mixed.denominator!=1 or left<0 or right<0 or (2*left).denominator!=1 or (2*right).denominator!=1:
                        failures.append(name+'_moment_sign_or_quantization')
                    if mixed>full[name][0]*full[name][1]:failures.append(name+'_mixed_index_upper_bound')
                    if parity and name in ('0','a','c0','c1','c2','d1','d2','d3','d4','d5','d6') and (left.denominator!=1 or right.denominator!=1):
                        failures.append(name+'_symmetric_fourth_integrality')
            new_support={}
            if not failures and large_support:
                for name,d,h in (('d5',13,F(7,13)),('d6',14,F(8,13))):
                    mixed,left,right=all_moments[name]
                    target=(*full[name],int(mixed),int(2*left),int(2*right))
                    witness,stats=realize_quartic(d,k,l,target,energy,h,parity)
                    new_support[name]={'target':target,'witness':witness,'DP_statistics':stats}
                    if witness is None:failures.append(name+'_joint_quartic_support')
            result={'input_witness_index':wi,'original_witness_index':w['original_witness_index'],
                'small_ground_witness':small,'known_ground_moments':known,
                'quartic_predictions':predictions,'new_large_ground_support':new_support,
                'passes':not failures,'failures':failures}
            records.append(result)
            if not failures:kept.append(result)
        output.append({'levels':[k,l],'residual_central_charge':residual,'witnesses':records})
        if kept:survivors.append({'levels':[k,l],'residual_central_charge':residual,'witness_count':len(kept),'witnesses':kept})
    if len(levels)!=data['d6_dimension_summary']['level_pair_count'] or sum(len(x['witnesses']) for x in levels)!=data['d6_dimension_summary']['witness_count']:
        raise ValueError('Input summary counts disagree')
    return {'coefficient_certificate':cert,'all_tested_levels':output,'surviving_levels':survivors,
        'summary':support.summary(survivors),'input_energy_filter_applied':energy,
        'input_energy_premise':data.get('energy_premise'),'input_bilinear_filter_applied':parity,
        'large_ground_quartic_support_applied':large_support,
        'scope':'Exact necessary joint/same-axis Jacobi constraints; no new nonvacuum energy premise. Retains every surviving small-ground witness. Each large-ground DP witness proves only support; failure exhausts its bounded finite domain. Passing does not construct a VOA.'}


def selftest():
    cert=coefficient_certificate()
    cases=0
    for n in range(1,9):
        weights=range(1-n,n,2)
        if sum((F(x*x,2) for x in weights),F(0))!=support.index(n) or sum((F(x**4,4) for x in weights),F(0))!=fourth(n):
            raise AssertionError('Literal SU2 weight moments disagree')
        for m in range(1,9):
            direct=sum((F(x*x*y*y,4) for x in range(1-n,n,2) for y in range(1-m,m,2)),F(0))
            if direct!=support.index(n)*support.index(m):raise AssertionError('Literal mixed Cartan moment disagrees')
            cases+=1
    # Independent tensor-product representation and refusal, including paired quaternionic terms.
    witness,_=realize_quartic(4,1,1,(2,2,1,2,2),False,F(1),True)
    if witness is None:raise AssertionError('Known(2,2) support refused')
    refused,_=realize_quartic(4,1,1,(2,2,0,2,2),False,F(1),True)
    if refused is not None:raise AssertionError('Impossible4D mixed moment accepted')
    # Scalar arithmetic of the separately proved rank-three charge-rank argument.
    qd4,qd1,rd4,rd1=F(12,13),F(16,13),F(72,169),F(32,169)
    if 4-3*qd4!=qd1 or 13*(rd4+rd1)!=8 or 7*rd1>=qd1*qd1:
        raise AssertionError('Rank-three fourth/Cauchy contradiction arithmetic failed')
    rank3_k2=40*4-56*2+16-26*8
    if rank3_k2!=-144:raise AssertionError('Rank-three level2 same-axis refusal failed')
    return {'literal_mixed_weight_cases':cases,'literal_fourth_weights_checked':True,
        'quartic_support_controls_checked':True,'functional_constants_checked':True,
        'rank3_scalar_controls':{'level1_Cauchy_gap':qd1*qd1-7*rd1,
            'level2_same_axis_identity_residual':rank3_k2,
            'scope':'Arithmetic only; the charge-support/orthogonality proof is recorded separately in hi_cft_third_rank3_quartic_obstruction.md.'}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--identities-only',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('Use ROOT coordinated128MiB launcher')
    inp,out=args.input.resolve(),args.output.resolve()
    pending=out.with_name(out.name+'.pending')
    sources=[Path(__file__).resolve(),Path(modular.__file__).resolve(),Path(support.__file__).resolve()]
    if out.suffix!='.json' or out.exists() or pending.exists() or out in [inp,*sources]:raise ValueError('Choose new noncolliding.json output')
    if inp.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
    payload=inp.read_bytes()
    if len(payload)>2*1024**2:raise ValueError('Input grew beyond2MiB')
    data=json.loads(payload)
    bindings=data.get('producer_source_hashes',{})
    if str(Path(support.__file__).resolve()) not in bindings:raise ValueError('Input producer identity missing')
    snapshots={inp:payload}
    for path in dict.fromkeys([*sources,*map(Path,bindings)]):
        if path.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[path]=path.read_bytes()
        if len(snapshots[path])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(path):hashlib.sha256(raw).hexdigest() for path,raw in snapshots.items()}
    if any(hashes[path]!=value for path,value in bindings.items()):raise ValueError('Input producer source changed')
    started=monotonic()
    def timeout(signum,frame):raise TimeoutError('Sixty-second exact quartic certificate cap')
    previous=signal.signal(signal.SIGALRM,timeout)
    signal.setitimer(signal.ITIMER_REAL,60)
    try:
        result=run(data,not args.identities_only)
        result.update(selftest=selftest(),input_record={'path':str(inp),'sha256':hashes[str(inp)]},
            producer_source_hashes={path:value for path,value in hashes.items() if path!=str(inp)},
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(path.read_bytes()!=raw for path,raw in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if out.exists() or any(path.read_bytes()!=raw for path,raw in snapshots.items()):raise RuntimeError('Input/source/output changed before promotion')
        pending.replace(out)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous)
        if pending.exists():pending.unlink()
    print(json.dumps(support.encode({'output':str(out),'summary':result['summary'],'seconds':result['seconds']})),flush=True)


if __name__=='__main__':main()
