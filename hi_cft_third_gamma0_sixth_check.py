"""Exact sixth-current moment system for the two actual E8 survivors.

ROOT-only128MiB, pure stdlib. No support search or tensor arrays.
The actual B embedding and unique W2 finite representation are premises.
Six fixed rows are imposed without assuming their linear independence.
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

import hi_cft_third_gamma0_grade2_check as old


def representation(items):
    result=Counter()
    for item in items:
        n,m,c=(item[key] for key in ('left_dimension','right_dimension','multiplicity'))
        if any(type(x) is not int or x<=0 for x in (n,m,c)):raise ValueError('Malformed irrep')
        result[n,m]+=c
    return result


def power_trace(n,power):
    return sum((F(h**power,2**(power//2)) for h in range(1-n,n,2)),F(0))


def sixth(rep,left_power):
    return sum((c*power_trace(n,left_power)*power_trace(m,6-left_power)
                for (n,m),c in rep.items()),F(0))


def moment_controls():
    for n in range(1,41):
        if power_trace(n,2)!=old.next_grade.index(n) or power_trace(n,4)!=old.quartic.fourth(n):
            raise AssertionError('Literal Cartan powers disagree with old normalization')
        closed=F(n*(n*n-1)*(3*n**4-18*n*n+31),168)
        if power_trace(n,6)!=closed:raise AssertionError('Sixth-power closed formula failed')
    modular=old.quartic.modular
    eq=modular.shift(modular.B_at(984),864)
    space=modular.solve(eq,[F(0)]*12)
    if not space['consistent'] or space['dimension']!=6:raise AssertionError('M6 dimension changed')
    # P3=D4 D2 D0 chi. This explicit convolution independently checks
    # all three vacuum coefficients including the polar cross terms.
    character=[F(1),F(6),F(120)];exponents=[F(-1,3),F(2,3),F(5,3)]
    e2=[F(1),F(-24),F(-72)]
    def serre(series,weight):
        return [exponents[i]*series[i]-F(weight,12)*sum(e2[j]*series[i-j] for j in range(i+1))
                for i in range(3)]
    p3=serre(serre(serre(character,0),2),4)
    if p3!=[F(-1,9),F(14,9),F(1276,3)]:raise AssertionError('P3 vacuum coefficients failed')
    leading=[lam*(lam-F(1,6))*(lam-F(1,3))*modular.CHI[i][0]+F(8,9)*(i==0)
             for i,lam in enumerate(modular.LAMBDA)]
    if leading[0]!=p3[1]:raise AssertionError('P3 leading formula failed')
    if -24-(-504)!=480:raise AssertionError('Delta/E6 next coefficient failed')
    return {'space':space,'equations':eq,'P3_leading':leading,'P3_vacuum_coefficients':p3,
        'normalization':'S_ab=Tr(h_left^a h_right^b)/8 for a+b=6; ordinary I=Tr h²/2 and S4=Tr h⁴/4',
        'form':'H6=(Delta/E6)Xi v plus its stated P3 particular; (Bi+864I)v=0'}


def base_value(k,l,left_power,p3,chi_e23,q_e22,quartic_e2):
    ql,qr=q_e22;sl,mixed,sr=quartic_e2
    if left_power in (6,0):
        level=k if left_power==6 else l
        q=ql if left_power==6 else qr;s=sl if left_power==6 else sr
        return F(5*level**3,64)*p3+F(5*level,4)*s-F(5*level**2,16)*q+F(5*level**3,576)*chi_e23
    if left_power==2:
        k,l=l,k;ql,qr=qr,ql;sl=sr
    if left_power not in (4,2):raise ValueError('Unsupported even polarization')
    return F(k*k*l,64)*p3+F(k,2)*mixed+F(l,12)*sl-F(k*k,48)*qr-F(k*l,24)*ql+F(k*k*l,576)*chi_e23


def fit_one(k,l,witness,w2,certificate):
    modular=old.quartic.modular;names=modular.NAMES
    small=witness['small_ground_witness']
    traces=old.quartic.support.all_trace_targets({name:(small[name]['left_Dynkin_index'],small[name]['right_Dynkin_index'])
        for name in ('c1','d1','d4')},k,l)
    s4={kind:{name:F(value) for name,value in witness['quartic_predictions'][kind]['predicted_leading_moments'].items()}
        for kind in ('left','mixed','right')}
    target2,_=old.next_moments(k,l,witness)
    if old.moments(w2)!=target2:raise ValueError('Unique W2 representation does not reproduce all previous moments')
    reps={name:representation(small[name]['irreducible_summands']) for name in ('c1','d1','d4')}
    reps.update({'0':Counter({(3,1):1,(1,3):1}),'b':old.B80[k,l],'vacuum_grade2':w2})
    for name,rep in reps.items():
        if name=='vacuum_grade2':continue
        exact=old.moments(rep)
        expected=(int(modular.CHI[names.index(name)][0]),*traces[name],s4['mixed'][name],2*s4['left'][name],2*s4['right'][name])
        if exact!=expected:raise ValueError('Known representation disagrees with quadratic/quartic inputs')
    output=[]
    fixed=('0','c1','d1','d4','b','vacuum_grade2')
    for power in (6,4,2,0):
        base=[]
        for i,name in enumerate(names):
            base.append(base_value(k,l,power,certificate['P3_leading'][i],modular.CHI[i][0]-72*(i==0),
                traces[name],(s4['left'][name],s4['mixed'][name],s4['right'][name])))
        # E2*S4 and E2²*I have no polar term; their next coefficients
        # use only the known preceding vacuum-current coefficients.
        base2=base_value(k,l,power,F(1276,3),120-72*6+1512,
            (target2[1]-48*4,target2[2]-48*4),
            (F(target2[4],2)-24*8,target2[3],F(target2[5],2)-24*8))
        rows=list(certificate['equations']);rhs=[F(0)]*12;fixed_values={}
        for name in fixed:
            actual=sixth(reps[name],power)
            if name=='vacuum_grade2':
                row=[modular.CHI[0][j]+480*(j==0) for j in range(12)];part=base2
            else:
                i=names.index(name);row=modular.unit_row(i);part=base[i]
            rows.append(row);rhs.append(actual-part)
            fixed_values[name]={'sixth_trace':actual,'particular_base':part,'holomorphic_constraint':actual-part}
        solution=modular.solve(rows,rhs)
        record={'powers':[power,6-power],'fixed_rows':fixed_values,'solution':solution}
        if solution['consistent']:
            vector=solution['particular'];basis=solution['basis']
            record['all_ground_moment_affine_forms']={name:{'constant':base[i]+vector[i],
                'free_coefficients':[v[i] for v in basis]} for i,name in enumerate(names)}
        output.append(record)
    return {'levels':[k,l],'all_polarizations_consistent':all(x['solution']['consistent'] for x in output),
        'polarizations':output,'W2_representation':old.describe(w2)}


def calculate(quartic,factored):
    cert=moment_controls();rows=[]
    if len(quartic['surviving_levels'])!=2 or len(factored['rows'])!=2:raise ValueError('Both survivors required')
    for row in quartic['surviving_levels']:
        k,l=row['levels']
        if (k,l) not in old.P27 or len(row['witnesses'])!=1:raise ValueError('Unexpected survivor')
        saved=[r for r in factored['rows'] if r['levels']==[k,l]]
        if len(saved)!=1 or len(saved[0]['all_feasible_decompositions'])!=1:raise ValueError('Unique exhaustive W2 decomposition required')
        rep=representation(saved[0]['all_feasible_decompositions'][0]['affine_primary_irreps'])
        _,affine,_,_=old.ambient(k,l)
        rows.append(fit_one(k,l,row['witnesses'][0],rep+affine,cert))
    if {tuple(r['levels']) for r in rows}!={(1,39),(3,13)}:raise ValueError('Duplicate survivor')
    return {'coefficient_certificate':cert,'rows':rows,
        'scope':'Necessary sixth-current Jacobi system with the actual E8 embedding and unique W2 finite representation. Consistency does not prove sixth-moment support or VOA existence. Any residual free coefficients are retained explicitly; no support witness is selected for other grounds.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quartic',type=Path,required=True)
    parser.add_argument('--factored',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('ROOT coordinated128MiB launcher required')
    inputs=[args.quartic.resolve(),args.factored.resolve()];output=args.output.resolve();pending=output.with_name(output.name+'.pending')
    if output.suffix!='.json' or output.exists() or pending.exists() or output in inputs:raise ValueError('Choose new noncolliding output')
    snapshots={}
    for p in inputs:
        if p.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
        snapshots[p]=p.read_bytes()
        if len(snapshots[p])>2*1024**2:raise ValueError('Input grew beyond2MiB')
    quartic,factored=(json.loads(snapshots[p]) for p in inputs)
    # Verify the intermediate record joining the exhaustive W2 certificate
    # to the exact quartic input, rather than only matching source versions.
    middle_record=factored.get('input_record',{})
    middle=Path(middle_record['path']).resolve()
    if middle in inputs or middle==output or middle.stat().st_size>2*1024**2:
        raise ValueError('Invalid intermediate moment record')
    snapshots[middle]=middle.read_bytes()
    if len(snapshots[middle])>2*1024**2 or hashlib.sha256(snapshots[middle]).hexdigest()!=middle_record['sha256']:
        raise ValueError('Intermediate moment record changed')
    middle_data=json.loads(snapshots[middle]);upstream=middle_data.get('input_record',{})
    if Path(upstream['path']).resolve()!=inputs[0] or upstream['sha256']!=hashlib.sha256(snapshots[inputs[0]]).hexdigest():
        raise ValueError('Factored W2 and supplied quartic inputs have different ancestry')
    bindings={}
    for data in (quartic,factored,middle_data):
        for p,h in data.get('producer_source_hashes',{}).items():
            if p in bindings and bindings[p]!=h:raise ValueError('Producer versions disagree')
            bindings[p]=h
    if str(Path(old.quartic.__file__).resolve()) not in bindings:raise ValueError('Quartic producer binding absent')
    paths={Path(__file__).resolve(),Path(old.__file__).resolve(),Path(old.next_grade.__file__).resolve(),*map(Path,bindings)}
    if output in paths:raise ValueError('Output collides with source')
    for p in paths:
        if p.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[p]=p.read_bytes()
        if len(snapshots[p])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(p):hashlib.sha256(raw).hexdigest() for p,raw in snapshots.items()}
    if any(hashes[p]!=h for p,h in bindings.items()):raise ValueError('Producer source changed')
    def timeout(signum,frame):raise TimeoutError('Thirty-second sixth-moment cap')
    handler=signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,30)
    started=monotonic()
    try:
        result=calculate(quartic,factored)
        result.update(input_records=[{'path':str(p),'sha256':hashes[str(p)]} for p in inputs+[middle]],
            producer_source_hashes={p:h for p,h in hashes.items() if Path(p) not in inputs+[middle]},
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(p.read_bytes()!=raw for p,raw in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(old.quartic.support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if output.exists() or any(p.read_bytes()!=raw for p,raw in snapshots.items()):raise RuntimeError('Input/source/output changed')
        pending.replace(output)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,handler)
        if pending.exists():pending.unlink()
    print(json.dumps({'output':str(output),'rows':[{'levels':r['levels'],'consistent':r['all_polarizations_consistent'],
        'free_dimensions':[x['solution'].get('dimension') for x in r['polarizations']]} for r in result['rows']]}),flush=True)


if __name__=='__main__':main()
