"""Exact eighth-current Jacobi certificate using all unique ground supports.

ROOT128MiB only. Pure stdlib, bounded rational systems; no support search.
Actual E8 placement, H+ retention and prior unique support are premises.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_third_gamma0_orbit_sixth_ground as orbit


old=orbit.old
sixth=orbit.sixth


def gaussian(a,b,k,l):
    result={}
    for i in range(a//2+1):
        for j in range(b//2+1):
            combinatorial=F(factorial(a)*factorial(b),factorial(a-2*i)*factorial(b-2*j)*factorial(i)*factorial(j))
            result[a-2*i,b-2*j,i+j]=combinatorial*F((-k)**i*(-l)**j,24**(i+j))
    return result


def trace(rep,a,b):
    return sum((count*sixth.power_trace(n,a)*sixth.power_trace(m,b) for (n,m),count in rep.items()),F(0))


def completion(rep,a,b,k,l,previous=None,polar=False):
    value=F(0)
    for (aa,bb,r),coefficient in gaussian(a,b,k,l).items():
        moment=trace(rep,aa,bb)
        if previous is not None:
            moment-=24*r*trace(previous,aa,bb)
            if polar and aa==bb==0:moment+=-72*r+288*r*(r-1)
        elif polar and aa==bb==0:moment-=24*r
        value+=coefficient*moment
    return value


def certificate():
    # Compare the generic Gaussian recipe to the already audited M4/M6
    # normalizations; parameters3/13 avoid coinciding coefficients.
    k,l=3,13
    if gaussian(4,0,k,l)!={(4,0,0):F(1),(2,0,1):F(-k,2),(0,0,2):F(k*k,48)}:
        raise AssertionError('Generic Gaussian differs from pure quartic normalization')
    if gaussian(2,2,k,l)!={(2,2,0):F(1),(0,2,1):F(-k,12),(2,0,1):F(-l,12),(0,0,2):F(k*l,144)}:
        raise AssertionError('Generic Gaussian differs from mixed quartic normalization')
    if gaussian(6,0,k,l)!={(6,0,0):F(1),(4,0,1):F(-5*k,4),(2,0,2):F(5*k*k,16),(0,0,3):F(-5*k**3,576)}:
        raise AssertionError('Generic Gaussian differs from pure sixth normalization')
    if gaussian(4,2,k,l)!={(4,2,0):F(1),(2,2,1):F(-k,2),(4,0,1):F(-l,12),
            (0,2,2):F(k*k,48),(2,0,2):F(k*l,24),(0,0,3):F(-k*k*l,576)}:
        raise AssertionError('Generic Gaussian differs from mixed sixth normalization')
    if gaussian(8,0,k,l)[0,0,4]!=F(35*k**4,6912):raise AssertionError('Pure eighth polar coefficient failed')
    modular=old.quartic.modular
    bw=modular.B_at(-744)
    equations=modular.matmul(modular.shift(bw,-576),modular.shift(bw,-1152))
    space=modular.solve(equations,[F(0)]*12)
    if not space['consistent'] or space['dimension']!=9:raise AssertionError('M8 dimension changed')
    # Four successive Serre operations, including all polar cross terms.
    exponents=[F(-1,3),F(2,3),F(5,3)];e2=[F(1),F(-24),F(-72)]
    p4=[F(1),F(6),F(120)]
    for weight in (0,2,4,6):
        p4=[exponents[i]*p4[i]-F(weight,12)*sum(e2[j]*p4[i-j] for j in range(i+1)) for i in range(3)]
    if p4!=[F(5,54),F(-29,27),F(4598,9)]:raise AssertionError('P4 vacuum coefficients failed')
    leading=[lam*(lam-F(1,6))*(lam-F(1,3))*(lam-F(1,2))*modular.CHI[i][0]-F(32,27)*(i==0)
        for i,lam in enumerate(modular.LAMBDA)]
    if leading[0]!=p4[1] or -24-240!=-264:raise AssertionError('P4 leading or Delta/E4 next coefficient failed')
    if gaussian(8,0,1,1)[0,0,4]/p4[0]!=F(7,128):raise AssertionError('Pure eighth particular normalization failed')
    return {'space':space,'equations':equations,'P4_vacuum_coefficients':p4,'P4_leading':leading,
        'normalization':'R_ab=Tr(h_left^a h_right^b)/2^((a+b)/2); a+b=8 here.',
        'form':'H8=(Delta/E4)Xi v plus its polar P4 particular; (Bw-576I)(Bw-1152I)v=0; next=(chi_matrix-264I)v',
        'quartic_and_sixth_Gaussian_controls':True}


def calculate(support,m6):
    cert=certificate();modular=old.quartic.modular;names=modular.NAMES;rows=[]
    if len(support['rows'])!=2 or len(m6['rows'])!=2:raise ValueError('Both survivors required')
    for row in support['rows']:
        k,l=row['levels']
        if (k,l) not in old.P27 or not row['all_ground_supports_exist']:raise ValueError('Both supported pairs required')
        if len(row['grounds'])!=11 or {r['name'] for r in row['grounds']}!=set(names)-{'0'}:
            raise ValueError('Every nonvacuum ground required exactly once')
        reps={'0':Counter({(3,1):1,(1,3):1})}
        for ground in row['grounds']:
            if not ground['support_found'] or not ground['unique_support'] or ground['support_count']!=1 or len(ground['all_support_witnesses'])!=1:
                raise ValueError('An arbitrary nonunique ground support cannot fix eighth moments')
            rep=sixth.representation(ground['all_support_witnesses'][0])
            if orbit.moments(rep)!=tuple(map(F,ground['target'])) or not orbit.orbit_matches(rep,k,l):
                raise ValueError('Ground support fails old exact moments or orbit conditions')
            reps[ground['name']]=rep
        matching=[r for r in m6['rows'] if r['levels']==[k,l]]
        if len(matching)!=1 or not matching[0]['all_polarizations_consistent']:raise ValueError('Unique sixth row required')
        w2=sixth.representation(matching[0]['W2_representation'])
        if old.moments(w2)[0]!=120:raise ValueError('Full W2 dimension must be120')
        # The vacuum2 sixth moments are independently bound to the existing
        # certificate, rather than inferred from one newly chosen support.
        for polarization in matching[0]['polarizations']:
            power=polarization['powers'][0]
            if trace(w2,power,6-power)!=F(polarization['fixed_rows']['vacuum_grade2']['sixth_trace']):
                raise ValueError('W2 sixth moment does not match previous certificate')
        tests=[]
        for a in (8,6,4,2,0):
            b=8-a;polar=gaussian(a,b,k,l)[0,0,4]
            particular=polar/cert['P4_vacuum_coefficients'][0]
            constraints=list(cert['equations']);rhs=[F(0)]*12;fixed={}
            for i,name in enumerate(names):
                h8=completion(reps[name],a,b,k,l,polar=name=='0')
                value=h8-particular*cert['P4_leading'][i]
                constraints.append(modular.unit_row(i));rhs.append(value)
                fixed[name]={'eighth_trace':trace(reps[name],a,b),'completed_H8':h8,'holomorphic_constraint':value}
            ground_solution=modular.solve(constraints,rhs)
            hnext=completion(w2,a,b,k,l,previous=reps['0'],polar=True)
            value_next=hnext-particular*cert['P4_vacuum_coefficients'][2]
            constraints.append([modular.CHI[0][j]-264*(j==0) for j in range(12)]);rhs.append(value_next)
            full_solution=modular.solve(constraints,rhs)
            fixed['vacuum_grade2']={'eighth_trace':trace(w2,a,b),'completed_H8':hnext,'holomorphic_constraint':value_next}
            tests.append({'powers':[a,b],'polar_H8':polar,'P4_particular_coefficient':particular,
                'fixed_rows':fixed,'ground_only_solution':ground_solution,'full_solution':full_solution})
        rows.append({'levels':[k,l],'all_polarizations_consistent':all(r['full_solution']['consistent'] for r in tests),
            'polarizations':tests})
    if {tuple(r['levels']) for r in rows}!={(1,39),(3,13)}:raise ValueError('Duplicate survivor')
    return {'coefficient_certificate':cert,'rows':rows,
        'scope':'Necessary eighth-current Jacobi constraints under actual E8 placement, retained H+ extension and prior exhaustive unique ground/W2 representations. No affine-energy positivity of nonvacuum modules is added. Passing is not VOA existence; inconsistent exact systems exclude the stated necessary representation data.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--support',type=Path,required=True);p.add_argument('--sixth',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('ROOT coordinated128MiB guard required')
    inputs=[args.support.resolve(),args.sixth.resolve()];out=args.output.resolve();pending=out.with_name(out.name+'.pending')
    if out.suffix!='.json' or out.exists() or pending.exists() or out in inputs:raise ValueError('Choose new noncolliding output')
    snapshots={};data_records={}
    def load(path):
        if path.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
        raw=path.read_bytes()
        if len(raw)>2*1024**2:raise ValueError('Input grew beyond2MiB')
        snapshots[path]=raw;data_records[path]=json.loads(raw)
        return data_records[path]
    support,m6=(load(path) for path in inputs)
    ancestry=support.get('input_records',[])
    if len(ancestry)>5 or len(ancestry)<3:raise ValueError('Expected bounded support ancestry')
    for record in ancestry:
        path=Path(record['path']).resolve()
        if path==out:raise ValueError('Output collides with ancestor')
        if path not in snapshots:load(path)
        if hashlib.sha256(snapshots[path]).hexdigest()!=record['sha256']:raise ValueError('Support ancestor changed')
    if str(inputs[1]) not in {r['path'] for r in ancestry}:raise ValueError('Support record does not bind supplied sixth result')
    input_paths=set(snapshots);bindings={}
    for data in (support,m6):
        for path,h in data.get('producer_source_hashes',{}).items():
            if path in bindings and bindings[path]!=h:raise ValueError('Producer versions disagree')
            bindings[path]=h
    if str(Path(orbit.__file__).resolve()) not in bindings:raise ValueError('Exhaustive support producer missing')
    paths={Path(__file__).resolve(),Path(orbit.__file__).resolve(),*map(Path,bindings)}
    if out in paths:raise ValueError('Output collides with source')
    for path in paths:
        if path.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[path]=path.read_bytes()
        if len(snapshots[path])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(path):hashlib.sha256(raw).hexdigest() for path,raw in snapshots.items()}
    if any(hashes[path]!=h for path,h in bindings.items()):raise ValueError('Producer changed')
    def timeout(signum,frame):raise TimeoutError('Thirty-second eighth-moment cap')
    handler=signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,30);started=monotonic()
    try:
        result=calculate(support,m6)
        result.update(input_records=[{'path':str(path),'sha256':hashes[str(path)]} for path in sorted(input_paths)],
            producer_source_hashes={path:h for path,h in hashes.items() if Path(path) not in input_paths},
            seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        if any(path.read_bytes()!=raw for path,raw in snapshots.items()):raise RuntimeError('Input/source changed')
        with pending.open('x') as stream:
            json.dump(old.quartic.support.encode(result),stream,indent=2,allow_nan=False);stream.write('\n')
        if out.exists() or any(path.read_bytes()!=raw for path,raw in snapshots.items()):raise RuntimeError('Input/source/output changed')
        pending.replace(out)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,handler)
        if pending.exists():pending.unlink()
    print(json.dumps({'output':str(out),'rows':[{'levels':r['levels'],'consistent':r['all_polarizations_consistent']} for r in result['rows']]}),flush=True)


if __name__=='__main__':main()
