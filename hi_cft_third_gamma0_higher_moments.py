"""Exact degree10/12 current moments from every unique ground and W2.

ROOT128MiB only. Generic Gaussian completion, complete M10/M12 spaces,
small rational systems. No support search, tensor job or asymptotic fit.
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

import hi_cft_third_gamma0_eighth_check as eighth
old=eighth.old
modular=old.quartic.modular


def space_and_serre(degree):
    if degree==10:
        k6=modular.solve(modular.shift(modular.B_at(984),864),[F(0)]*12)
        k4=modular.solve(modular.shift(modular.B_at(-744),-1152),[F(0)]*12)
        if k6['dimension']!=6 or k4['dimension']!=3:raise AssertionError('M6/M4 dimensions changed')
        basis=k6['basis']+k4['basis'];shifts=[720]*6+[-1008]*3
    elif degree==12:
        basis=[modular.unit_row(i) for i in range(12)];shifts=[-24]*12
    else:raise ValueError('Only degrees10/12 reviewed')
    size=len(basis)
    leading_rows=[[v[i] for v in basis]+[F(0)]*(12-size) for i in range(12)]
    padding=[modular.unit_row(i) for i in range(size,12)]
    independent=modular.solve(leading_rows+padding,[F(0)]*(12+len(padding)))
    if not independent['consistent'] or independent['dimension']!=0:raise AssertionError('Leading basis is not independent')
    next_row=[sum(modular.CHI[0][j]*v[j] for j in range(12))+shift*v[0] for v,shift in zip(basis,shifts)]+[F(0)]*(12-size)
    p=[F(1),F(6),F(120)];exponents=[F(-1,3),F(2,3),F(5,3)];e2=[F(1),F(-24),F(-72)]
    for weight in range(0,degree,2):
        p=[exponents[i]*p[i]-F(weight,12)*sum(e2[j]*p[i-j] for j in range(i+1)) for i in range(3)]
    expected={10:[F(-5,54),F(40,27),F(13450,27)],12:[F(35,324),F(-170,81),F(35575,81)]}
    if p!=expected[degree]:raise AssertionError('Independent higher-Serre vacuum coefficients failed')
    def polynomial(lam):
        value=F(1)
        for weight in range(0,degree,2):value*=lam-F(weight,12)
        return value
    correction=p[1]-polynomial(F(2,3))*6
    pleading=[polynomial(lam)*modular.CHI[i][0]+correction*(i==0) for i,lam in enumerate(modular.LAMBDA)]
    return {'degree':degree,'dimension':size,'leading_basis':basis,'scalar_next_shifts':shifts,
        'leading_constraint_rows':leading_rows,'padding_rows':padding,'vacuum_next_row':next_row,
        'Serre_vacuum_coefficients':p,'Serre_leading':pleading,
        'form':'E4*M6 direct sum E6*M4' if degree==10 else 'Delta*Xi*v, arbitrary twelve-vector',
        'completeness':'At the E4 elliptic zero, E6*M4 spans the allowed values; subtract and divide by E4 to obtain M6. The sum is direct.' if degree==10 else 'Divide by Delta to obtain a weight-zero form with the single allowed principal part, represented uniquely by Xi*v.'}


def representations(support,m6):
    names=modular.NAMES;result=[]
    if len(support['rows'])!=2 or len(m6['rows'])!=2:raise ValueError('Both unique survivors required')
    for row in support['rows']:
        k,l=row['levels']
        if (k,l) not in old.P27 or not row['all_ground_supports_exist']:raise ValueError('Unexpected pair')
        if len(row['grounds'])!=11 or {r['name'] for r in row['grounds']}!=set(names)-{'0'}:
            raise ValueError('All eleven distinct nonvacuum grounds required')
        reps={'0':Counter({(3,1):1,(1,3):1})}
        for ground in row['grounds']:
            if not ground['unique_support'] or ground['support_count']!=1 or len(ground['all_support_witnesses'])!=1:
                raise ValueError('Nonunique support cannot fix higher moments')
            rep=eighth.sixth.representation(ground['all_support_witnesses'][0])
            if eighth.orbit.moments(rep)!=tuple(map(F,ground['target'])) or not eighth.orbit.orbit_matches(rep,k,l):
                raise ValueError('Ground fails old ten-moment or orbit controls')
            reps[ground['name']]=rep
        match=[r for r in m6['rows'] if r['levels']==[k,l]]
        if len(match)!=1 or not match[0]['all_polarizations_consistent']:raise ValueError('Matching M6 row required')
        w2=eighth.sixth.representation(match[0]['W2_representation'])
        if old.moments(w2)[0]!=120:raise ValueError('Full W2 dimension changed')
        for r in match[0]['polarizations']:
            a,b=r['powers']
            if eighth.trace(w2,a,b)!=F(r['fixed_rows']['vacuum_grade2']['sixth_trace']):raise ValueError('W2 sixth moments changed')
        result.append((k,l,reps,w2))
    if {(k,l) for k,l,_,_ in result}!={(1,39),(3,13)}:raise ValueError('Duplicate pair')
    return result


def calculate(support,m6):
    # Reuse the unchanged M8 controls, which verify the generic Gaussian
    # completion against all four pure/mixed M4/M6 formulas.
    eighth.certificate()
    spaces={degree:space_and_serre(degree) for degree in (10,12)}
    rows=[]
    for k,l,reps,w2 in representations(support,m6):
        degrees=[]
        for degree,space in spaces.items():
            polarizations=[]
            for a in range(degree,-1,-2):
                b=degree-a;polar=eighth.gaussian(a,b,k,l)[0,0,degree//2]
                particular=polar/space['Serre_vacuum_coefficients'][0]
                constraints=list(space['padding_rows']);rhs=[F(0)]*len(constraints);fixed={}
                for i,name in enumerate(modular.NAMES):
                    h=eighth.completion(reps[name],a,b,k,l,polar=name=='0')
                    value=h-particular*space['Serre_leading'][i]
                    constraints.append(space['leading_constraint_rows'][i]);rhs.append(value)
                    fixed[name]={'ordinary_moment':eighth.trace(reps[name],a,b),'completed_moment':h,'holomorphic_constraint':value}
                ground_solution=modular.solve(constraints,rhs)
                h=eighth.completion(w2,a,b,k,l,previous=reps['0'],polar=True)
                value=h-particular*space['Serre_vacuum_coefficients'][2]
                constraints.append(space['vacuum_next_row']);rhs.append(value)
                full_solution=modular.solve(constraints,rhs)
                fixed['vacuum_grade2']={'ordinary_moment':eighth.trace(w2,a,b),'completed_moment':h,'holomorphic_constraint':value}
                polarizations.append({'powers':[a,b],'polar_coefficient':polar,'Serre_particular_coefficient':particular,
                    'fixed_rows':fixed,'ground_only_solution':ground_solution,'full_solution':full_solution})
            degrees.append({'degree':degree,'all_polarizations_consistent':all(p['full_solution']['consistent'] for p in polarizations),
                'polarizations':polarizations})
        rows.append({'levels':[k,l],'degrees':degrees,'all_degrees_consistent':all(d['all_polarizations_consistent'] for d in degrees)})
    return {'spaces':spaces,'rows':rows,
        'normalization':'R_ab=Tr(h_left^a h_right^b)/2^((a+b)/2); degree a+b is10 or12.',
        'scope':'Necessary exact Jacobi constraints under the actual E8, forced H+ and exhaustively unique finite-representation premises. No nonvacuum affine-energy positivity is added. Consistency does not construct a VOA; no degree14 or higher completeness claim is made.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--support',type=Path,required=True);p.add_argument('--sixth',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();cap=resource.getrlimit(resource.RLIMIT_AS)[0]
    if cap==resource.RLIM_INFINITY or cap>128*1024**2:raise RuntimeError('ROOT coordinated128MiB guard required')
    inputs=[args.support.resolve(),args.sixth.resolve()];out=args.output.resolve();pending=out.with_name(out.name+'.pending')
    if out.suffix!='.json' or out.exists() or pending.exists() or out in inputs:raise ValueError('Choose new noncolliding output')
    snapshots={}
    def load(path):
        if path.stat().st_size>2*1024**2:raise ValueError('Input exceeds2MiB')
        raw=path.read_bytes()
        if len(raw)>2*1024**2:raise ValueError('Input grew beyond2MiB')
        snapshots[path]=raw;return json.loads(raw)
    support,m6=(load(path) for path in inputs)
    ancestry=support.get('input_records',[])
    if not 3<=len(ancestry)<=5:raise ValueError('Complete bounded support ancestry required')
    for record in ancestry:
        path=Path(record['path']).resolve()
        if path==out:raise ValueError('Output collides with ancestor')
        if path not in snapshots:load(path)
        if hashlib.sha256(snapshots[path]).hexdigest()!=record['sha256']:raise ValueError('Support ancestor changed')
    if str(inputs[1]) not in {r['path'] for r in ancestry}:raise ValueError('Support does not bind supplied sixth result')
    input_paths=set(snapshots);bindings={}
    for data in (support,m6):
        for path,h in data.get('producer_source_hashes',{}).items():
            if path in bindings and bindings[path]!=h:raise ValueError('Producer versions disagree')
            bindings[path]=h
    if str(Path(eighth.orbit.__file__).resolve()) not in bindings:raise ValueError('Exhaustive support producer missing')
    paths={Path(__file__).resolve(),Path(eighth.__file__).resolve(),*map(Path,bindings)}
    if out in paths:raise ValueError('Output collides with source')
    for path in paths:
        if path.stat().st_size>128*1024:raise ValueError('Source exceeds128KiB')
        snapshots[path]=path.read_bytes()
        if len(snapshots[path])>128*1024:raise ValueError('Source grew beyond128KiB')
    hashes={str(path):hashlib.sha256(raw).hexdigest() for path,raw in snapshots.items()}
    if any(hashes[path]!=h for path,h in bindings.items()):raise ValueError('Producer changed')
    def timeout(signum,frame):raise TimeoutError('Thirty-second higher-moment cap')
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
    print(json.dumps({'output':str(out),'rows':[{'levels':r['levels'],'consistent':r['all_degrees_consistent']} for r in result['rows']]}),flush=True)


if __name__=='__main__':main()
