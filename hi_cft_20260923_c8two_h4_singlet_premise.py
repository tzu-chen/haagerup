"""Exact replay of the raising premises for twelve projected H4 targets.

No lattice mode or native solve is evaluated. Root-only certificate job.
"""
import argparse
from collections import defaultdict
from contextlib import closing
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_c8two_gate4_verify as base
import hi_cft_20260923_next_fast_field as fast

auth=base.source
MIB=1024**2


def read(path):
    path=Path(path).resolve()
    assert path.is_file() and path.stat().st_size<=32*MIB
    return json.loads(path.read_text())


def connect(path):
    path=Path(path).resolve()
    assert path.is_file() and path.stat().st_size<=512*MIB
    assert not Path(str(path)+'-journal').exists() and not Path(str(path)+'-wal').exists()
    db=sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True)
    db.execute('PRAGMA cache_size=-2048');db.execute('PRAGMA mmap_size=0')
    return db


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--control',default='hi_cft_20260923_c8two_structure_h4_singlet_control.json')
    parser.add_argument('--saturation',default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--raised-directory',default='hi_cft_20260923_c8two_structure_h4_raised_exact')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_h4_singlet_premise_verified.json')
    parser.add_argument('--seconds',type=int,default=180)
    args=parser.parse_args()
    assert 0<args.seconds<=300 and 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    started=monotonic()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('singlet premise replay alarm')))
    signal.alarm(args.seconds)
    output=Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix(output.suffix+'.tmp').exists()
    bindings={}

    def bind(path):
        path=str(Path(path).resolve());digest=auth.sha(path)
        assert path not in bindings or bindings[path]==digest
        bindings[path]=digest

    def boundary():
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<=768*1024
        assert monotonic()-started<=args.seconds

    def checked(v):
        assert len(v)<=322 and all(isinstance(i,int) and 0<=i<322 for i in v)
        for c in v.values():
            assert c and max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in c)<=4096
        boundary();return v

    def unpack(rows):
        assert len(rows)<=322
        out={i:fast.FastField(c) for i,c in rows}
        assert len(out)==len(rows)
        return checked(out)

    def packed(v):return [[i,[str(q) for q in c]] for i,c in sorted(v.items())]

    def add(out,i,c):
        value=out.get(i,fast.ZERO)+c
        if value:out[i]=value
        else:out.pop(i,None)

    try:
        for path in (__file__,base.__file__,auth.__file__,fast.__file__):bind(path)
        control,sat=read(args.control),read(args.saturation)
        assert control['format']=='H4-pending-singlet-control-v1'
        assert control['status'] in ('unresolved_nonsinglet_classes','all_pending_H4_classes_are_K_singlets')
        auth.nested_graphs(control,bindings);bind(args.control)
        assert bindings[str(Path(args.saturation).resolve())]==auth.sha(args.saturation)
        assert sat['format']==auth.FORMAT and sat['status']=='complete' and sat['arithmetic']=='exact'
        assert sat['S3_dimension']==956 and sat['N3_dimension']==634 and sat['Q_dimension']==322
        assert len(sat['left_highest_checks'])==9 and all(row['passed'] for row in sat['left_highest_checks'])
        auth.nested_graphs(sat,bindings);bind(args.saturation)
        order,weights=sat['quotient_order'],sat['quotient_weights']
        assert len(order)==len(set(order))==len(weights)==322
        qi={name:i for i,name in enumerate(order)}
        pending=[(row['operator'],row['exact_input']) for row in control['pending_targets']]
        assert len(pending)==len(set(pending))==12
        opweights=[(0,4),(0,8),(0,8),(0,12),(1,1),(1,5),(1,7),(1,13),(0,0)]
        assert all(tuple(a+b for a,b in zip(opweights[op],weights[qi[name]]))==(0,0) for op,name in pending)
        E={}
        for row in sat['raising_images']:
            axis,name=row['axis'],row['input'];key=(axis,qi[name])
            assert axis in ('LEFT','RIGHT') and key not in E
            shift=(2,0) if axis=='LEFT' else (0,2)
            weight=[a+b for a,b in zip(weights[qi[name]],shift)]
            assert row['weight']==weight
            vector=unpack(row['coordinates'])
            assert all(weights[i]==weight for i in vector)
            E[key]=vector
        assert len(E)==644

        # Authenticate the actual H4 seed identities, independently of their counts.
        refs=defaultdict(dict)
        operators=control['operators']
        assert len(operators)==len({row['operator'] for row in operators})
        assert {row['operator'] for row in operators}=={op for op,_ in pending}
        for row in operators:
            op=row['operator']
            for record in row['basis_records']:
                recipe=record['recipe']
                if recipe['kind']=='exact_H4_seed':
                    name,ref=recipe['input'],recipe['record']
                    path=str(Path(ref['file']).resolve())
                    assert path in bindings and name in qi
                    key=(ref['table'],ref['name'])
                    value=(op,name,ref['record_sha256'])
                    assert key not in refs[path] or refs[path][key]==value
                    refs[path][key]=value
        seed_count=0
        for path,records in refs.items():
            with closing(connect(path)) as db:
                for (table,key),(op,name,digest) in records.items():
                    assert table in ('relations','zero_relations')
                    pair,actual=base.exact_record(db,table,key,digest)
                    assert pair==(op,name) and actual==digest
                    seed_count+=1
            boundary()

        required=set();results=[]
        for row in operators:
            op=row['operator'];basis={};vectors=[]

            def reduce(vector):
                out=dict(vector);relation=[]
                for pivot,(index,known) in sorted(basis.items()):
                    c=out.get(pivot,fast.ZERO)
                    if c:
                        relation.append([index,[str(q) for q in c]])
                        for i,value in known.items():add(out,i,-c*value)
                return checked(out),relation

            for index,record in enumerate(row['basis_records']):
                recipe=record['recipe']
                if recipe['kind']=='exact_H4_seed':
                    raw={qi[recipe['input']]:fast.ONE}
                else:
                    assert recipe['kind']=='raising_image' and recipe['axis'] in ('LEFT','RIGHT')
                    prior=recipe['basis_record'];assert isinstance(prior,int) and 0<=prior<index
                    raw={}
                    for i,c in vectors[prior].items():
                        for j,value in E[recipe['axis'],i].items():add(raw,j,c*value)
                checked(raw)
                assert raw==unpack(record['raw_coordinates'])
                reduced,relation=reduce(raw)
                assert relation==record['elimination'] and reduced
                pivot=min(reduced);factor=reduced[pivot]
                assert pivot==record['pivot'] and factor==fast.FastField(record['normalizing_pivot_coefficient'])
                inverse=factor.inv();normal=checked({i:c*inverse for i,c in reduced.items()})
                assert normal==unpack(record['coordinates']) and pivot not in basis
                basis[pivot]=(index,normal);vectors.append(normal)
            assert len(basis)==len(vectors)==row['known_kernel_dimension']<=322
            checks=row['pending_raising_checks']
            assert len(checks)==2*sum(operator==op for operator,_ in pending)
            seen=set()
            for check in checks:
                name,axis=check['input'],check['axis']
                assert (op,name) in pending and axis in ('LEFT','RIGHT') and (name,axis) not in seen
                seen.add((name,axis))
                residual,relation=reduce(E[axis,qi[name]])
                assert residual==unpack(check['exact_residual'])
                assert relation==check['basis_coefficients'] and check['passed']==(not residual)
                for i in residual:required.add((op,order[i]))
                results.append({'operator':op,'input':name,'axis':axis,
                    'replayed_kernel_dimension':len(basis),'residual_coordinates':packed(residual),
                    'new_exact_seed_inputs':[order[i] for i in sorted(residual)]})
        assert len(results)==24 and len(required)==12

        directory=Path(args.raised_directory).resolve()
        assert directory.is_dir() and not list(directory.glob('*-journal')) and not list(directory.glob('*-wal'))
        summarypath,policypath=directory/'summary.json',directory/'targeted_policy.json'
        summary,policy=read(summarypath),read(policypath)
        assert policy['format']=='targeted-H4-integer-residual-v1'
        assert summary['status']=='all_requested_exact_H4_targets_passed' and summary['policy']==policy
        assert {tuple(pair) for pair in policy['requested_targets']}==required
        auth.nested_graphs(policy,bindings);bind(summarypath);bind(policypath)
        raised={}
        for block in summary['blocks']:
            path=Path(block['output']).with_suffix('.sqlite').resolve()
            assert path.parent==directory and block['weight']==[0,2]
            with closing(connect(path)) as db:
                meta=json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
                assert meta['format']=='exact-n4-selected-block-v1' and meta['weight']==[0,2]
                assert meta['targeted_selection']['policy']==policy
                assert meta['all_requested_targets_verified'] and meta['failed_targets']==0
                auth.nested_graphs(meta,bindings)
                names=[item[0] for item in db.execute('SELECT name FROM relations ORDER BY name')]
                assert len(names)==meta['verified_targets']==block['verified_targets']
                for name in names:
                    pair,digest=base.exact_record(db,'relations',name)
                    assert pair in required and pair not in raised
                    raised[pair]={'file':str(path),'name':name,'record_sha256':digest}
            bind(path)
        assert set(raised)==required
        boundary()
        assert str(output) not in bindings and str(output.with_suffix(output.suffix+'.tmp')) not in bindings
        result={'format':'verified-H4-singlet-raising-premise-v1',
            'status':'all_pending_H4_classes_are_K_singlets','source_sha256':bindings,
            'pending_targets':control['pending_targets'],'pending_target_count':12,
            'exact_raising_checks_replayed':24,'exact_kernel_seed_records_authenticated':seed_count,
            'raising_checks':results,'additional_exact_seed_records':[
                {'operator':op,'input':name,**raised[op,name]} for op,name in sorted(raised)],
            'scope':'Each pending weight-zero H4 class is killed by both raising currents modulo W4. Exact joint-singlet projected containment is still required; no unprojected H4 membership is asserted here.',
            'seconds':monotonic()-started,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        auth.atomic(output,result)
        print({k:result[k] for k in ('status','pending_target_count','exact_raising_checks_replayed','seconds','peak_rss_KiB')},flush=True)
    finally:signal.alarm(0)


if __name__=='__main__':main()
