"""Exact raising-kernel check for unfinished output-weight-zero H4 targets.

This proves only that the unresolved quotient classes are K singlets. Their
singlet projections still require exact membership certificates. Root-only;
all input H4 writers must be closed. No lattice modes are regenerated.
"""
import argparse
from collections import defaultdict,deque
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


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--saturation',default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--targeted-directory',default='hi_cft_20260923_c8two_targeted_h4_trimmed_v2')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_structure_h4_singlet_control.json')
    parser.add_argument('--seconds',type=int,default=180)
    args=parser.parse_args()
    assert 0<args.seconds<=300 and 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    started=monotonic()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('singlet control alarm')))
    signal.alarm(args.seconds)
    output=Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix(output.suffix+'.tmp').exists()
    path=Path(args.saturation).resolve();directory=Path(args.targeted_directory).resolve()
    cert=json.loads(path.read_text())
    assert cert['format']==auth.FORMAT and cert['status']=='complete' and cert['arithmetic']=='exact'
    assert cert['S3_dimension']==956 and cert['N3_dimension']==634 and cert['Q_dimension']==322
    assert len(cert['left_highest_checks'])==9 and all(r['passed'] for r in cert['left_highest_checks'])
    bindings={}
    auth.verify_graph(cert['source_sha256'],bindings)
    for p in (path,__file__,base.__file__,auth.__file__,fast.__file__):
        bindings[str(Path(p).resolve())]=auth.sha(p)
    order,weights=cert['quotient_order'],cert['quotient_weights']
    assert len(order)==len(set(order))==len(weights)==322
    qi={name:i for i,name in enumerate(order)}
    seeds={op:{} for op in range(9)}
    grouped=defaultdict(list)
    for opt,records in cert['seed_records'].items():
        op=int(opt)
        for name,ref in records.items():grouped[ref['file']].append((op,name,ref))
    for filename,records in grouped.items():
        dbpath=Path(filename).resolve()
        assert str(dbpath) in bindings
        assert not Path(str(dbpath)+'-journal').exists() and not Path(str(dbpath)+'-wal').exists()
        with closing(sqlite3.connect(dbpath.as_uri()+'?mode=ro&immutable=1',uri=True)) as db:
            db.execute('PRAGMA cache_size=-2048');db.execute('PRAGMA mmap_size=0')
            for op,name,ref in records:
                pair,digest=base.exact_record(db,ref['table'],ref['name'],ref['record_sha256'])
                assert pair==(op,name) and name not in seeds[op]
                seeds[op][name]=ref
    assert sum(map(len,seeds.values()))==2145
    assert directory.is_dir() and not list(directory.glob('*-journal')) and not list(directory.glob('*-wal'))
    policy_path=directory/'targeted_policy.json';policy=json.loads(policy_path.read_text())
    auth.nested_graphs(policy,bindings)
    assert policy['source_sha256'][str(path)]==auth.sha(path)
    requested={(r['operator'],r['exact_input']) for r in cert['additional_tests']}
    assert {tuple(v) for v in policy['requested_targets']}==requested
    bindings[str(policy_path)]=auth.sha(policy_path)
    additions={}
    databases=sorted(directory.glob('block_*.sqlite'))
    assert 0<len(databases)<=100
    for dbpath in databases:
        assert dbpath.stat().st_size<=512*MIB
        with closing(sqlite3.connect(dbpath.as_uri()+'?mode=ro&immutable=1',uri=True)) as db:
            db.execute('PRAGMA cache_size=-2048');db.execute('PRAGMA mmap_size=0')
            meta=json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            assert meta['failed_targets']==0 and meta['targeted_selection']['policy']==policy
            auth.nested_graphs(meta,bindings)
            records=list(db.execute('SELECT name FROM relations ORDER BY name'))
            assert len(records)==meta['verified_targets']
            for (key,) in records:
                pair,digest=base.exact_record(db,'relations',key)
                assert pair in requested and pair not in additions and pair[1] not in seeds[pair[0]]
                ref={'file':str(dbpath),'table':'relations','name':key,'record_sha256':digest}
                additions[pair]=ref;seeds[pair[0]][pair[1]]=ref
        bindings[str(dbpath)]=auth.sha(dbpath)
    pending=sorted(requested-set(additions))
    opweights=[(0,4),(0,8),(0,8),(0,12),(1,1),(1,5),(1,7),(1,13),(0,0)]
    assert pending and all(tuple(a+b for a,b in zip(opweights[op],weights[qi[n]]))==(0,0) for op,n in pending)

    def checked(v):
        assert len(v)<=322
        for c in v.values():
            assert max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in c)<=4096
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<=768*1024
        if monotonic()-started>args.seconds:raise TimeoutError('singlet control deadline')
        return v

    def subtract(out,c,row):
        if not c:return
        for index,value in row.items():
            v=out.get(index,fast.ZERO)-c*value
            if v:out[index]=v
            else:out.pop(index,None)

    def packed(v):return [[i,[str(q) for q in c]] for i,c in sorted(v.items())]

    E={}
    for row in cert['raising_images']:
        axis,name=row['axis'],row['input'];key=(axis,qi[name])
        assert axis in ('LEFT','RIGHT') and key not in E
        shift=(2,0) if axis=='LEFT' else (0,2)
        weight=[a+b for a,b in zip(weights[qi[name]],shift)]
        assert row['weight']==weight
        v={i:fast.FastField(c) for i,c in row['coordinates']}
        assert len(v)==len(row['coordinates']) and all(weights[i]==weight for i in v)
        E[key]=checked(v)
    assert len(E)==644

    result={'format':'H4-pending-singlet-control-v1','status':'initializing',
            'source_sha256':bindings,'old_exact_seed_count':2145,'additional_exact_count':len(additions),
            'pending_targets':[{'operator':op,'exact_input':n} for op,n in pending],
            'operators':[],'scope':'Exact raising annihilation modulo W4 only; singlet projected membership remains required.'}
    passed=True
    for op in sorted({op for op,n in pending}):
        basis={};records=[];queue=deque()
        def reduce(v):
            out=dict(v);rel=[]
            for pivot,(index,row) in sorted(basis.items()):
                c=out.get(pivot,fast.ZERO)
                if c:subtract(out,c,row);rel.append([index,[str(q) for q in c]])
            return checked(out),rel
        def insert(raw,recipe):
            v,rel=reduce(raw)
            if not v:return False
            pivot=min(v);factor=v[pivot];inv=factor.inv()
            v=checked({i:c*inv for i,c in v.items()})
            index=len(records)
            basis[pivot]=(index,v)
            records.append({'recipe':recipe,'raw_coordinates':packed(raw),'elimination':rel,
                            'normalizing_pivot_coefficient':[str(q) for q in factor],
                            'pivot':pivot,'coordinates':packed(v)})
            queue.append(index)
            assert len(records)<=322
            return True
        for name,ref in sorted(seeds[op].items()):
            insert({qi[name]:fast.ONE},{'kind':'exact_H4_seed','input':name,'record':ref})
        while queue:
            index=queue.popleft();v=dict((i,fast.FastField(c)) for i,c in records[index]['coordinates'])
            for axis in ('LEFT','RIGHT'):
                image={}
                for i,c in v.items():subtract(image,-c,E[axis,i])
                insert(checked(image),{'kind':'raising_image','axis':axis,'basis_record':index})
        checks=[]
        for operator,name in pending:
            if operator!=op:continue
            for axis in ('LEFT','RIGHT'):
                residual,rel=reduce(E[axis,qi[name]])
                checks.append({'input':name,'axis':axis,'basis_coefficients':rel,
                               'exact_residual':packed(residual),'passed':not residual})
                passed=passed and not residual
        result['operators'].append({'operator':op,'known_kernel_dimension':len(basis),
                                    'basis_records':records,'pending_raising_checks':checks})
    result.update(status='all_pending_H4_classes_are_K_singlets' if passed else 'unresolved_nonsinglet_classes',
                  seconds=monotonic()-started,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    assert str(output) not in bindings and str(output.with_suffix(output.suffix+'.tmp')) not in bindings
    auth.atomic(output,result)
    signal.alarm(0)
    print({'status':result['status'],'pending':len(pending),'seconds':result['seconds']},flush=True)


if __name__=='__main__':main()
