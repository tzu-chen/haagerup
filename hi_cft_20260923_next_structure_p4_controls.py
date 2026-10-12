"""Root-only exact P4 triplet construction and lower controls, no self-launch.

Builds a genuine (1,3) K-module from the first discovered raw extra using
finite Casimir projectors. Checks18 current identities and6 Virasoro
containments against the frozen exact lower spaces. A split-prime quotient
check is a basis-replacement control, never a characteristic-zero upper rank.
"""
import argparse
from functools import lru_cache
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as e4
import hi_cft_20260923_next_fast_field as fast
import hi_cft_20260923_next_structure_lower_closure as lower

MIB=1024**2
PRIME=1000003
MAX_TERMS=12000


def bounded(vector):
    assert len(vector)<=MAX_TERMS
    assert all(lower.bits(c)<=2048 for c in vector.values())
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<=768*1024
    return vector


def unpack(blob):
    decoder=zlib.decompressobj()
    data=decoder.decompress(blob,16*MIB+1)
    assert len(data)<=16*MIB and decoder.eof and not decoder.unconsumed_tail
    return json.loads(data)


def specialize(value):
    answer=0
    for q,r in zip(value,(1,231543,1000,231543000)):
        denominator=int(q.denominator)%PRIME
        assert denominator
        answer+=int(q.numerator)*pow(denominator,-1,PRIME)*r
    return answer%PRIME


def modular_control(path,fields):
    path=Path(path).resolve()
    assert path.stat().st_size<=512*MIB
    assert not Path(str(path)+'-journal').exists(),'Close modular producer first'
    connection=sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True)
    connection.execute('PRAGMA cache_size=-4096')
    connection.execute('PRAGMA mmap_size=0')
    try:
        meta=json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert meta['prime']==PRIME and meta['normal_span_complete']
        assert meta['normal_rank']==6007 and meta['extra_rank']==3
        states={}
        for idx,record in connection.execute('SELECT id,value FROM states ORDER BY id'):
            a,o=json.loads(record)
            states[idx]=(tuple(a),tuple(o))
        assert len(states)<=71052
        digest=hashlib.sha256()
        used_states=set()
        result=[]
        for field in fields:
            weight=tuple(field['weight'])
            vector=field['exact_vector']
            out={s:v for s,c in vector.items() if (v:=specialize(c))}
            assert out
            selected=list(connection.execute('SELECT id,pivot FROM rows WHERE w0=? AND w1=?',weight))
            selected.sort(key=lambda r:states[r[1]])
            for idx,pivot_id in selected:
                pivot=states[pivot_id]
                factor=out.get(pivot,0)
                if not factor:
                    continue
                blob,=connection.execute('SELECT reduced FROM rows WHERE id=?',(idx,)).fetchone()
                row=unpack(blob)
                digest.update(lower.text([field['id'],idx,pivot_id,hashlib.sha256(blob).hexdigest()]).encode())
                for state_id,c in row:
                    used_states.add(state_id)
                    state=states[state_id]
                    value=(out.get(state,0)-factor*c)%PRIME
                    if value:
                        out[state]=value
                    else:
                        out.pop(state,None)
            assert out,'Projected P4 disappears modulo the selected N4 columns'
            extras=list(connection.execute('SELECT id,pivot,reduced FROM extras WHERE w0=? AND w1=?',weight))
            assert len(extras)==1
            extra_id,pivot_id,blob=extras[0]
            row=unpack(blob)
            pivot=states[pivot_id]
            multiplier=out.get(pivot,0)
            assert multiplier
            digest.update(lower.text(['extra',extra_id,pivot_id,hashlib.sha256(blob).hexdigest()]).encode())
            for state_id,c in row:
                used_states.add(state_id)
                state=states[state_id]
                value=(out.get(state,0)-multiplier*c)%PRIME
                if value:
                    out[state]=value
                else:
                    out.pop(state,None)
            assert not out,'Projected vector has a new modular direction beyond recorded extras'
            result.append({'field':field['id'],'weight':list(weight),'extra_id':extra_id,
                           'nonzero_multiplier_mod_prime':multiplier,
                           'quotient_replacement_passed':True})
        for idx in sorted(used_states):
            digest.update(lower.text([idx,states[idx]]).encode())
        return {'prime':PRIME,'rank_over_selected_normal_columns':3,
                'controls':result,'consumed_normal_extra_records_sha256':digest.hexdigest(),
                'discovery_database':str(path),'discovery_snapshot_sha256':lower.sha(path),
                'scope':'Independent replacement of three columns at one split prime; no characteristic-zero upper-rank inference.'}
    finally:
        connection.close()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--pilot-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-row',default='r3_000705')
    parser.add_argument('--source-operator',type=int,default=0)
    parser.add_argument('--output',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--seconds',type=int,default=300)
    args=parser.parse_args()
    assert 0<args.seconds<=900 and 0<=args.source_operator<10
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    output=Path(args.output)
    vector_path=output.with_suffix('.vectors.json.gz')
    assert not output.exists() and not vector_path.exists()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('P4 control hard alarm')))
    signal.alarm(args.seconds)
    started=monotonic()
    try:
        fast.install(x)
        x.creation=lru_cache(maxsize=64)(e4.creation.__wrapped__)
        e4.creation=x.creation
        x.vertex=lru_cache(maxsize=128)(e4.vertex.__wrapped__)
        x.basis_mode=lru_cache(maxsize=256)(e4.basis_mode.__wrapped__)
        source,hashes,rows,blocks,ops,_,input_terms=lower.load(args)
        for path in (__file__,e4.__file__):
            hashes[str(path)]=lower.sha(path)
        assert args.source_row in source['order']['3'][634:]
        raw=bounded(x.mode(ops[args.source_operator],0,rows[args.source_row]))
        assert raw and all(x.grade(s)==4 and x.weight(s)==(0,2) for s in raw)
        projected=raw
        projector_steps=[]
        for name,raising,lowering,levels in (
                ('left_spin0',x.LEFT[1],x.LEFT[2],range(1,3)),
                ('right_spin1',x.RIGHT[1],x.RIGHT[2],range(2,13))):
            for level in levels:
                denominator=level*(level+1)-(2 if name=='right_spin1' else 0)
                raised=bounded(x.mode(raising,0,projected))
                returned=bounded(x.mode(lowering,0,raised))
                projected=bounded(x.vadd((1,projected),(-fast.rational(1)/denominator,returned)))
                assert all(x.grade(s)==4 and x.weight(s)==(0,2) for s in projected)
                projector_steps.append({'factor':name,'spin':level,'denominator':denominator,
                                        'terms':len(projected)})
                for function in (x.creation,x.vertex,x.basis_mode):
                    function.cache_clear()
                print({'projection':name,'spin':level,'terms':len(projected),
                       'seconds':monotonic()-started},flush=True)
        assert projected
        middle=bounded(x.mode(x.RIGHT[2],0,projected))
        bottom=bounded(x.mode(x.RIGHT[2],0,middle))
        assert middle and bottom
        exact_fields=[projected,middle,bottom]
        names=['P4_plus','P4_zero','P4_minus']
        fields=[{'id':name,'grade':4,'weight':[0,2-2*i],'exact_vector':vector}
                for i,(name,vector) in enumerate(zip(names,exact_fields))]
        current_checks=[]
        for i,field in enumerate(fields):
            vector=field['exact_vector']
            assert all(x.weight(s)==tuple(field['weight']) for s in vector)
            for cur,current in enumerate(x.LEFT+x.RIGHT):
                actual=bounded(x.mode(current,0,vector))
                if cur<3:
                    expected={}
                elif cur==3:
                    expected=x.vadd((2-2*i,vector))
                elif cur==4:
                    expected={} if i==0 else x.vadd((2,exact_fields[i-1]))
                else:
                    expected={} if i==2 else exact_fields[i+1]
                assert actual==expected,('Exact K-type control failed',field['id'],cur)
                current_checks.append({'field':field['id'],'current':cur,'passed':True})
        virasoro=[]
        omega=x.omega()
        for field in fields:
            for vir_mode,grade in ((1,3),(2,2)):
                target=bounded(x.mode(omega,vir_mode+1,field['exact_vector']))
                assert all(x.grade(s)==grade for s in target)
                residual=target.copy()
                relation=[]
                weight=tuple(field['weight'])
                for pivot,name in sorted(blocks[grade].get(weight,{}).items()):
                    coefficient=residual.get(pivot,x.ZERO_A)
                    if coefficient:
                        assert lower.bits(coefficient)<=4096
                        relation.append([name,lower.coefficient(coefficient)])
                        lower.subtract(residual,coefficient,rows[name])
                assert not residual,('Positive Virasoro image leaves exact lower space',field['id'],vir_mode)
                virasoro.append({'field':field['id'],'L_mode':vir_mode,'target_grade':grade,
                                  'relation':relation,'exact_residual_zero':True,
                                  'target_sha256':hashlib.sha256(lower.text(lower.packed(target)).encode()).hexdigest()})
        modular=modular_control(args.pilot_database,fields)
        provenance={'source_operator':args.source_operator,'source_row':args.source_row,'source_mode':0,
                    'source_weight':[0,2],'source_raw_sha256':hashlib.sha256(lower.text(lower.packed(raw)).encode()).hexdigest(),
                    'projector_steps':projector_steps,
                    'triplet_definition':['v','F_right(0)v','F_right(0)^2v'],
                    'scope':'Exact actual K-type(1,3); provenance A_0S3+N4. No characteristic-zero quotient-dimension claim.'}
        payload={'format':'exact-p4-triplet-v1','source_sha256':hashes,
                 'fields':[{k:v for k,v in field.items() if k!='exact_vector'} |
                           {'vector':lower.packed(field['exact_vector'])} for field in fields],
                 'provenance':provenance,'current_controls':current_checks,
                 'virasoro_controls':virasoro,'modular_control':modular}
        serialized=lower.text(payload).encode()
        assert len(serialized)<=32*MIB
        temporary=vector_path.with_suffix(vector_path.suffix+'.tmp')
        with gzip.open(temporary,'wb',compresslevel=1) as stream:
            stream.write(serialized)
        temporary.replace(vector_path)
        result={'status':'exact_P4_triplet_and_lower_controls_passed',
                'source_sha256':hashes,'K_type':[1,3],'field_ids':names,
                'field_terms':[len(v) for v in exact_fields],
                'current_zero_mode_controls':len(current_checks),
                'positive_Virasoro_controls':len(virasoro),
                'vectors_file':str(vector_path),'vectors_sha256':lower.sha(vector_path),
                'modular_control':modular,'provenance':provenance,
                'input_sparse_terms':input_terms,'seconds':monotonic()-started,
                'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                'scope':'Small exact H4 prerequisites only. Exact A0P3 and A0P4 normal-word containment gates remain.'}
        temporary=output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump(result,stream,indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(output)
        print({'status':result['status'],'seconds':result['seconds'],
               'field_terms':result['field_terms']},flush=True)
    finally:
        signal.alarm(0)


if __name__=='__main__':
    main()
