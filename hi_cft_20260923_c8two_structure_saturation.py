"""Root-only grade-three raising-coinvariant certificate for the H4 gate.

No job is authorized by this source. Existing H4 writers must be CLOSED.
Exact arithmetic gives exact deficits; prime full rank also proves spanning
against the independently certified characteristic-zero dimension 956.
"""
import argparse
from collections import Counter
from functools import lru_cache
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
import hi_cft_20260923_c8_exact_grade3 as g3
import hi_cft_20260923_next_grade4_disk as frozen
import hi_cft_20260923_next_fast_field as fast

MIB=1024**2
PRIME=1000003
FORMAT='h4-raising-coinvariant-certificate-v1'
MAX_BITS=4096
HASHES={}


class Stop(Exception):
    pass


def sha(path):
    path=str(Path(path).resolve())
    if path not in HASHES:
        digest=hashlib.sha256()
        with open(path,'rb') as stream:
            for block in iter(lambda:stream.read(MIB),b''):
                digest.update(block)
        HASHES[path]=digest.hexdigest()
    return HASHES[path]


def compact(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))


def unpack(blob,digest):
    decoder=zlib.decompressobj()
    data=decoder.decompress(blob,16*MIB+1)
    assert len(data)<=16*MIB and decoder.eof and not decoder.unconsumed_tail
    assert hashlib.sha256(data).hexdigest()==digest
    return json.loads(data)


def verify_graph(graph,bindings):
    for filename,digest in graph.items():
        assert sha(filename)==digest,filename
        filename=str(Path(filename).resolve())
        assert filename not in bindings or bindings[filename]==digest
        bindings[filename]=digest


def nested_graphs(value,bindings):
    if isinstance(value,dict):
        for key,item in value.items():
            if key.endswith('source_sha256') or key=='ancestor_files_sha256':
                assert isinstance(item,dict)
                verify_graph(item,bindings)
            elif isinstance(item,(dict,list)):
                nested_graphs(item,bindings)
    elif isinstance(value,list):
        for item in value:
            nested_graphs(item,bindings)


def atomic(path,value):
    data=json.dumps(value,indent=2).encode()
    if len(data)>32*MIB:
        raise Stop('32 MiB output record cap')
    temporary=path.with_suffix(path.suffix+'.tmp')
    with temporary.open('wb') as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--h4-directory',default='hi_cft_20260923_next_h4_integer_bulk_v2')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--arithmetic',choices=('exact','prime'),default='exact')
    parser.add_argument('--seconds',type=int,default=300)
    args=parser.parse_args()
    assert 0<args.seconds<=900
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=3*1024**3
    output=Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix(output.suffix+'.tmp').exists()
    started=monotonic()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('raising certificate alarm')))
    signal.alarm(args.seconds)
    result={'format':FORMAT,'status':'initializing','arithmetic':args.arithmetic,
            'prime':PRIME if args.arithmetic=='prime' else None,'operators':[],
            'additional_tests':[]}

    def boundary():
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss>1024*1024:
            raise Stop('1 GiB RSS boundary')
        if monotonic()-started>args.seconds:
            raise TimeoutError('raising certificate deadline')

    def checked(vector):
        assert len(vector)<=20000
        if args.arithmetic=='exact':
            for value in vector.values():
                assert max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in value)<=MAX_BITS
        boundary()
        return vector

    def packed(vector):
        return [[idx,[str(q) for q in value] if args.arithmetic=='exact' else int(value)]
                for idx,value in sorted(vector.items())]

    def save(status):
        result.update(status=status,seconds=monotonic()-started,
                      peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        atomic(output,result)
        print({'status':status,'operators':len(result['operators']),
               'additional_tests':len(result['additional_tests']),
               'seconds':result['seconds']},flush=True)

    try:
        if args.arithmetic=='exact':
            fast.install(x)
        else:
            assert g3.install_prime(PRIME)==[231543,1000]
        x.creation=lru_cache(maxsize=128)(g3.creation.__wrapped__)
        g3.creation=x.creation
        x.vertex=lru_cache(maxsize=256)(g3.vertex.__wrapped__)
        x.basis_mode=lru_cache(maxsize=512)(g3.basis_mode.__wrapped__)

        manifest=Path(args.checkpoint)/'manifest.json'
        assert manifest.stat().st_size<8*MIB
        meta=json.loads(manifest.read_text())
        assert meta['format']=='exact-cartan-span-v1'
        assert meta['completed_grade3'] and meta['dimensions']['3']==956
        assert any(h['stage']=='grade3 translation descendants' and h['dimensions']['3']==634 for h in meta['history'])
        order=meta['order']['3']
        assert len(order)==956 and len(set(order))==956
        normal=set(order[:634])
        quotient=order[634:]
        qindex={name:i for i,name in enumerate(quotient)}
        bindings={str(manifest.resolve()):sha(manifest)}
        verify_graph(meta['sources'],bindings)
        for path in (__file__,x.__file__,g3.__file__,frozen.__file__,fast.__file__):
            bindings[str(Path(path).resolve())]=sha(path)
        lower=Path('hi_cft_20260923_next_structure_lower_closure.json')
        lower_meta=json.loads(lower.read_text())
        assert lower_meta['status']=='complete' and lower_meta['cursor']==lower_meta['total_tasks']==3970
        verify_graph(lower_meta['source_sha256'],bindings)
        bindings[str(lower.resolve())]=sha(lower)
        unitary=Path('hi_cft_20260923_c8_exact_unitary_certificate.json')
        unitary_meta=json.loads(unitary.read_text())
        assert unitary_meta['exact_PCT_preservation']
        assert all(row['exact_primary_and_eigenvalue_checks'] for row in unitary_meta['primary_checks'])
        verify_graph(unitary_meta['source_sha256'],bindings)
        bindings[str(unitary.resolve())]=sha(unitary)
        control=Path('hi_cft_20260923_next_fast_field_check.json')
        control_meta=json.loads(control.read_text())
        assert control_meta['status']=='exact_field_and_mode_equivalence_passed'
        verify_graph(control_meta['source_sha256'],bindings)
        bindings[str(control.resolve())]=sha(control)

        rows,weights,blocks,terms={},{},{},0
        for filename in meta['block_files']:
            if not filename.startswith('grade3_'):
                continue
            path=manifest.parent/filename
            assert sha(path)==meta['files_sha256'][filename]
            bindings[str(path.resolve())]=sha(path)
            for record in frozen.row_stream(path):
                name=record['id']
                assert name in order and name not in rows and record['grade']==3
                weight=tuple(record['weight'])
                vector={(tuple(a),tuple(o)):v for a,o,c in record['vector'] if (v:=x.A(c))}
                checked(vector)
                assert vector and all(x.grade(s)==3 and x.weight(s)==weight for s in vector)
                pivot=min(vector)
                assert vector[pivot]==x.ONE
                block=blocks.setdefault(weight,{})
                assert pivot not in block
                block[pivot]=name
                rows[name],weights[name]=vector,weight
                terms+=len(vector)
                assert terms<=300000
        assert set(rows)==set(order)
        blocks={w:sorted(block.items()) for w,block in blocks.items()}
        quotient_multiplicities=Counter(weights[name] for name in quotient)
        assert max(quotient_multiplicities.values())<=64
        raising_bindings=dict(bindings)

        # Authenticate complete exact relation records in CLOSED H4 databases.
        directory=Path(args.h4_directory).resolve()
        assert directory.is_dir() and not list(directory.glob('*-journal'))
        databases=sorted(directory.glob('block_*.sqlite'))
        assert 0<len(databases)<=100
        passed={op:{} for op in range(9)}
        for path in databases:
            assert path.stat().st_size<=512*MIB and output!=path.resolve()
            connection=sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True)
            connection.execute('PRAGMA cache_size=-2048')
            connection.execute('PRAGMA mmap_size=0')
            try:
                bm=json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
                assert bm['format']=='exact-n4-selected-block-v1' and bm['failed_targets']==0
                assert bm['serial_bulk_policy']['operators']==list(range(9))
                nested_graphs(bm,bindings)
                assert bm['source_sha256'].get(str(manifest))==sha(manifest) or any(
                    Path(p).resolve()==manifest.resolve() and d==sha(manifest)
                    for p,d in bm['source_sha256'].items())
                names={r[0] for r in connection.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                for table in ('relations','zero_relations'):
                    if table not in names:
                        continue
                    count=0
                    for name,blob,digest,success in connection.execute('SELECT name,record,digest,passed FROM '+table+' ORDER BY name'):
                        assert success==1
                        record=unpack(blob,digest)
                        word=record['word']
                        op,input_name=word['operator'],word['exact_input']
                        assert 0<=op<9 and input_name in qindex and word['mode']==0
                        assert name=='A%d_zero_%s'%(op,input_name)
                        if table=='relations':
                            assert record['exact_residual_zero'] and record['residual']==[]
                        else:
                            assert record['exact_target_zero'] and record['normal_columns']==[]
                        assert input_name not in passed[op]
                        passed[op][input_name]={'file':str(path),'table':table,'name':name,'record_sha256':digest}
                        count+=1
                    expected=bm['verified_targets'] if table=='relations' else bm.get('zero_targets_verified',0)
                    assert count==expected
                bindings[str(path)]=sha(path)
            finally:
                connection.close()
            boundary()
        assert str(output) not in bindings
        result.update(source_sha256=bindings,raising_source_sha256=raising_bindings,
                      S3_dimension=956,N3_dimension=634,Q_dimension=322,input_sparse_terms=terms,
                      seed_count=sum(len(v) for v in passed.values()),seed_records=passed,
                      quotient_order=quotient,quotient_weights=[weights[name] for name in quotient])
        save('sources_authenticated')

        def subtract(out,c,row):
            for state,value in row.items():
                v=out.get(state,x.ZERO_A)-c*value
                if v:
                    out[state]=v
                else:
                    out.pop(state,None)

        def coordinates(vector,weight):
            out=checked(dict(vector))
            answer={}
            for pivot,name in blocks.get(weight,[]):
                coefficient=out.get(pivot,x.ZERO_A)
                if coefficient:
                    if name in qindex:
                        answer[qindex[name]]=coefficient
                    subtract(out,coefficient,rows[name])
            assert not out,('Raising image leaves the certified S3 space',weight)
            return checked(answer)

        def insert(echelon,vector):
            out=dict(vector)
            for pivot,row in sorted(echelon.items()):
                coefficient=out.get(pivot,x.ZERO_A)
                if coefficient:
                    subtract(out,coefficient,row)
            checked(out)
            if not out:
                return False
            pivot=min(out)
            inverse=out[pivot].inv()
            echelon[pivot]=checked({s:c*inverse for s,c in out.items()})
            assert len(echelon)<=322
            return True

        image_basis={}
        raising_images=[]
        raising_serialized_bytes=0
        for name in quotient:
            for axis,current,shift in (('LEFT',x.LEFT[1],(2,0)),('RIGHT',x.RIGHT[1],(0,2))):
                weight=tuple(a+b for a,b in zip(weights[name],shift))
                image=checked(x.mode(current,0,rows[name]))
                assert all(x.grade(s)==3 and x.weight(s)==weight for s in image)
                coordinate=coordinates(image,weight)
                independent=insert(image_basis,coordinate)
                record={'axis':axis,'input':name,'weight':weight,
                        'coordinates':packed(coordinate),'independent':independent}
                raising_serialized_bytes+=len(compact(record).encode())
                if raising_serialized_bytes>12*MIB:
                    raise Stop('12 MiB compact raising-coordinate record cap')
                raising_images.append(record)
            if len(raising_images)%40==0:
                print({'raising_images':len(raising_images),'image_rank':len(image_basis),
                       'seconds':monotonic()-started},flush=True)
                for function in (x.creation,x.vertex,x.basis_mode):
                    function.cache_clear()
        multiplicities=Counter(weights[name] for name in quotient)
        irreducibles=[]
        for left,right in sorted(multiplicities):
            if left>0 or right>0:
                continue
            count=(multiplicities[left,right]-multiplicities[left-2,right]
                   -multiplicities[left,right-2]+multiplicities[left-2,right-2])
            assert count>=0
            if count:
                irreducibles.append({'highest_weight':[-left,-right],'multiplicity':count})
        expected_coinvariants=sum(row['multiplicity'] for row in irreducibles)
        assert sum((row['highest_weight'][0]+1)*(row['highest_weight'][1]+1)*row['multiplicity'] for row in irreducibles)==322
        assert len(image_basis)==322-expected_coinvariants,('Raising-image rank disagrees with exact K character',len(image_basis),expected_coinvariants)
        result.update(raising_images=raising_images,raising_image_rank=len(image_basis),
                      exact_K_character=irreducibles,coinvariant_dimension=expected_coinvariants)
        save('raising_images_complete')

        data=json.loads(Path('hi_cft_20260923_c8_exact_fields.json').read_text())['fields']
        op_weights=[(r['dimensions'][0]-1,r['dimensions'][1]-1) for r in data[:-1]]+[(0,0)]
        assert len(op_weights)==9
        result['left_highest_checks']=[]
        for op,record in enumerate(data):
            left=x.read_field(record)
            assert all(x.grade(s)==2 and x.weight(s)==op_weights[op] for s in left)
            assert not x.mode(x.LEFT[1],0,left)
            assert not x.mode(x.RIGHT[1],0,left)
            result['left_highest_checks'].append({'operator':op,'passed':True,'arithmetic':args.arithmetic})
        # Output-weight size is a heuristic for selecting economical EXISTING
        # right inputs. It has no role in any exact rank conclusion.
        for op in range(9):
            basis={p:dict(row) for p,row in image_basis.items()}
            for name in quotient:
                if name in passed[op]:
                    insert(basis,{qindex[name]:x.ONE})
            seeded_rank=len(basis)
            deficit=322-seeded_rank
            candidates=[name for name in quotient if name not in passed[op]]
            candidates.sort(key=lambda name:(-sum(abs(a+b) for a,b in zip(op_weights[op],weights[name])),len(rows[name]),name))
            additional=[]
            for name in candidates:
                if insert(basis,{qindex[name]:x.ONE}):
                    entry={'operator':op,'exact_input':name,
                           'input_weight':weights[name],
                           'output_weight':tuple(a+b for a,b in zip(op_weights[op],weights[name]))}
                    additional.append(entry)
                if len(basis)==322:
                    break
            assert len(basis)==322 and len(additional)==deficit
            result['operators'].append({'operator':op,'passed_input_count':len(passed[op]),
                'seeded_quotient_rank':seeded_rank,
                'exact_deficit':deficit if args.arithmetic=='exact' else None,
                'prime_deficit_upper_bound':deficit if args.arithmetic=='prime' else None,
                'gate4_proved_from_existing_identities':deficit==0,
                'augmented_quotient_rank':322,
                'gate4_proved_if_additional_identities_pass':True,
                'additional_tests':additional})
            result['additional_tests'].extend(additional)
            save('operator_saturation_complete')
        result['all_gate4_proved_from_existing_identities']=not result['additional_tests']
        result['scope']=('Exact raising-coinvariant ranks and minimal additional saved-input count.'
            if args.arithmetic=='exact' else
            'Prime full rank proves characteristic-zero spanning inside the already exact956D S3. Partial deficits are upper bounds only.')
        result['scope']+=' New additional A0P3 identities remain conditional; this does not certify the grade-five gate or properness.'
        save('complete')
    except (Stop,TimeoutError,MemoryError) as error:
        signal.alarm(0)
        result['stop_reason']=str(error)
        save('bounded_stop')
    finally:
        signal.alarm(0)


if __name__=='__main__':
    main()
