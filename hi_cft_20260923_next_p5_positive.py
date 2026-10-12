"""Root-only exact positive-mode tests on A[7]_0 of the canonical P4 triplet.

Default: thirty PCT(A)_5 P5 tests against the six-current space. Optional
modes4,3 test saved S2,S3. Exact nonzero residuals are retained, not rounded.
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
from time import monotonic

import hi_cft_20260923_next_structure_lower_closure as lower
import hi_cft_20260923_proof_general_modes_v2 as modes
import hi_cft_20260923_proof_exact4 as e4

x,fast = lower.x,lower.fast
MIB = 1024**2


def bounded(vector,limit=40000):
    assert len(vector) <= limit
    assert max((lower.bits(c) for c in vector.values()),default=0) <= 2048
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 1024*1024
    return vector


def write(path,result):
    temporary = path.with_suffix('.json.tmp')
    with temporary.open('w') as stream:
        json.dump(result,stream,indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def install():
    fast.install(x)
    modes.vertex.cache_clear()
    modes.basis_mode.cache_clear()
    modes.old.creation.cache_clear()
    modes.MAX_GRADE = 5
    x.creation = lru_cache(maxsize=64)(modes.old.creation.__wrapped__)
    modes.old.creation = x.creation
    modes.vertex = lru_cache(maxsize=64)(modes.vertex.__wrapped__)
    modes.basis_mode = lru_cache(maxsize=128)(modes.basis_mode.__wrapped__)
    x.vertex,x.basis_mode = modes.vertex,modes.basis_mode


def reduce_exact(vector,grade,weight,rows,blocks):
    residual,relation = dict(vector),[]
    for pivot,name in sorted(blocks[grade].get(weight,{}).items()):
        coefficient = residual.get(pivot,x.ZERO_A)
        if coefficient:
            assert lower.bits(coefficient) <= 4096
            relation.append([name,lower.coefficient(coefficient)])
            lower.subtract(residual,coefficient,rows[name])
    bounded(residual)
    return residual,relation


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--p4-controls',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--output',default='hi_cft_20260923_next_p5_positive.json')
    parser.add_argument('--modes',default='5')
    parser.add_argument('--seconds',type=int,default=180)
    args = parser.parse_args()
    selected_modes = sorted(set(map(int,args.modes.split(','))),reverse=True)
    assert selected_modes and set(selected_modes) <= {5,4,3}
    assert 0 < args.seconds <= 600
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    output = Path(args.output)
    assert not output.exists(),'Use a new output for each bounded attempt'
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    started,result = monotonic(),None
    try:
        install()
        _,hashes,rows,blocks,ops,current_basis,input_terms = lower.load(args)
        control_path = Path(args.p4_controls)
        assert control_path.stat().st_size <= 8*MIB
        control = json.loads(control_path.read_text())
        assert control['status'] == 'exact_P4_triplet_and_lower_controls_passed'
        vectors_path = Path(control['vectors_file'])
        assert lower.sha(vectors_path) == control['vectors_sha256']
        with gzip.open(vectors_path,'rb') as stream:
            raw = stream.read(32*MIB+1)
            assert len(raw) <= 32*MIB and not stream.read(1)
        payload = json.loads(raw)
        del raw
        assert payload['format'] == 'exact-p4-triplet-v1'
        assert payload['source_sha256'] == control['source_sha256']
        for path,digest in payload['source_sha256'].items():
            assert lower.sha(path) == digest,path
            assert path not in hashes or hashes[path] == digest
            hashes[path] = digest
        p4_fields = []
        for field in payload['fields']:
            vector = bounded({(tuple(a),tuple(o)):x.A(c) for a,o,c in field['vector']},12000)
            assert len(vector) == len(field['vector']) and vector and all(vector.values())
            weight = tuple(field['weight'])
            assert field['grade'] == 4 and all(x.grade(s) == 4 and x.weight(s) == weight for s in vector)
            p4_fields.append((field['id'],weight,vector))
        assert [(name,weight) for name,weight,_ in p4_fields] == [
            ('P4_plus',(0,2)),('P4_zero',(0,0)),('P4_minus',(0,-2))]
        del payload
        for path in (__file__,lower.__file__,modes.__file__,e4.__file__,control_path,vectors_path):
            hashes[str(path)] = lower.sha(path)
        result = {'status':'running','source_sha256':hashes,'modes':selected_modes,
                  'expected_targets':30*len(selected_modes),'passed_targets':0,
                  'source_operator':7,'source_fields':[],'lowest_left_controls':[],
                  'relations':[],'current_basis':current_basis,'input_sparse_terms':input_terms,
                  'scope':'Exact finite tests on actual U words. A nonzero current residual proves U1 exceeds K and hence U=B under the separately established fork. Empty residuals are only these tested containments.'}
        # PCT conventions come from the source-bound lattice function. Exact
        # reduction into S2 independently certifies that every left field is inU.
        lowest = []
        for op,highest in enumerate(ops):
            vector = bounded(e4.pct(highest),12000)
            weights = {x.weight(s) for s in vector}
            assert len(weights) == 1
            weight = weights.pop()
            assert weight == tuple(-v for v in x.weight(next(iter(highest))))
            assert all(x.grade(s) == 2 for s in vector)
            residual,relation = reduce_exact(vector,2,weight,rows,blocks)
            assert not residual,('PCT left field is not in saved S2',op)
            result['lowest_left_controls'].append({'operator':op,'weight':weight,
                'vector':lower.packed(vector),'exact_S2_relation':relation})
            lowest.append((op,weight,vector))
        source_weight = x.weight(next(iter(ops[7])))
        assert source_weight == (1,13)
        p5_fields = []
        for name,weight,vector in p4_fields:
            target = bounded(x.mode(ops[7],0,vector))
            target_weight = tuple(a+b for a,b in zip(source_weight,weight))
            assert all(x.grade(s) == 5 and x.weight(s) == target_weight for s in target)
            record = {'id':'P5_from_'+name,'weight':target_weight,'grade':5,
                      'word':{'operator':7,'mode':0,'P4':name},'vector':lower.packed(target)}
            data = lower.text(record).encode()
            assert len(data) <= 32*MIB
            artifact = output.with_suffix('.'+name+'.json.gz')
            assert not artifact.exists()
            temporary = artifact.with_suffix('.gz.tmp')
            with gzip.open(temporary,'wb',compresslevel=1) as stream:
                stream.write(data)
            temporary.replace(artifact)
            result['source_fields'].append({'id':record['id'],'weight':target_weight,
                'word':record['word'],'terms':len(target),'vector_file':str(artifact),
                'file_sha256':lower.sha(artifact),'content_sha256':hashlib.sha256(data).hexdigest()})
            p5_fields.append((record['id'],target_weight,target))
            result['seconds'] = monotonic()-started
            write(output,result)
            del record,data
        for mode in selected_modes:
            grade = 6-mode
            for op,op_weight,operator in lowest:
                for name,pw,vector in p5_fields:
                    weight = tuple(a+b for a,b in zip(op_weight,pw))
                    target = bounded(x.mode(operator,mode,vector))
                    assert all(x.grade(s) == grade and x.weight(s) == weight for s in target)
                    residual,relation = reduce_exact(target,grade,weight,rows,blocks)
                    packed = lower.packed(target)
                    record = {'operator':op,'left_is_PCT':True,'mode':mode,'input':name,
                              'target_grade':grade,'weight':weight,'target_terms':len(target),
                              'relation':relation,'target_sha256':hashlib.sha256(lower.text(packed).encode()).hexdigest(),
                              'exact_residual_zero':not residual,'residual':lower.packed(residual)}
                    result['relations'].append(record)
                    result['seconds'] = monotonic()-started
                    result['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
                    if residual:
                        record['exact_target_vector'] = packed
                        result['status'] = ('exact_new_current_proves_U_equals_B' if grade == 1
                                            else 'exact_mode_leaves_saved_lower_space')
                        write(output,result)
                        print({'status':result['status'],'operator':op,'mode':mode,
                               'input':name,'residual_terms':len(residual)},flush=True)
                        return
                    result['passed_targets'] += 1
                write(output,result)
            print({'mode':mode,'passed_targets':result['passed_targets'],
                   'seconds':monotonic()-started},flush=True)
        assert result['passed_targets'] == result['expected_targets']
        result['status'] = 'all_selected_exact_positive_P5_modes_passed'
        write(output,result)
        print({'status':result['status'],'seconds':result['seconds'],
               'peak_rss_KiB':result['peak_rss_KiB']},flush=True)
    except (TimeoutError,MemoryError):
        if result is not None:
            result['status'] = 'bounded_interruption_partial_records_retained'
            result['seconds'] = monotonic()-started
            write(output,result)
        raise
    finally:
        signal.alarm(0)


if __name__ == '__main__':
    main()
