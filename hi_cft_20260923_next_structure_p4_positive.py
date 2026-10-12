"""Root-only exact positive A modes on the controlled P4 triplet.

All ten weight-two highest fields, three P4 vectors, modes4,3,2:
90 targets in K,S2,S3. An exact nonzero echelon residual is retained
as a witness; no numerical rank inference is used.
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

import hi_cft_20260923_next_structure_lower_closure as lower
import hi_cft_20260923_proof_exact4 as e4
import hi_cft_20260923_next_structure_p4_controls as p4check

x,fast = lower.x,lower.fast
MIB = 1024**2


def bounded(vector):
    assert len(vector) <= 12000
    assert max((lower.bits(c) for c in vector.values()),default=0) <= 2048
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 768*1024
    return vector


def write(path,result):
    temporary = path.with_suffix('.json.tmp')
    with temporary.open('w') as stream:
        json.dump(result,stream,indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def grade4_controls(args,fields,ops,control,hashes,result,output,started):
    path = Path(args.pilot_database).resolve()
    assert path.stat().st_size <= 512*MIB
    assert not Path(str(path)+'-journal').exists()
    digest = lower.sha(path)
    assert digest == control['modular_control']['discovery_snapshot_sha256']
    hashes[str(path)] = digest
    connection = sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True)
    connection.execute('PRAGMA cache_size=-4096')
    connection.execute('PRAGMA mmap_size=0')
    try:
        meta = json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert meta['prime'] == p4check.PRIME and meta['normal_span_complete']
        assert meta['normal_rank'] == 6007 and meta['extra_rank'] == 3
        for filename,sha in meta['source_sha256'].items():
            assert lower.sha(filename) == sha
        states = {}
        for index,value in connection.execute('SELECT id,value FROM states ORDER BY id'):
            a,o = json.loads(value)
            states[index] = (tuple(a),tuple(o))
        assert len(states) <= 71052
        result['grade4_prime_controls'] = []
        result['grade4_prime'] = p4check.PRIME
        for op,operator in enumerate(ops):
            ow = x.weight(next(iter(operator)))
            for name,pw,vector in fields:
                weight = tuple(a+b for a,b in zip(ow,pw))
                target = bounded(x.mode(operator,1,vector))
                assert all(x.grade(s) == 4 and x.weight(s) == weight for s in target)
                out = {s:v for s,c in target.items() if (v:=p4check.specialize(c))}
                coefficients = []
                selected = list(connection.execute('SELECT id,pivot FROM rows WHERE w0=? AND w1=?',weight))
                selected.sort(key=lambda row:states[row[1]])
                extras = list(connection.execute('SELECT id,pivot FROM extras WHERE w0=? AND w1=?',weight))
                extras.sort(key=lambda row:states[row[1]])
                for table,choices in (('rows',selected),('extras',extras)):
                    for index,pivot in choices:
                        factor = out.get(states[pivot],0)
                        if not factor:
                            continue
                        coefficients.append([table,index,factor])
                        blob, = connection.execute('SELECT reduced FROM '+table+' WHERE id=?',(index,)).fetchone()
                        for state_id,c in p4check.unpack(blob):
                            state = states[state_id]
                            value = (out.get(state,0)-factor*c)%p4check.PRIME
                            if value:
                                out[state] = value
                            else:
                                out.pop(state,None)
                record = {'operator':op,'mode':1,'input':name,'weight':weight,
                          'target_sha256':hashlib.sha256(lower.text(lower.packed(target)).encode()).hexdigest(),
                          'prime_echelon_coefficients':coefficients,'prime_residual_zero':not out,
                          'prime_residual':[[list(s[0]),list(s[1]),v] for s,v in sorted(out.items())]}
                result['grade4_prime_controls'].append(record)
                result['seconds'] = monotonic()-started
                result['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
                if out:
                    record['exact_target_vector'] = lower.packed(target)
                    result['status'] = 'exact_U4_vectors_have_prime_rank_at_least_6011'
                    result['scope'] = 'One exact A1P4 target has a nonzero specialization residual beyond6010 independent actual U4 columns; this certifies dim U4>=6011. Empty prime residuals do not certify exact membership.'
                    write(output,result)
                    print({'status':result['status'],'operator':op,'input':name,'residual_terms':len(out)},flush=True)
                    return False
            write(output,result)
        assert len(result['grade4_prime_controls']) == 30
        return True
    finally:
        connection.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--p4-controls',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--pilot-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--output',default='hi_cft_20260923_next_structure_p4_positive.json')
    parser.add_argument('--seconds',type=int,default=300)
    args = parser.parse_args()
    assert 0 < args.seconds <= 300
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    output = Path(args.output)
    assert not output.exists()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    started = monotonic()
    result = None
    try:
        fast.install(x)
        x.creation = lru_cache(maxsize=64)(e4.creation.__wrapped__)
        e4.creation = x.creation
        x.vertex = lru_cache(maxsize=128)(e4.vertex.__wrapped__)
        x.basis_mode = lru_cache(maxsize=256)(e4.basis_mode.__wrapped__)
        _,hashes,rows,blocks,ops,current_basis,input_terms = lower.load(args)
        control_path = Path(args.p4_controls)
        assert control_path.stat().st_size < 8*MIB
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
            assert lower.sha(path) == digest
            assert path not in hashes or hashes[path] == digest
            hashes[path] = digest
        fields = []
        for field in payload['fields']:
            vector = bounded({(tuple(a),tuple(o)):x.A(c) for a,o,c in field['vector']})
            assert len(vector) == len(field['vector']) and vector and all(vector.values())
            weight = tuple(field['weight'])
            assert field['grade'] == 4
            assert all(x.grade(s) == 4 and x.weight(s) == weight for s in vector)
            fields.append((field['id'],weight,vector))
        assert [(name,weight) for name,weight,_ in fields] == [
            ('P4_plus',(0,2)),('P4_zero',(0,0)),('P4_minus',(0,-2))]
        del payload
        for path in (__file__,e4.__file__,p4check.__file__,control_path,vectors_path):
            hashes[str(path)] = lower.sha(path)
        result = {'status':'running','source_sha256':hashes,'expected_targets':90,
                  'passed_targets':0,'relations':[],'current_basis':current_basis,
                  'input_sparse_terms':input_terms,
                  'scope':'Exact A_n P4 membership in the actual saved K,S2,S3 spaces. A nonzero residual is a complete exact witness outside that space.'}
        for mode in (4,3,2):
            grade = 5-mode
            for op,operator in enumerate(ops):
                op_weights = {x.weight(s) for s in operator}
                assert len(op_weights) == 1
                ow = op_weights.pop()
                for name,pw,vector in fields:
                    weight = tuple(a+b for a,b in zip(ow,pw))
                    target = bounded(x.mode(operator,mode,vector))
                    assert all(x.grade(s) == grade and x.weight(s) == weight for s in target)
                    residual = target.copy()
                    relation = []
                    for pivot,row_name in sorted(blocks[grade].get(weight,{}).items()):
                        c = residual.get(pivot,x.ZERO_A)
                        if c:
                            assert lower.bits(c) <= 4096
                            relation.append([row_name,lower.coefficient(c)])
                            lower.subtract(residual,c,rows[row_name])
                    record = {'operator':op,'mode':mode,'input':name,'target_grade':grade,
                              'weight':weight,'target_terms':len(target),'relation':relation,
                              'target_sha256':hashlib.sha256(lower.text(lower.packed(target)).encode()).hexdigest(),
                              'exact_residual_zero':not residual,'residual':lower.packed(residual)}
                    result['relations'].append(record)
                    result['seconds'] = monotonic()-started
                    result['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
                    if residual:
                        result['status'] = 'exact_positive_mode_leaves_saved_lower_space'
                        write(output,result)
                        print({'status':result['status'],'witness':{k:v for k,v in record.items() if k not in ('relation','residual')}},flush=True)
                        return
                    result['passed_targets'] += 1
                write(output,result)
            print({'mode':mode,'passed_targets':result['passed_targets'],
                   'seconds':monotonic()-started},flush=True)
        assert result['passed_targets'] == 90
        if not grade4_controls(args,fields,ops,control,hashes,result,output,started):
            return
        result['status'] = 'all_90_exact_positive_and_30_prime_grade4_modes_passed'
        result['scope'] += ' The30 grade-four checks are finite-prime containments only; they are not characteristic-zero membership certificates.'
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
