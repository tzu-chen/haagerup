"""Root-only serial exact H4 block certificate; no workers or subprocesses.

Nine primitive left families suffice by the independently proved neutral
stress identity. Each block retains the frozen H4 consumer's complete
sparse identity checks. Empty-column blocks require exact zero targets.
"""
import argparse
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_next_n4_h4_flint as h

b = h.b


def atomic_json(path, value):
    path = Path(path)
    temporary = path.with_suffix('.json.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def plan(args):
    path = Path(args.database).resolve()
    assert not Path(str(path)+'-journal').exists()
    source = sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1', uri=True)
    try:
        pm = json.loads(source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert pm['normal_span_complete'] and pm['normal_rank'] == 6007
        assert pm['extra_rank'] == 3 and pm['union_rank_lower_bound'] == 6010
        for filename, digest in pm['source_sha256'].items():
            assert b.sha(filename) == digest
        ranks = {(w0, w1): count for w0, w1, count in
                 source.execute('SELECT w0,w1,COUNT(*) FROM rows GROUP BY w0,w1')}
    finally:
        source.close()
    manifest_path = Path(pm['checkpoint_manifest'])
    frozen = b.load_json(manifest_path)
    assert frozen['completed_grade3'] and frozen['dimensions']['3'] == 956
    p3 = set(frozen['order']['3'][634:])
    assert len(p3) == 322
    weights = {}
    for filename in frozen['block_files']:
        if filename.startswith('grade3_'):
            filename_path = manifest_path.parent/filename
            assert b.sha(filename_path) == frozen['files_sha256'][filename]
            for row in b.row_stream(filename_path):
                if row['id'] in p3:
                    assert row['id'] not in weights
                    weights[row['id']] = tuple(row['weight'])
    assert set(weights) == p3
    fields = b.load_json('hi_cft_20260923_c8_exact_fields.json')['fields']
    operators = [b.x.read_field(row) for row in fields[:-1]]
    neutral = b.x.read_field(fields[-1])
    operators += [neutral, b.x.vadd((1,b.x.omega()),(-1,b.x.sugawara(b.x.LEFT,1)),
                                  (-1,b.x.sugawara(b.x.RIGHT,39)),(-1,neutral))]
    assert len(operators) == 10
    op_weights = []
    for vector in operators:
        ws = {b.x.weight(s) for s in vector}
        assert len(ws) == 1
        op_weights.append(ws.pop())
    groups = {}
    for op in args.operators:
        for name in frozen['order']['3'][634:]:
            weight = tuple(a+c for a,c in zip(op_weights[op],weights[name]))
            groups.setdefault(weight,[]).append((op,name))
    p4_weights = {(0,2),(0,0),(0,-2)}
    nonzero, zero = [], []
    for weight, targets in groups.items():
        rank = ranks.get(weight,0)
        if weight in p4_weights:
            assert rank > 0
            rank += 1
        if rank:
            assert rank <= args.max_rank, ('Unreviewed block rank',weight,rank)
            nonzero.append({'weight':weight,'rank':rank,'targets':targets})
        else:
            zero.extend((op,name,weight) for op,name in targets)
    nonzero.sort(key=lambda row:(row['rank'],row['weight']))
    assert nonzero and sum(len(row['targets']) for row in nonzero)+len(zero) == 322*len(args.operators)
    bindings = {str(Path(__file__).resolve()):b.sha(__file__),
                str(Path(h.__file__).resolve()):b.sha(h.__file__),
                str(path):b.sha(path),str(manifest_path):b.sha(manifest_path)}
    controls_path = Path(args.p4_controls).resolve()
    controls = b.load_json(controls_path)
    assert controls['status'] == 'exact_P4_triplet_and_lower_controls_passed'
    vectors_path = Path(controls['vectors_file']).resolve()
    assert b.sha(vectors_path) == controls['vectors_sha256']
    bindings[str(controls_path)] = b.sha(controls_path)
    bindings[str(vectors_path)] = controls['vectors_sha256']
    return nonzero, zero, bindings


class Consumer(h.Consumer):
    def __init__(self,args,policy):
        super().__init__(args)
        self.targets = [(op,name) for op,name in self.targets if op in args.operators]
        previous = self.meta.get('serial_bulk_policy')
        if previous is not None:
            assert previous == policy
        else:
            assert not self.meta['verified_targets'] and not self.meta['failed_targets']
            self.meta['serial_bulk_policy'] = policy
        self.db.execute('CREATE TABLE IF NOT EXISTS zero_relations (name TEXT PRIMARY KEY,record BLOB,digest TEXT,passed INTEGER)')
        self.meta.setdefault('zero_targets_verified',0)
        self.save('serial exact block policy authenticated')

    def verify_zeros(self,words):
        self.meta['zero_targets_expected'] = len(words)
        for op,name,weight in words:
            key = 'A%d_zero_%s'%(op,name)
            previous = self.db.execute('SELECT passed FROM zero_relations WHERE name=?',(key,)).fetchone()
            if previous:
                assert previous[0]
                continue
            target = b.x.mode(self.ops[op],0,self.vector('input:'+name))
            assert len(target) <= b.MAX_TERMS
            assert all(b.x.grade(s) == 4 and b.x.weight(s) == tuple(weight) for s in target)
            assert not target, ('Nonzero exact target in an empty selected block',op,name,weight)
            record = {'word':{'operator':op,'mode':0,'exact_input':name},
                      'weight':weight,'normal_columns':[],
                      'target_sha256':hashlib.sha256(b.compact([]).encode()).hexdigest(),
                      'exact_target_zero':True}
            blob,digest = b.pack(record)
            self.db.execute('INSERT INTO zero_relations VALUES (?,?,?,1)',(key,blob,digest))
            self.meta['zero_targets_verified'] += 1
            self.boundary()
        self.save('all empty-column targets verified exactly')


def tag(weight):
    return '_'.join(('m'+str(-n)) if n < 0 else 'p'+str(n) for n in weight)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--p4-controls',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--output-directory',default='hi_cft_20260923_next_h4_bulk')
    parser.add_argument('--operators',default='0,1,2,3,4,5,6,7,8')
    parser.add_argument('--max-rank',type=int,default=300)
    parser.add_argument('--batch',type=int,default=8)
    parser.add_argument('--seconds',type=int,default=300)
    args = parser.parse_args()
    args.operators = sorted(set(map(int,args.operators.split(','))))
    assert args.operators == list(range(9)) or args.operators == list(range(10))
    assert 0 < args.max_rank <= 300 and 1 <= args.batch <= 16
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    args.max_targets = 0
    output = Path(args.output_directory)
    output.mkdir(exist_ok=True)
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    b.x.creation = lru_cache(maxsize=128)(b.e4.creation.__wrapped__)
    b.e4.creation = b.x.creation
    b.x.vertex = lru_cache(maxsize=256)(b.e4.vertex.__wrapped__)
    b.x.basis_mode = lru_cache(maxsize=256)(b.e4.basis_mode.__wrapped__)
    started = monotonic()
    consumer = None
    summary = {'status':'initializing','blocks':[]}
    try:
        blocks, zeros, bindings = plan(args)
        policy = {'format':'serial-exact-h4-v1','source_sha256':bindings,
                  'operators':args.operators,'plan_sha256':hashlib.sha256(b.compact([blocks,zeros]).encode()).hexdigest(),
                  'omitted_neutral_family_derived_from_total_stress':args.operators == list(range(9))}
        summary.update({'status':'running','policy':policy,'expected_targets':322*len(args.operators),
                        'zero_targets':len(zeros),'block_count':len(blocks),
                        'largest_rank':max(row['rank'] for row in blocks)})
        atomic_json(output/'summary.json',summary)
        for index,row in enumerate(blocks):
            args.weight = ','.join(map(str,row['weight']))
            args.output = str(output/('block_'+tag(row['weight'])+'.json'))
            consumer = Consumer(args,policy)
            assert consumer.r == row['rank'] and consumer.targets == row['targets']
            if index == 0:
                consumer.verify_zeros(zeros)
            consumer.run()
            assert consumer.meta['all_block_targets_verified']
            summary['blocks'].append({'weight':row['weight'],'rank':row['rank'],
                                      'output':args.output,'verified_targets':consumer.meta['verified_targets']})
            if index == 0:
                summary['zero_targets_verified'] = consumer.meta['zero_targets_verified']
            consumer.db.close()
            consumer.pilot.close()
            consumer = None
            b.clear_modes()
            summary['seconds_this_call'] = monotonic()-started
            atomic_json(output/'summary.json',summary)
        total = sum(row['verified_targets'] for row in summary['blocks'])+summary.get('zero_targets_verified',0)
        assert total == summary['expected_targets']
        summary.update({'status':'all_selected_H4_relations_passed','verified_targets':total})
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if consumer is not None:
            consumer.db.rollback()
        summary['status'] = 'interrupted_exact_checkpoints_retained'
    except b.BudgetStop as error:
        signal.alarm(0)
        if consumer is not None:
            consumer.save(str(error),'bounded_stop')
        summary.update({'status':'bounded_stop','reason':str(error)})
    except AssertionError:
        summary['status'] = 'failed_assertion_no_complete_certificate'
        raise
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close()
            consumer.pilot.close()
        summary['seconds_this_call'] = monotonic()-started
        atomic_json(output/'summary.json',summary)
        print(summary,flush=True)


if __name__ == '__main__':
    main()
