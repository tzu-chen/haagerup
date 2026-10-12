"""Root-only exact A0P3 relations using normal words and the exact P4 triplet.

The frozen one-block consumer supplies raw DAG reconstruction and storage.
This extension binds separate sources, adds at most one exact P4 column
per Cartan block, batches exact FLINT solves, and checks full residuals.
Initial reviewed gate: rank64, batch8, AS3GiB,600s. Larger blocks need a
separate allocation review; the CLI is not authorization for larger jobs.
"""
import argparse
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import resource
import signal

import hi_cft_20260923_next_n4_exact_block as b
import hi_cft_20260923_next_flint_field_solve as native


class Consumer(b.Consumer):
    def __init__(self,args):
        controls = Path(args.p4_controls)
        control = b.load_json(controls)
        assert control['status'] == 'exact_P4_triplet_and_lower_controls_passed'
        vectors = Path(control['vectors_file'])
        assert b.sha(vectors) == control['vectors_sha256']
        with gzip.open(vectors,'rb') as stream:
            raw = stream.read(32*b.MIB+1)
            assert len(raw) <= 32*b.MIB and not stream.read(1)
        payload = json.loads(raw)
        del raw
        assert payload['format'] == 'exact-p4-triplet-v1'
        for path,digest in payload['source_sha256'].items():
            assert b.sha(path) == digest
        assert payload['source_sha256'] == control['source_sha256']
        native_control = Path('hi_cft_20260923_next_flint_field_check.json')
        checked = b.load_json(native_control)
        assert checked['status'] == 'exact_flint_regular_representation_controls_passed'
        for path,digest in checked['source_sha256'].items():
            assert b.sha(path) == digest
        extra_sources = {str(p):b.sha(p) for p in
                         (Path(__file__).resolve(),Path(native.__file__).resolve(),controls,vectors,native_control)}
        self.p4 = {}
        self.p4_info = {}
        assert len(payload['fields']) == 3
        for index,field in enumerate(payload['fields']):
            key = -1-index
            assert field['grade'] == 4
            vector = {(tuple(a),tuple(o)):b.fast.FastField(c) for a,o,c in field['vector']}
            weight = tuple(field['weight'])
            assert vector and len(vector) <= 12000
            assert all(b.x.grade(s) == 4 and b.x.weight(s) == weight for s in vector)
            self.p4[key] = vector
            self.p4_info[key] = {'id':field['id'],'weight':weight}
        del payload
        self.flint = native.Flint()
        super().__init__(args)
        # The frozen base intentionally records only its original normal
        # columns. Detach both lists before adding the external P4 column.
        self.meta['columns'] = list(self.meta['columns'])
        self.columns = list(self.columns)
        if 'H4_extension_source_sha256' in self.meta:
            assert self.meta['H4_extension_source_sha256'] == extra_sources
        else:
            assert self.meta['verified_targets'] == 0 and self.meta['failed_targets'] == 0
            self.meta['H4_extension_source_sha256'] = extra_sources
        self.meta['P4_columns'] = {str(k):v for k,v in self.p4_info.items()}
        self.meta['solver'] = {'library':'FLINT','version':self.flint.version,
                               'arithmetic':'exact rational regular representation of K',
                               'threads':1,'batch':args.batch}
        for key,info in self.p4_info.items():
            if info['weight'] == self.weight:
                extras = list(self.pilot.execute('SELECT pivot FROM extras WHERE w0=? AND w1=?',self.weight))
                assert len(extras) == 1
                state = self.state_ids[extras[0][0]]
                assert state not in self.pivot_states
                self.columns.append(key)
                self.pivot_states.append(state)
        self.r = len(self.columns)
        assert 0 < self.r <= args.max_rank <= 300
        if 'extended_columns' in self.meta:
            assert self.meta['extended_columns'] == self.columns
        self.meta['extended_columns'] = list(self.columns)
        self.meta['extended_rank'] = self.r
        self.save('H4 exact triplet columns and native solver bound')

    def vector(self,name):
        if name.startswith('normal:') and int(name.split(':')[1]) < 0:
            return self.p4[int(name.split(':')[1])]
        return super().vector(name)

    def verify_ready(self,op,name,target,coefficients):
        assert len(coefficients) == self.r
        assert max((b.height(c) for c in coefficients),default=0) <= b.MATRIX_BITS
        residual = dict(target)
        for idx,c in zip(self.columns,coefficients):
            if c:
                for state,value in self.vector('normal:'+str(idx)).items():
                    b.x.add(residual,state,-c*value)
            self.boundary()
        target_record = [[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(target.items())]
        record = {'word':{'operator':op,'mode':0,'exact_input':name},
                  'normal_word_coefficients':[[idx,[str(q) for q in c]] for idx,c in zip(self.columns,coefficients) if c],
                  'negative_columns_are_exact_P4_fields':True,
                  'target_sha256':hashlib.sha256(b.compact(target_record).encode()).hexdigest(),
                  'target_terms':len(target),'exact_residual_zero':not residual,
                  'residual':[[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(residual.items())]}
        blob,digest = b.pack(record)
        key = 'A%d_zero_%s'%(op,name)
        self.db.execute('INSERT INTO relations VALUES (?,?,?,?)',(key,blob,digest,int(not residual)))
        self.meta['verified_targets' if not residual else 'failed_targets'] += 1
        self.save('full exact H4 sparse identity checked')
        if residual:
            raise b.BudgetStop('Target outside chosen exact H4 column subset; no full-span upper bound claimed')

    def run(self):
        selected = self.targets[:self.args.max_targets] if self.args.max_targets else self.targets
        pending = []
        for op,name in selected:
            key = 'A%d_zero_%s'%(op,name)
            previous = self.db.execute('SELECT passed FROM relations WHERE name=?',(key,)).fetchone()
            if previous:
                assert previous[0]
            else:
                pending.append((op,name))
        matrix = self.matrix() if pending else None
        for start in range(0,len(pending),self.args.batch):
            words = pending[start:start+self.args.batch]
            targets = []
            for op,name in words:
                target = b.x.mode(self.ops[op],0,self.vector('input:'+name))
                assert len(target) <= b.MAX_TERMS
                assert all(b.x.grade(s) == 4 and b.x.weight(s) == self.weight for s in target)
                assert max((b.height(c) for c in target.values()),default=0) <= b.VECTOR_BITS
                targets.append(target)
                self.boundary()
            rhs = [[target.get(s,b.fast.ZERO) for target in targets] for s in self.pivot_states]
            coefficients = self.flint.solve(matrix,rhs)
            self.meta['selected_exact_minor_invertible'] = True
            for j,((op,name),target) in enumerate(zip(words,targets)):
                self.verify_ready(op,name,target,[row[j] for row in coefficients])
            del targets,rhs,coefficients
        self.meta['all_block_targets_count'] = len(self.targets)
        self.meta['all_block_targets_verified'] = self.meta['verified_targets'] == len(self.targets)
        self.save('selected H4 block targets completed','complete' if self.meta['all_block_targets_verified'] else 'partial_complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--p4-controls',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--weight',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--max-rank',type=int,default=64)
    parser.add_argument('--max-targets',type=int,default=0)
    parser.add_argument('--batch',type=int,default=8)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900 and 0 <= args.max_targets <= 400
    assert 1 <= args.batch <= 16
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    b.x.creation = lru_cache(maxsize=128)(b.e4.creation.__wrapped__)
    b.e4.creation = b.x.creation
    b.x.vertex = lru_cache(maxsize=256)(b.e4.vertex.__wrapped__)
    b.x.basis_mode = lru_cache(maxsize=256)(b.e4.basis_mode.__wrapped__)
    consumer = None
    try:
        consumer = Consumer(args)
        consumer.run()
    except b.BudgetStop as error:
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.db.rollback()
        print({'status':'interrupted','action':'prior committed exact vectors and identities retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close()
            consumer.pilot.close()


if __name__ == '__main__':
    main()
