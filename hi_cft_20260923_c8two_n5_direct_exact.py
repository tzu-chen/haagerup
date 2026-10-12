"""Exact replay of directly projected N5 normal recipes; root-only.

There is no ordinary-N5 basis provider. Every accepted projected column is
lifted from its original normal recipe, checked modulo the pilot prime, and
used in a native pivot solve followed by a full exact sparse residual.
The root launcher must impose an external timeout around native FLINT.
"""
import argparse
from collections import OrderedDict
import hashlib
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_next_n5_projected_exact as projected
import hi_cft_20260923_next_exact_mode_cache as action_cache

raw,b = projected.raw,projected.b
MIB = 1024**2
FORMAT = 'exact-direct-normal-N5-highest-relations-v1'


def residue_digest(vector):
    record = [[list(s[0]),list(s[1]),residue] for s,c in sorted(vector.items())
              if (residue := b.specialization(c))]
    data = b.compact(record).encode()
    assert len(data) <= 16*MIB
    return hashlib.sha256(data).hexdigest()


class Consumer(projected.Consumer):
    def __init__(self,args):
        self.args,self.started = args,monotonic()
        self.last_save = self.started
        self.output,self.path = Path(args.output),Path(args.output).with_suffix('.sqlite')
        source_path,summary_path = Path(args.database).resolve(),Path(args.source_summary).resolve()
        assert source_path.stat().st_size <= 512*MIB
        assert not Path(str(source_path)+'-journal').exists(),'Close the direct prime producer first'
        self.source = sqlite3.connect(source_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.source.execute('PRAGMA cache_size=-4096')
        self.source.execute('PRAGMA mmap_size=0')
        self.pm = json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.pm['format'] == 'direct-normal-N5-highest-prime-v1'
        assert self.pm['prime'] == b.PRIME and self.pm['roots'] == [231543,1000]
        assert self.pm['targets_ready'] and 0 < self.pm['target_count'] <= 3
        self.weight = tuple(self.pm['weight'])
        assert len(self.weight) == 2 and self.pm['bounds'] == [4,27]
        self.factors = projected.factors_for(self.weight)
        assert self.pm['factors'] == self.factors
        bindings = dict(self.pm['source_sha256'])
        for filename,digest in bindings.items():
            assert b.sha(filename) == digest,filename
        summary = b.load_json(summary_path)
        for key in ('format','source_sha256','input_paths','weight','factors','cursor',
                    'normal_rank','targets_ready','target_count','task_digest','target_digest'):
            assert summary[key] == self.pm[key]
        bindings[str(source_path)],bindings[str(summary_path)] = b.sha(source_path),b.sha(summary_path)
        for filename in (__file__,projected.__file__,raw.__file__,raw.h4.__file__,b.__file__,
                         raw.modes.__file__,raw.h4.native.__file__,action_cache.__file__):
            bindings[str(Path(filename).resolve())] = b.sha(filename)
        self.states = {}
        for idx,value in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx == len(self.states) and idx < 120000
            a,o = json.loads(value)
            state = (tuple(a),tuple(o))
            assert b.x.grade(state) == 5 and b.x.weight(state) == self.weight
            self.states[idx] = state
        assert len(self.states) == len(set(self.states.values())) == self.pm['known_grade5_states']
        self.blocks = {self.weight:[]}
        for idx,source_id,w0,w1,pivot in self.source.execute('SELECT id,source_id,w0,w1,pivot FROM rows ORDER BY id'):
            assert idx == len(self.blocks[self.weight]) and 0 <= source_id < self.pm['cursor']
            assert (w0,w1) == self.weight and pivot in self.states
            self.blocks[self.weight].append((idx,self.states[pivot]))
        assert len(self.blocks[self.weight]) == self.pm['normal_rank'] <= 300
        self.targets = []
        for idx,source_id,w0,w1,word_json in self.source.execute('SELECT id,source_id,w0,w1,word FROM targets ORDER BY id'):
            assert idx == source_id == len(self.targets) and (w0,w1) == self.weight
            word = json.loads(word_json)
            self.validate_word(word)
            assert word['normal_recipe'] == self.pm['target_recipes'][idx]
            assert word['normal_recipe']['kind'] == 'S2_zero_P4_canonical'
            self.targets.append((idx,self.weight,word))
        assert len(self.targets) == self.pm['target_count']
        assert self.source.execute('SELECT COUNT(*) FROM projections').fetchone()[0] == self.pm['cursor']

        paths = self.pm['input_paths']
        grade4_path = Path(paths['grade4_database']).resolve()
        p4_path = Path(paths['p4_summary']).resolve()
        resolved = {str(Path(path).resolve()):digest for path,digest in bindings.items()}
        assert resolved[str(grade4_path)] == b.sha(grade4_path)
        assert resolved[str(p4_path)] == b.sha(p4_path)
        provider_output = self.output.with_suffix('.grade4.json')
        protected = {Path(filename).resolve() for filename in bindings}
        for filename in (self.output,self.path,self.output.with_suffix('.json.tmp'),
                         provider_output,provider_output.with_suffix('.sqlite'),provider_output.with_suffix('.json.tmp')):
            assert filename.resolve() not in protected,'Derived output would overwrite an authenticated source'
        connection = sqlite3.connect(grade4_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        try:
            assert not Path(str(grade4_path)+'-journal').exists()
            w0,w1 = connection.execute('SELECT w0,w1 FROM rows GROUP BY w0,w1 ORDER BY COUNT(*),w0,w1 LIMIT 1').fetchone()
        finally:
            connection.close()
        provider_args = argparse.Namespace(database=str(grade4_path),p4_controls=str(p4_path),
            weight=f'{w0},{w1}',output=str(provider_output),max_rank=300,max_targets=0,batch=3,seconds=args.seconds)
        self.provider = raw.h4.Consumer(provider_args)
        for graph in (self.provider.meta['source_sha256'],
                      self.provider.meta['H4_extension_source_sha256']):
            for filename,digest in graph.items():
                assert filename not in bindings or bindings[filename] == digest
                bindings[filename] = digest
        extension = {'format':'direct-N5-grade4-provider-v1','source_sha256':bindings}
        previous = self.provider.meta.get('direct_N5_provider_extension')
        if previous is None:
            assert not self.provider.meta['verified_targets'] and not self.provider.meta['failed_targets']
            self.provider.meta['direct_N5_provider_extension'] = extension
            self.provider.save('Direct N5 exact recipe provider bound')
        else:
            assert previous == extension
        self.p4 = {info['id']:self.provider.p4[key] for key,info in self.provider.p4_info.items()}
        assert set(self.p4) == {'P4_plus','P4_zero','P4_minus'}
        self.ops,self.currents,self.omega = self.provider.ops,self.provider.currents,self.provider.omega
        self.flint = self.provider.flint
        self.mode_cache = action_cache.ExactModeCache(b.x,b.fast.FastField,max_bytes=128*MIB,max_entries=20000)
        for field in [*self.ops,*self.currents,self.omega]:
            self.mode_cache.register(field)

        self.db = sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-4096')
        self.db.execute('PRAGMA temp_store=FILE')
        self.db.execute('PRAGMA mmap_size=0')
        assert self.db.execute('PRAGMA page_size').fetchone()[0] == 4096
        self.db.execute('PRAGMA max_page_count=131072')
        self.db.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS vectors (name TEXT PRIMARY KEY,record BLOB,digest TEXT,terms INTEGER,bits INTEGER)')
        self.db.execute('CREATE TABLE IF NOT EXISTS relations (id INTEGER PRIMARY KEY,record BLOB,digest TEXT,passed INTEGER)')
        self.db.commit()
        self.cache,self.cache_bytes = OrderedDict(),0
        previous = self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if previous:
            self.meta = json.loads(previous[0])
            assert self.meta['format'] == FORMAT and self.meta['source_sha256'] == bindings
            assert tuple(self.meta['weight']) == self.weight and self.meta['factors'] == self.factors
            assert self.db.execute('SELECT COUNT(*) FROM relations').fetchone()[0] == self.meta['verified_targets']+self.meta['failed_targets']
        else:
            assert not self.db.execute('SELECT 1 FROM vectors LIMIT 1').fetchone()
            self.meta = {'format':FORMAT,'source_sha256':bindings,'weight':self.weight,
                'factors':self.factors,'bounds':[4,27],'saved_terms':0,
                'verified_targets':0,'failed_targets':0,'target_count':len(self.targets),
                'status':'running','history':[],'largest_vector_bits':0,
                'largest_relation_bits':0,'completed_blocks':[],
                'exact_highest_target_checks':{},'provider_file':str(self.provider.path)}
        self.oracle_controls()
        b.x.mode = self.mode_cache.mode
        self.save('Exact direct projected N5 consumer initialized')

    def validate_word(self,word):
        assert word['kind'] == 'direct_normal_highest_projection'
        assert word['factors'] == self.factors and tuple(word['weight']) == self.weight
        assert tuple(word['normal_recipe']['weight']) == self.weight
        assert len(word['unprojected_sha256']) == 64

    def oracle_controls(self):
        state = next(iter(self.states.values()),((0,)*8,(0,)*5))
        assert b.x.grade(state) == 5
        records = []
        for index,current in enumerate(self.currents):
            for scalar in (b.fast.ONE,b.fast.FastField((1,1,0,0))):
                right = {state:scalar}
                expected = self.mode_cache.original_mode(current,0,right)
                actual = self.mode_cache.mode(current,0,right)
                assert actual == expected
                records.append({'current':index,'scalar':[str(q) for q in scalar],
                                'terms':len(actual),'specialization_sha256':residue_digest(actual)})
        assert self.mode_cache.statistics()['basis_hits'] > 0
        self.meta['original_mode_oracle_controls'] = records

    def bounded(self,vector):
        assert len(vector) <= raw.MAX_TERMS
        assert max((b.height(c) for c in vector.values()),default=0) <= b.VECTOR_BITS
        self.boundary()
        return vector

    def ordinary(self,word,kind):
        if word['kind'] == 'S2_zero_P4_canonical':
            assert kind == 'target' and word['mode'] == 0 and word['source4_table'] == 'P4'
            assert 0 <= word['operator'] <= 8
            left,right,n = self.ops[word['operator']],self.source4(word),0
        elif word['kind'] == 'grade4_descendant':
            assert kind == 'grade5'
            op = word['operator']
            assert 0 <= op < 7 and word['mode'] == (-1 if op < 6 else 0)
            left,right,n = self.currents[op] if op < 6 else self.omega,self.source4(word),word['mode']
        else:
            assert kind == 'grade5' and word['kind'] == 'S2_minus1_S3' and word['mode'] == -1
            assert word['exact_left'] in self.provider.frozen['order']['2']
            assert word['exact_right'] in self.provider.frozen['order']['3']
            left = self.provider.vector('input:'+word['exact_left'])
            right = self.provider.vector('input:'+word['exact_right'])
            n = -1
        return self.bounded(b.x.mode(left,n,right))

    def vector(self,name):
        if name in self.cache:
            self.cache.move_to_end(name)
            return self.cache[name][0]
        previous = self.db.execute('SELECT record,digest,terms,bits FROM vectors WHERE name=?',(name,)).fetchone()
        if previous:
            blob,digest,terms,bits = previous
            record = raw.unpack(blob,digest)
            assert len(record) == terms <= raw.MAX_TERMS and bits <= b.VECTOR_BITS
            vector = {(tuple(a),tuple(o)):b.fast.FastField(c) for a,o,c in record}
            assert len(vector) == terms
            self.cache_put(name,vector,bits)
            return vector
        kind,idx = name.split(':')
        idx = int(idx)
        assert kind in ('grade5','target')
        table = 'rows' if kind == 'grade5' else 'targets'
        word_json,blob,digest = self.source.execute(f'SELECT word,raw,digest FROM {table} WHERE id=?',(idx,)).fetchone()
        word = json.loads(word_json)
        self.validate_word(word)
        vector = self.ordinary(word['normal_recipe'],kind)
        assert all(b.x.grade(s) == 5 and b.x.weight(s) == self.weight for s in vector)
        assert residue_digest(vector) == word['unprojected_sha256'],('Ordinary recipe digest mismatch',name)
        for factor in self.factors:
            raised = self.bounded(b.x.mode(self.currents[factor['current_E']],0,vector))
            feedback = self.bounded(b.x.mode(self.currents[factor['current_F']],0,raised))
            coefficient = b.fast.FastField(-1)/factor['eigenvalue']
            out = dict(vector)
            for state,value in feedback.items():
                b.x.add(out,state,coefficient*value)
            del raised,feedback
            vector = self.bounded(out)
        expected = {self.states[i]:c for i,c in raw.unpack(blob,digest)}
        actual = {s:residue for s,c in vector.items() if (residue:=b.specialization(c))}
        assert actual == expected,('Projected recipe specialization mismatch',name)
        if kind == 'target':
            assert not self.bounded(b.x.mode(self.currents[1],0,vector))
            assert not self.bounded(b.x.mode(self.currents[4],0,vector))
            self.meta['exact_highest_target_checks'][str(idx)] = True
        return self.store(name,vector)

    def save(self,reason,status='running'):
        self.meta['exact_action_cache'] = self.mode_cache.statistics()
        super().save(reason,status)

    def close(self,rollback=False):
        b.x.mode = self.mode_cache.original_mode
        raw.ExactSelected.close(self,rollback)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',required=True)
    parser.add_argument('--source-summary',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--max-rank',type=int,default=300)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    args.weight = None
    assert 0 < args.max_rank <= 300 and 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('Direct N5 exact Python alarm')))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    raw.installed_modes()
    consumer,rollback = None,False
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
        rollback = True
        if consumer is None:
            raise
        print({'status':'interrupted','action':'Prior direct N5 exact checkpoints retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.close(rollback)


if __name__ == '__main__':
    main()
