"""Exact identities for a closed finite-prime N5 highest-projection pilot.

Raw normal words are lifted by the frozen exact selected-N5 provider. The
recorded current-zero projector is reconstructed over the number field,
then selected small pivot solves are checked by full sparse residuals.
"""
import argparse
from collections import OrderedDict
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_next_n5_exact_selected as raw

b = raw.b
MIB = 1024**2
FORMAT = 'exact-selected-N5-highest-relations-v1'


def factors_for(weight):
    factors = []
    for axis,w,bound,e,f in zip(('LEFT','RIGHT'),weight,(4,27),(1,4),(2,5)):
        assert 0 <= w <= bound
        for higher in range(w+2,bound+1,2):
            numerator = (higher-w)*(higher+w+2)
            assert numerator % 4 == 0
            eigenvalue = numerator//4
            assert eigenvalue > 0
            factors.append({'axis':axis,'current_E':e,'current_F':f,'weight':w,
                'higher_weight':higher,'eigenvalue':eigenvalue,'numerator':-1,
                'denominator':eigenvalue,
                'coefficient_mod_prime':(-pow(eigenvalue,-1,b.PRIME))%b.PRIME})
    return factors


class Consumer(raw.ExactSelected):
    def __init__(self,args):
        self.args,self.started = args,monotonic()
        self.last_save = self.started
        self.output = Path(args.output)
        self.path = self.output.with_suffix('.sqlite')
        source_path = Path(args.database).resolve()
        assert source_path.stat().st_size <= 512*MIB
        assert not Path(str(source_path)+'-journal').exists(),'Close the prime projector first'
        self.source = sqlite3.connect(source_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.source.execute('PRAGMA cache_size=-4096')
        self.source.execute('PRAGMA mmap_size=0')
        self.pm = json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.pm['format'] == 'selected-n5-highest-prime-v1'
        assert self.pm['prime'] == b.PRIME
        self.weight = tuple(self.pm['weight'])
        assert len(self.weight) == 2 and self.pm['bounds'] == [4,27]
        self.factors = factors_for(self.weight)
        assert self.pm['factors'] == self.factors
        bindings = dict(self.pm['source_sha256'])
        for filename,digest in bindings.items():
            assert b.sha(filename) == digest,filename
        bindings[str(source_path)] = b.sha(source_path)
        summary_path = Path(args.source_summary).resolve()
        summary = b.load_json(summary_path)
        for key in ('format','source_sha256','weight','factors','cursor','normal_rank',
                    'targets_ready','target_count'):
            assert summary[key] == self.pm[key]
        assert self.pm['targets_ready']
        bindings[str(summary_path)] = b.sha(summary_path)
        for filename in (__file__,raw.__file__):
            bindings[str(Path(filename).resolve())] = b.sha(filename)
        raw_output = self.output.with_suffix('.raw.json')
        grade4_output = raw_output.with_suffix('.grade4.json')
        protected = {Path(filename).resolve() for filename in bindings}
        protected.update(Path(filename).resolve() for filename in
            (self.pm['raw_source_database'],self.pm['raw_source_summary'],args.grade4_database,args.p4_controls))
        for derived in (self.output,self.path,raw_output,raw_output.with_suffix('.sqlite'),
                        grade4_output,grade4_output.with_suffix('.sqlite')):
            assert derived.resolve() not in protected,'Derived output would overwrite a source'
        raw_args = argparse.Namespace(database=self.pm['raw_source_database'],
            source_summary=self.pm['raw_source_summary'],grade4_database=args.grade4_database,
            p4_controls=args.p4_controls,output=str(raw_output),
            weight=None,max_rank=300,seconds=args.seconds)
        self.raw = raw.ExactSelected(raw_args)
        for filename,digest in self.raw.meta['source_sha256'].items():
            assert filename not in bindings or bindings[filename] == digest
            bindings[filename] = digest
        self.currents,self.flint = self.raw.currents,self.raw.flint
        self.states = {}
        for idx,value in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx == len(self.states) and idx < 120000
            a,o = json.loads(value)
            state = (tuple(a),tuple(o))
            assert b.x.grade(state) == 5 and b.x.weight(state) == self.weight
            self.states[idx] = state
        assert len(self.states) == self.pm['known_grade5_states']
        self.blocks = {self.weight:[]}
        for idx,source_id,w0,w1,pivot in self.source.execute('SELECT id,source_id,w0,w1,pivot FROM rows ORDER BY id'):
            assert idx == len(self.blocks[self.weight])
            assert (w0,w1) == self.weight and source_id >= 0
            assert pivot in self.states
            self.blocks[self.weight].append((idx,self.states[pivot]))
        assert len(self.blocks[self.weight]) == self.pm['normal_rank']
        self.targets = []
        for idx,source_id,w0,w1,word_json in self.source.execute('SELECT id,source_id,w0,w1,word FROM targets ORDER BY id'):
            assert idx == len(self.targets)
            word = json.loads(word_json)
            assert (w0,w1) == self.weight and word['source5_target'] == source_id
            assert word['kind'] == 'joint_highest_projection' and word['factors'] == self.factors
            assert tuple(word['weight']) == self.weight
            self.targets.append((idx,self.weight,word))
        assert 0 < len(self.targets) <= 3 and len(self.targets) == self.pm['target_count']
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
                'exact_highest_target_checks':{},'raw_provider_file':str(self.raw.path)}
        self.save('exact projected N5 consumer initialized')

    def cache_put(self,name,vector,bits):
        cost = len(vector)*(512+8*((bits+7)//8))+4096
        while self.cache and self.cache_bytes+cost > 64*MIB:
            _,(_,previous) = self.cache.popitem(last=False)
            self.cache_bytes -= previous
        if cost <= 64*MIB:
            self.cache[name] = (vector,cost)
            self.cache_bytes += cost

    def save(self,reason,status='running'):
        self.meta.update({'status':status,'seconds_this_call':monotonic()-self.started,
            'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'scope':'Exact projected-target identities in projected actual normal words. No ambient rank upper bound. Recovering unprojected families requires the stated current-equivariance and Clebsch-Gordan argument.',
            'native_solver':{'library':'FLINT','version':self.flint.version,'threads':1},
            'source_target_words':[word for _,_,word in self.targets]})
        self.meta['history'].append({'reason':reason,'verified_targets':self.meta['verified_targets'],
            'failed_targets':self.meta['failed_targets'],'seconds_this_call':monotonic()-self.started})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(b.compact(self.meta),))
        self.db.commit()
        temporary = self.output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump({**self.meta,'sqlite_file':str(self.path)},stream,indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.output)
        b.clear_modes()
        self.last_save = monotonic()
        print({'status':status,'reason':reason,'verified_targets':self.meta['verified_targets'],
               'weight':self.weight,'seconds':monotonic()-self.started},flush=True)

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
        source_id,word_json,blob,digest = self.source.execute(
            f'SELECT source_id,word,raw,digest FROM {table} WHERE id=?',(idx,)).fetchone()
        word = json.loads(word_json)
        source_key = 'source5_row' if kind == 'grade5' else 'source5_target'
        assert word['kind'] == 'joint_highest_projection' and word[source_key] == source_id
        assert word['factors'] == self.factors and tuple(word['weight']) == self.weight
        source_word, = self.raw.source.execute(f'SELECT word FROM {table} WHERE id=?',(source_id,)).fetchone()
        assert word['source_word'] == json.loads(source_word)
        vector = self.raw.vector(kind+':'+str(source_id))
        for factor in self.factors:
            raised = b.x.mode(self.currents[factor['current_E']],0,vector)
            assert len(raised) <= raw.MAX_TERMS
            assert max((b.height(c) for c in raised.values()),default=0) <= b.VECTOR_BITS
            self.boundary()
            feedback = b.x.mode(self.currents[factor['current_F']],0,raised)
            assert len(feedback) <= raw.MAX_TERMS
            assert max((b.height(c) for c in feedback.values()),default=0) <= b.VECTOR_BITS
            self.boundary()
            coefficient = b.fast.FastField(-1)/factor['eigenvalue']
            out = dict(vector)
            for state,value in feedback.items():
                b.x.add(out,state,coefficient*value)
            vector = out
            del raised,feedback
            assert len(vector) <= raw.MAX_TERMS
            assert max((b.height(c) for c in vector.values()),default=0) <= b.VECTOR_BITS
            self.boundary()
        assert all(b.x.grade(s) == 5 and b.x.weight(s) == self.weight for s in vector)
        expected = {self.states[i]:c for i,c in raw.unpack(blob,digest)}
        actual = {s:residue for s,c in vector.items() if (residue:=b.specialization(c))}
        assert actual == expected,('Exact projector disagrees with saved prime vector',name)
        if kind == 'target':
            assert not b.x.mode(self.currents[1],0,vector)
            assert not b.x.mode(self.currents[4],0,vector)
            self.meta['exact_highest_target_checks'][str(idx)] = True
        return self.store(name,vector)

    def close(self,rollback=False):
        if rollback:
            self.db.rollback()
        self.db.close()
        self.source.close()
        self.raw.close(rollback)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',required=True)
    parser.add_argument('--source-summary',required=True)
    parser.add_argument('--grade4-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--p4-controls',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--output',required=True)
    parser.add_argument('--max-rank',type=int,default=64)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    args.weight = None
    assert 0 < args.max_rank <= 300 and 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('exact projected N5 Python alarm')))
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
        print({'status':'interrupted','action':'Prior exact projected N5 checkpoints retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.close(rollback)


if __name__ == '__main__':
    main()
