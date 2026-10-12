"""Direct highest projection of selected N5 normal recipes; root-only."""
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

import hi_cft_20260923_c8two_n5_inputs as inputs
import hi_cft_20260923_next_n5_highest_prime as highest

old,p,helper = highest.old,highest.old.p,highest.helper
MIB = 1024**2
FORMAT = 'direct-normal-N5-highest-prime-v1'


def vector_digest(vector):
    rows = [[list(s[0]),list(s[1]),int(c)] for s,c in sorted(vector.items()) if c]
    data = old.compact(rows).encode()
    if len(data) > 16*MIB:
        raise p.Stop('16 MiB direct raw-vector digest serialization cap')
    return hashlib.sha256(data).hexdigest()


class Consumer(highest.Consumer):
    def __init__(self,args):
        self.args,self.started = args,monotonic()
        self.last_save = self.started
        self.output,self.path = Path(args.output),Path(args.output).with_suffix('.sqlite')
        self.weight = tuple(map(int,args.weight.split(',')))
        assert len(self.weight) == 2
        self.factors = highest.factors_for(self.weight)
        self.data = inputs.Inputs(args)
        self.currents = self.data.currents
        self.operators = sorted(set(map(int,args.operators.split(','))))
        assert self.operators and set(self.operators) <= set(range(9))
        self.target_words,self.tasks,counts = self.data.build_words(self.weight,self.operators,args.order)
        self.source_targets = list(range(len(self.target_words)))
        bindings = dict(self.data.hashes)
        for filename in (__file__,inputs.__file__,highest.__file__,helper.__file__):
            bindings[str(Path(filename).resolve())] = p.sha(filename)
        protected = {Path(filename).resolve() for filename in bindings}
        assert all(path.resolve() not in protected for path in
                   (self.output,self.path,self.output.with_suffix('.json.tmp')))
        self.mode_cache = helper.PrimeModeCache(p.x,p.PRIME,max_terms=300000,max_entries=50000)
        for field in [*self.currents,self.data.omega,*[v for v,_ in self.data.ops],
                      *[self.data.inputs[name] for name in self.data.frozen['order']['2']]]:
            self.mode_cache.register(field)
        assert self.mode_cache.statistics()['registered_left_fields'] <= 137
        self.db = sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-8192')
        self.db.execute('PRAGMA mmap_size=0')
        self.db.execute('PRAGMA temp_store=FILE')
        assert self.db.execute('PRAGMA page_size').fetchone()[0] == 4096
        self.db.execute('PRAGMA max_page_count=131072')
        self.db.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS states (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS rows (id INTEGER PRIMARY KEY,source_id INTEGER UNIQUE,w0 INTEGER,w1 INTEGER,pivot INTEGER,nnz INTEGER,raw BLOB,reduced BLOB,word TEXT,digest TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS targets (id INTEGER PRIMARY KEY,source_id INTEGER UNIQUE,w0 INTEGER,w1 INTEGER,raw BLOB,word TEXT,digest TEXT,residual BLOB)')
        self.db.execute('CREATE TABLE IF NOT EXISTS projections (source_id INTEGER PRIMARY KEY,raw_terms INTEGER,terms INTEGER,digest TEXT,accepted_rowid INTEGER)')
        self.db.commit()
        self.states,self.ids,self.pivots,self.info = [],{},{},[]
        self.row_cache,self.row_cache_terms = OrderedDict(),0
        task_digest = hashlib.sha256(old.compact(self.tasks).encode()).hexdigest()
        target_digest = hashlib.sha256(old.compact(self.target_words).encode()).hexdigest()
        previous = self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if previous:
            self.meta = json.loads(previous[0])
            assert self.meta['format'] == FORMAT and self.meta['source_sha256'] == bindings
            assert self.meta['task_digest'] == task_digest and self.meta['target_digest'] == target_digest
            assert tuple(self.meta['weight']) == self.weight and self.meta['factors'] == self.factors
            assert 0 <= self.meta['cursor'] <= len(self.tasks)
            for idx,value in self.db.execute('SELECT id,value FROM states ORDER BY id'):
                assert idx == len(self.states) and idx < 120000
                a,o = json.loads(value)
                state = (tuple(a),tuple(o))
                assert p.x.grade(state) == 5 and p.x.weight(state) == self.weight
                self.ids[state] = idx
                self.states.append(state)
            assert len(self.ids) == len(self.states) == self.meta['known_grade5_states']
            for idx,source_id,pivot,nnz in self.db.execute('SELECT id,source_id,pivot,nnz FROM rows ORDER BY id'):
                assert idx == len(self.info) and pivot not in self.pivots
                assert 0 <= source_id < self.meta['cursor']
                self.info.append((pivot,nnz))
                self.pivots[pivot] = idx
            assert len(self.info) == self.meta['normal_rank'] <= 300
            assert self.db.execute('SELECT COUNT(*) FROM projections').fetchone()[0] == self.meta['cursor']
            assert [row[0] for row in self.db.execute('SELECT source_id FROM projections ORDER BY source_id')] == list(range(self.meta['cursor']))
            targets = list(self.db.execute('SELECT id,source_id FROM targets ORDER BY id'))
            assert targets == [(i,i) for i in range(len(targets))]
            assert len(targets) <= self.meta['target_count'] == len(self.target_words)
            assert not self.meta['targets_ready'] or len(targets) == len(self.target_words)
        else:
            assert not self.db.execute('SELECT 1 FROM rows LIMIT 1').fetchone()
            self.meta = {'format':FORMAT,'source_sha256':bindings,'input_paths':self.data.paths,
                'prime':p.PRIME,'roots':[231543,1000],'weight':list(self.weight),
                'operators':self.operators,'bounds':[4,27],'factors':self.factors,
                'cursor':0,'normal_rank':0,'saved_terms':0,'target_count':len(self.target_words),
                'targets_ready':False,'target_contained_count':0,'candidate_count':len(self.tasks),
                'candidate_counts':counts,'task_digest':task_digest,'target_digest':target_digest,
                'target_recipes':self.target_words,'status':'running','history':[]}
        self.oracle_controls()
        self.save('Direct normal recipe sources and oracle controls authenticated')

    def oracle_controls(self):
        cases = [self.target_words[0]]
        for kind in ('grade4_descendant','S2_minus1_S3'):
            word = next((w for w in self.tasks if w['kind'] == kind),None)
            if word is not None:
                cases.append(word)
        records,grade5_example = [],None
        for word in cases:
            for scale in (1,7):
                def oracle(left,n,right):
                    return self.mode_cache.original_mode(left,n,{s:c*scale for s,c in right.items()})
                def cached(left,n,right):
                    return self.mode_cache.mode(left,n,{s:c*scale for s,c in right.items()})
                expected = highest.bounded(self.data.evaluate(word,oracle))
                actual = highest.bounded(self.data.evaluate(word,cached))
                assert actual == expected,('Direct candidate cache oracle mismatch',word,scale)
                if actual and grade5_example is None:
                    grade5_example = min(actual)
                records.append({'recipe':word,'scale':scale,'terms':len(actual),'digest':vector_digest(actual)})
        assert grade5_example is not None and p.x.grade(grade5_example) == 5
        current_controls = []
        for index,current in enumerate(self.currents):
            for scalar in (1,7):
                right = {grade5_example:p.x.A(scalar)}
                expected = self.mode_cache.original_mode(current,0,right)
                actual = self.mode_cache.mode(current,0,right)
                assert actual == expected
                current_controls.append({'current':index,'scale':scalar,
                    'state':grade5_example,'terms':len(actual),'digest':vector_digest(actual)})
        for H,E,F in (self.currents[:3],self.currents[3:]):
            assert self.mode_cache.mode(E,0,F) == {s:int(c) for s,c in H.items() if c}
            assert self.mode_cache.mode(H,0,E) == {s:2*int(c)%p.PRIME for s,c in E.items() if c}
        for left in self.currents[:3]:
            for right in self.currents[3:]:
                assert not self.mode_cache.mode(left,0,right)
        assert self.mode_cache.statistics()['basis_cache_hits'] > 0
        self.meta['controls'] = {'whole_word_original_mode_comparisons':records,
            'grade5_current_original_mode_comparisons':current_controls,
            'sl2_normalization_and_commuting_axes':True}

    def recipe(self,word,unprojected):
        return {'kind':'direct_normal_highest_projection','normal_recipe':word,
                'weight':list(self.weight),'factors':self.factors,
                'unprojected_sha256':vector_digest(unprojected)}

    def save(self,reason,status='running'):
        self.meta.update({'status':status,'seconds_this_call':monotonic()-self.started,
            'known_grade5_states':len(self.states),'normal_rank':len(self.info),
            'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'cache_statistics':self.mode_cache.statistics(),
            'input_S2_S3_terms':self.data.input_terms,
            'scope':'Finite-prime identities in projected actual normal recipes. No ordinary N5 rank, no complete strong-span claim, and no characteristic-zero containment without exact replay.'})
        self.meta['history'].append({'reason':reason,'cursor':self.meta['cursor'],
            'rank':len(self.info),'contained':self.meta['target_contained_count'],
            'seconds':self.meta['seconds_this_call']})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(old.compact(self.meta),))
        self.db.commit()
        temporary = self.output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump({**self.meta,'sqlite_file':str(self.path)},stream,indent=2)
            stream.write('\n');stream.flush();os.fsync(stream.fileno())
        temporary.replace(self.output)
        self.last_save = monotonic()
        p.clear_caches()
        print({'reason':reason,'status':status,'cursor':self.meta['cursor'],
            'total':len(self.tasks),'rank':len(self.info),'contained':self.meta['target_contained_count'],
            'seconds':self.meta['seconds_this_call']},flush=True)

    def run(self):
        for idx,word in enumerate(self.target_words):
            if self.db.execute('SELECT 1 FROM targets WHERE id=?',(idx,)).fetchone():
                continue
            vector = highest.bounded(self.data.evaluate(word,self.mode_cache.mode))
            projected = self.project(vector)
            assert self.project(projected) == projected
            raw_vector = self.intern(projected)
            self.add_terms(len(raw_vector))
            blob,digest = old.encode(sorted(raw_vector.items()))
            self.db.execute('INSERT INTO targets VALUES (?,?,?,?,?,?,?,?)',
                (idx,idx,*self.weight,blob,old.compact(self.recipe(word,vector)),digest,None))
            self.save('One direct projected target stored')
        self.meta['targets_ready'] = True
        if self.check_targets():
            self.meta['all_candidate_recipes_processed'] = self.meta['cursor'] == len(self.tasks)
            self.save('All projected targets contained at saved cursor','all_projected_targets_contained')
            return
        last_rank = len(self.info)
        while self.meta['cursor'] < len(self.tasks):
            index = self.meta['cursor']
            word = self.tasks[index]
            vector = highest.bounded(self.data.evaluate(word,self.mode_cache.mode))
            assert all(p.x.grade(s) == 5 and p.x.weight(s) == self.weight for s in vector)
            projected = self.project(vector)
            raw_vector = self.intern(projected)
            blob,digest = old.encode(sorted(raw_vector.items()))
            residual = self.reduce(raw_vector)
            accepted = None
            if residual:
                if len(self.info) >= 300:
                    raise p.Stop('300 projected-row review cap')
                pivot = min(residual,key=lambda i:self.states[i])
                inverse = pow(residual[pivot],-1,p.PRIME)
                residual = {i:c*inverse%p.PRIME for i,c in residual.items()}
                self.add_terms(len(raw_vector)+len(residual))
                reduced,_ = old.encode(sorted(residual.items()))
                accepted = len(self.info)
                self.db.execute('INSERT INTO rows VALUES (?,?,?,?,?,?,?,?,?,?)',
                    (accepted,index,*self.weight,pivot,len(residual),blob,reduced,
                     old.compact(self.recipe(word,vector)),digest))
                self.info.append((pivot,len(residual)))
                self.pivots[pivot] = accepted
            self.db.execute('INSERT INTO projections VALUES (?,?,?,?,?)',
                (index,len(vector),len(raw_vector),digest,accepted))
            self.meta['cursor'] += 1
            highest.bounded({})
            if len(self.info)-last_rank >= 5 or self.meta['cursor']%16 == 0:
                last_rank = len(self.info)
                if self.check_targets():
                    self.meta['all_candidate_recipes_processed'] = self.meta['cursor'] == len(self.tasks)
                    self.save('Selected actual normal recipes contain projected targets','all_projected_targets_contained')
                    return
            if monotonic()-self.last_save >= 20:
                self.save('Direct projected recipe checkpoint')
        self.meta['all_candidate_recipes_processed'] = True
        passed = self.check_targets()
        self.save('Explicit candidate recipe list exhausted',
            'all_projected_targets_contained' if passed else 'projected_target_residual')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--p4-summary',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--p4-vectors',default='hi_cft_20260923_next_structure_p4_controls.vectors.json.gz')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--operators',default='0,1,2,3,4,5,6,7,8')
    parser.add_argument('--weight',required=True)
    parser.add_argument('--order',choices=('interleaved','products_first','descendants_first'),default='interleaved')
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=int,default=300)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    consumer = None
    try:
        assert p.g3.install_prime(p.PRIME) == [231543,1000]
        old.install_modes()
        consumer = Consumer(args)
        consumer.run()
    except (p.Stop,helper.CacheLimit,TimeoutError,MemoryError) as error:
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.db.rollback()
        print({'status':'bounded_interruption','reason':str(error),
               'action':'Prior atomic recipe checkpoint retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close();consumer.data.db.close()


if __name__ == '__main__':
    main()
