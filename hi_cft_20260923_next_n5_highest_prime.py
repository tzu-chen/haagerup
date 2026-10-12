"""Root-only bounded joint K-highest projection of closed N5 prime words.

New output only; a partial output may resume against identical bound sources.
Every projected column remains an explicit current-zero-mode polynomial word.
Finite-prime containment is not characteristic-zero containment.
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

import hi_cft_20260923_next_n5_selected_pilot as old
import hi_cft_20260923_next_prime_mode_cache as helper

FORMAT = 'selected-n5-highest-prime-v1'
PRIME = old.p.PRIME
MIB = 1024**2
MAX_TERMS = 40000


def factors_for(weight):
    factors = []
    for axis,w,bound,E,F in zip(('LEFT','RIGHT'),weight,(4,27),(1,4),(2,5)):
        assert 0 <= w <= bound
        for higher in range(w+2,bound+1,2):
            numerator = (higher-w)*(higher+w+2)
            assert numerator % 4 == 0
            eigenvalue = numerator//4
            assert eigenvalue and eigenvalue % PRIME
            factors.append({'axis':axis,'current_E':E,'current_F':F,
                            'weight':w,'higher_weight':higher,'eigenvalue':eigenvalue,
                            'numerator':-1,'denominator':eigenvalue,
                            'coefficient_mod_prime':(-pow(eigenvalue,-1,PRIME)) % PRIME})
    return factors


def bounded(vector):
    if len(vector) > MAX_TERMS:
        raise old.p.Stop('40000-term projected/intermediate vector cap')
    if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss >= 1024*1024:
        raise old.p.Stop('1 GiB RSS projection boundary')
    return vector


class Consumer:
    def __init__(self,args):
        self.args,self.started = args,monotonic()
        self.last_save = self.started
        self.output = Path(args.output)
        self.path = self.output.with_suffix('.sqlite')
        self.weight = tuple(map(int,args.weight.split(',')))
        assert len(self.weight) == 2
        self.factors = factors_for(self.weight)
        source_path = Path(args.database).resolve()
        summary_path = Path(args.source_summary).resolve()
        assert self.path.resolve() != source_path
        assert self.output.resolve() != summary_path
        assert source_path.stat().st_size <= 512*MIB
        assert not Path(str(source_path)+'-journal').exists(),'Close the N5 writer first'
        self.source = sqlite3.connect(source_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.source.execute('PRAGMA cache_size=-4096')
        self.source.execute('PRAGMA mmap_size=0')
        sm = json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert sm['format'] == old.FORMAT and sm['prime'] == PRIME
        assert sm['roots'] == [231543,1000] and sm['targets_ready']
        assert summary_path.stat().st_size <= 8*MIB
        summary = json.loads(summary_path.read_text())
        for key in ('source_sha256','cursor','normal_rank','targets_ready','target_count'):
            assert summary[key] == sm[key],key
        bindings = dict(sm['source_sha256'])
        if 'mode_cache_v2' in sm:
            lineage = sm['mode_cache_v2']
            assert lineage['format'] == 'selected-n5-prime-mode-cache-v2'
            assert lineage['controls']['all_equal_to_original_mode']
            for path,digest in lineage['source_sha256'].items():
                assert path not in bindings or bindings[path] == digest
                bindings[path] = digest
            ancestor = lineage['ancestor_database']
            assert ancestor not in bindings or bindings[ancestor] == lineage['ancestor_database_sha256']
            bindings[ancestor] = lineage['ancestor_database_sha256']
        for path,digest in bindings.items():
            assert old.p.sha(path) == digest,path
        for path in (source_path,summary_path,__file__,old.__file__,helper.__file__,old.modes.__file__):
            resolved = str(Path(path).resolve())
            digest = old.p.sha(path)
            assert resolved not in bindings or bindings[resolved] == digest
            bindings[resolved] = digest
        self.source_states = []
        for idx,value in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx == len(self.source_states) and idx < 120000
            a,o = json.loads(value)
            state = (tuple(a),tuple(o))
            assert old.p.x.grade(state) == 5
            self.source_states.append(state)
        assert len(self.source_states) == sm['known_grade5_states']
        assert self.source.execute('SELECT COUNT(*) FROM rows').fetchone()[0] == sm['normal_rank']
        self.source_rows = [row[0] for row in self.source.execute(
            'SELECT id FROM rows WHERE w0=? AND w1=? ORDER BY id',self.weight)]
        self.source_targets = [row[0] for row in self.source.execute(
            'SELECT id FROM targets WHERE w0=? AND w1=? ORDER BY id',self.weight)]
        assert 0 < len(self.source_rows) <= 4096 and 0 < len(self.source_targets) <= 3
        self.currents = old.p.x.LEFT+old.p.x.RIGHT
        self.mode_cache = helper.PrimeModeCache(old.p.x,PRIME,max_terms=300000,max_entries=50000)
        for current in self.currents:
            self.mode_cache.register(current)
        self.db = sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-8192')
        self.db.execute('PRAGMA temp_store=FILE')
        self.db.execute('PRAGMA mmap_size=0')
        assert self.db.execute('PRAGMA page_size').fetchone()[0] == 4096
        self.db.execute('PRAGMA max_page_count=131072')
        self.db.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS states (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS rows (id INTEGER PRIMARY KEY,source_id INTEGER UNIQUE,w0 INTEGER,w1 INTEGER,pivot INTEGER,nnz INTEGER,raw BLOB,reduced BLOB,word TEXT,digest TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS targets (id INTEGER PRIMARY KEY,source_id INTEGER UNIQUE,w0 INTEGER,w1 INTEGER,raw BLOB,word TEXT,digest TEXT,residual BLOB)')
        self.db.execute('CREATE TABLE IF NOT EXISTS projections (source_id INTEGER PRIMARY KEY,terms INTEGER,digest TEXT,accepted_rowid INTEGER)')
        self.db.commit()
        self.states,self.ids,self.pivots,self.info = [],{},{},[]
        self.row_cache,self.row_cache_terms = OrderedDict(),0
        prior = self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if prior:
            self.meta = json.loads(prior[0])
            assert self.meta['format'] == FORMAT and self.meta['source_sha256'] == bindings
            assert tuple(self.meta['weight']) == self.weight and self.meta['factors'] == self.factors
            assert self.meta['status'] not in ('all_projected_targets_contained','projected_target_residual')
            for idx,value in self.db.execute('SELECT id,value FROM states ORDER BY id'):
                assert idx == len(self.states)
                a,o = json.loads(value)
                state = (tuple(a),tuple(o))
                assert old.p.x.grade(state) == 5 and old.p.x.weight(state) == self.weight
                self.states.append(state)
                self.ids[state] = idx
            for idx,pivot,nnz in self.db.execute('SELECT id,pivot,nnz FROM rows ORDER BY id'):
                assert idx == len(self.info) and pivot not in self.pivots
                self.info.append((pivot,nnz))
                self.pivots[pivot] = idx
            assert len(self.info) == self.meta['normal_rank']
            assert self.db.execute('SELECT COUNT(*) FROM projections').fetchone()[0] == self.meta['cursor']
        else:
            assert not self.db.execute('SELECT 1 FROM rows LIMIT 1').fetchone()
            self.meta = {'format':FORMAT,'source_sha256':bindings,'prime':PRIME,'roots':[231543,1000],
                         'raw_source_database':str(source_path),'raw_source_summary':str(summary_path),
                         'weight':list(self.weight),'bounds':[4,27],'factors':self.factors,
                         'cursor':0,'normal_rank':0,'saved_terms':0,'target_count':len(self.source_targets),
                         'source_column_count':len(self.source_rows),'targets_ready':False,
                         'target_contained_count':0,'status':'running','history':[]}
        self.oracle_controls()
        self.save('Prime current-action oracle controls passed')

    def read_source(self,table,idx):
        assert table in ('rows','targets')
        blob,digest,word,w0,w1 = self.source.execute(
            f'SELECT raw,digest,word,w0,w1 FROM {table} WHERE id=?',(idx,)).fetchone()
        assert (w0,w1) == self.weight
        pairs = old.decode(blob,digest)
        assert len(pairs) <= MAX_TERMS
        vector = {self.source_states[i]:int(c) for i,c in pairs}
        assert len(vector) == len(pairs)
        assert all(0 < c < PRIME and old.p.x.weight(s) == self.weight for s,c in vector.items())
        return vector,json.loads(word)

    def oracle_controls(self):
        vector,_ = self.read_source('targets',self.source_targets[0])
        state = min(vector) if vector else self.source_states[0]
        count = 0
        for current in self.currents:
            for scalar in (1,7):
                right = {state:old.p.x.A(scalar)}
                expected = {s:int(c) for s,c in self.mode_cache.original_mode(current,0,right).items() if c}
                assert self.mode_cache.mode(current,0,right) == expected
                count += 1
        # Independent sl2 normalization and mutual commutation controls.
        for H,E,F in (self.currents[:3],self.currents[3:]):
            assert self.mode_cache.mode(E,0,F) == {s:int(c) for s,c in H.items() if c}
            assert self.mode_cache.mode(H,0,E) == {s:2*int(c)%PRIME for s,c in E.items() if c}
        for left in self.currents[:3]:
            for right in self.currents[3:]:
                assert not self.mode_cache.mode(left,0,right)
        self.meta['controls'] = {'whole_current_mode_comparisons':count,
                                 'sl2_normalization_and_commuting_axes':True}

    def action(self,index,vector):
        return bounded(self.mode_cache.mode(self.currents[index],0,vector))

    def project(self,vector):
        out = bounded(dict(vector))
        for factor in self.factors:
            raised = self.action(factor['current_E'],out)
            if not raised:
                continue
            lowered = self.action(factor['current_F'],raised)
            coefficient = factor['coefficient_mod_prime']
            del raised
            for state,value in lowered.items():
                new = (out.get(state,0)+coefficient*value) % PRIME
                if new:
                    out[state] = new
                else:
                    out.pop(state,None)
            del lowered
            bounded(out)
        assert all(old.p.x.grade(s) == 5 and old.p.x.weight(s) == self.weight for s in out)
        assert not self.action(1,out),'LEFT highest check'
        assert not self.action(4,out),'RIGHT highest check'
        return out

    def intern(self,vector):
        out = {}
        for state,value in vector.items():
            idx = self.ids.get(state)
            if idx is None:
                idx = len(self.states)
                if idx >= 120000:
                    raise old.p.Stop('120000 projected state cap')
                self.states.append(state)
                self.ids[state] = idx
                self.db.execute('INSERT INTO states VALUES (?,?)',(idx,old.compact(state)))
            out[idx] = value
        return out

    def row(self,idx):
        if idx in self.row_cache:
            self.row_cache.move_to_end(idx)
            return self.row_cache[idx]
        blob, = self.db.execute('SELECT reduced FROM rows WHERE id=?',(idx,)).fetchone()
        row = dict(old.decode(blob))
        assert len(row) == self.info[idx][1] <= MAX_TERMS
        while self.row_cache and self.row_cache_terms+len(row) > 250000:
            _,previous = self.row_cache.popitem(last=False)
            self.row_cache_terms -= len(previous)
        self.row_cache[idx] = row
        self.row_cache_terms += len(row)
        return row

    def reduce(self,raw):
        residual = dict(raw)
        for pivot,idx in sorted(self.pivots.items(),key=lambda item:self.states[item[0]]):
            coefficient = residual.get(pivot,0)
            if coefficient:
                for state,value in self.row(idx).items():
                    new = (residual.get(state,0)-coefficient*value) % PRIME
                    if new:
                        residual[state] = new
                    else:
                        residual.pop(state,None)
        if len(residual) > MAX_TERMS:
            raise old.p.Stop('40000-term echelon residual cap')
        return residual

    def recipe(self,kind,idx,word):
        return {'kind':'joint_highest_projection',kind:idx,'weight':list(self.weight),
                'factors':self.factors,'source_word':word}

    def add_terms(self,count):
        if self.meta['saved_terms']+count > 16000000:
            raise old.p.Stop('16 million projected disk-term cap')
        self.meta['saved_terms'] += count

    def save(self,reason,status='running'):
        self.meta.update(status=status,seconds_this_call=monotonic()-self.started,
                         known_grade5_states=len(self.states),normal_rank=len(self.info),
                         peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                         cache_statistics=self.mode_cache.statistics(),
                         scope='Explicit current-zero-mode projections of actual raw U normal words. Finite-prime rank and containment only; exact replay is required. Exhaustion means every saved source column of this weight was projected.')
        self.meta['history'].append({'reason':reason,'cursor':self.meta['cursor'],
                                     'rank':len(self.info),'seconds':monotonic()-self.started})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(old.compact(self.meta),))
        self.db.commit()
        temporary = self.output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump({**self.meta,'sqlite_file':str(self.path)},stream,indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.output)
        self.last_save = monotonic()
        print({'reason':reason,'status':status,'cursor':self.meta['cursor'],
               'total':len(self.source_rows),'rank':len(self.info),
               'seconds':self.meta['seconds_this_call']},flush=True)

    def run(self):
        for idx,source_id in enumerate(self.source_targets):
            if self.db.execute('SELECT 1 FROM targets WHERE id=?',(idx,)).fetchone():
                continue
            vector,word = self.read_source('targets',source_id)
            projected = self.project(vector)
            assert self.project(projected) == projected,'Target projection idempotence'
            raw = self.intern(projected)
            self.add_terms(len(raw))
            blob,digest = old.encode(sorted(raw.items()))
            recipe = self.recipe('source5_target',source_id,word)
            self.db.execute('INSERT INTO targets VALUES (?,?,?,?,?,?,?,?)',
                            (idx,source_id,*self.weight,blob,old.compact(recipe),digest,None))
            self.save('One projected target stored')
        self.meta['targets_ready'] = True
        last_checked_rank = len(self.info)
        if self.args.early_contained and self.check_targets():
            self.meta['all_source_columns_projected'] = self.meta['cursor'] == len(self.source_rows)
            self.save('Projected targets already contained in selected columns','all_projected_targets_contained')
            return
        while self.meta['cursor'] < len(self.source_rows):
            source_id = self.source_rows[self.meta['cursor']]
            vector,word = self.read_source('rows',source_id)
            raw = self.intern(self.project(vector))
            blob,digest = old.encode(sorted(raw.items()))
            residual = self.reduce(raw)
            accepted = None
            if residual:
                if len(self.info) >= 300:
                    raise old.p.Stop('300 selected highest-row review cap')
                pivot = min(residual,key=lambda i:self.states[i])
                inverse = pow(residual[pivot],-1,PRIME)
                residual = {i:c*inverse % PRIME for i,c in residual.items()}
                self.add_terms(len(raw)+len(residual))
                reduced,_ = old.encode(sorted(residual.items()))
                accepted = len(self.info)
                recipe = self.recipe('source5_row',source_id,word)
                self.db.execute('INSERT INTO rows VALUES (?,?,?,?,?,?,?,?,?,?)',
                                (accepted,source_id,*self.weight,pivot,len(residual),blob,reduced,old.compact(recipe),digest))
                self.info.append((pivot,len(residual)))
                self.pivots[pivot] = accepted
            self.db.execute('INSERT INTO projections VALUES (?,?,?,?)',(source_id,len(raw),digest,accepted))
            self.meta['cursor'] += 1
            bounded({})
            if self.args.early_contained and (self.meta['cursor'] % 25 == 0 or
                                               len(self.info)-last_checked_rank >= 10):
                last_checked_rank = len(self.info)
                if self.check_targets():
                    self.meta['all_source_columns_projected'] = self.meta['cursor'] == len(self.source_rows)
                    self.save('Projected targets contained in a selected subset','all_projected_targets_contained')
                    return
            if monotonic()-self.last_save >= 20:
                self.save('Projected-column checkpoint')
        passed = self.check_targets()
        self.meta['all_source_columns_projected'] = True
        self.save('All saved source columns projected; full sparse target residuals checked',
                  'all_projected_targets_contained' if passed else 'projected_target_residual')

    def check_targets(self):
        contained = 0
        for idx,blob,digest in self.db.execute('SELECT id,raw,digest FROM targets ORDER BY id'):
            residual = self.reduce(dict(old.decode(blob,digest)))
            packed,_ = old.encode(sorted(residual.items()))
            self.db.execute('UPDATE targets SET residual=? WHERE id=?',(packed,idx))
            contained += not residual
        self.meta['target_contained_count'] = contained
        return contained == len(self.source_targets)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n5_cached_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n5_cached_v2.json')
    parser.add_argument('--weight',default='1,15')
    parser.add_argument('--output',default='hi_cft_20260923_next_n5_highest_prime.json')
    parser.add_argument('--seconds',type=int,default=300)
    parser.add_argument('--early-contained',action='store_true',
                        help='Permit success after a sufficient subset, explicitly marking nonexhaustion')
    args = parser.parse_args()
    assert 0 < args.seconds <= 600
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('Highest projection alarm')))
    signal.alarm(args.seconds)
    consumer = None
    try:
        assert old.p.g3.install_prime(PRIME) == [231543,1000]
        old.install_modes()
        consumer = Consumer(args)
        consumer.run()
    except (old.p.Stop,helper.CacheLimit) as error:
        signal.alarm(0)
        if consumer is None:
            raise
        # The current column may have partially added states. Roll it back;
        # the preceding atomic checkpoint remains authoritative on resume.
        consumer.db.rollback()
        print({'status':'bounded_stop','reason':str(error),'action':'Prior atomic checkpoint retained'},flush=True)
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.db.rollback()
        print({'status':'interrupted','action':'Prior atomic checkpoint retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close()
            consumer.source.close()


if __name__ == '__main__':
    main()
