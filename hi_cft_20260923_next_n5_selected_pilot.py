"""Root-only grade-five selected normal-word containment pilot.

No ambient grade-five basis. Full S2(-1)S3 products avoid cross-block
lowering assumptions. Exhaustion refers only to the explicit column family.
A modular residual never proves a new characteristic-zero strong generator.
"""
import argparse
from collections import OrderedDict
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

import hi_cft_20260923_next_n4_strong_pilot as p
import hi_cft_20260923_proof_general_modes_v2 as modes


MIB = 1024**2
FORMAT = 'selected-n5-normal-prime-v1'
MAX_RECORD = 16*MIB
MAX_ROW_TERMS = 40000
MAX_SAVED_TERMS = 16000000
MAX_STATES = 120000
CACHE_TERMS = 250000


def compact(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))


def encode(value):
    data = compact(value).encode()
    if len(data) > MAX_RECORD:
        raise p.Stop('16 MiB serialized-record cap')
    return zlib.compress(data,1),hashlib.sha256(data).hexdigest()


def decode(blob,digest=None):
    decoder = zlib.decompressobj()
    data = decoder.decompress(blob,MAX_RECORD+1)
    assert len(data) <= MAX_RECORD and decoder.eof and not decoder.unconsumed_tail
    if digest:
        assert hashlib.sha256(data).hexdigest() == digest
    return json.loads(data)


def install_modes():
    # Install before ANY mode call and clear both old and rebound caches.
    modes.vertex.cache_clear()
    modes.basis_mode.cache_clear()
    modes.old.creation.cache_clear()
    modes.MAX_GRADE = 5
    p.x.creation = lru_cache(maxsize=64)(modes.old.creation.__wrapped__)
    modes.old.creation = p.x.creation
    modes.vertex = lru_cache(maxsize=64)(modes.vertex.__wrapped__)
    modes.basis_mode = lru_cache(maxsize=128)(modes.basis_mode.__wrapped__)
    p.x.vertex,p.x.basis_mode = modes.vertex,modes.basis_mode


class Pilot:
    def __init__(self,args):
        self.args = args
        self.started = self.last_save = monotonic()
        self.output = Path(args.output)
        self.path = self.output.with_suffix('.sqlite')
        self.source_path = Path(args.source_database).resolve()
        assert self.source_path.stat().st_size <= 512*MIB
        assert not Path(str(self.source_path)+'-journal').exists(),'Close the grade-four writer first'
        self.source = sqlite3.connect(self.source_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.source.execute('PRAGMA cache_size=-4096')
        self.source.execute('PRAGMA mmap_size=0')
        self.source_meta = json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.source_meta['format'] == p.FORMAT and self.source_meta['prime'] == p.PRIME
        assert self.source_meta['normal_span_complete']
        assert self.source_meta['normal_rank'] == 6007 and self.source_meta['extra_rank'] == 3
        assert self.source_meta['union_rank_lower_bound'] == 6010
        for path,digest in self.source_meta['source_sha256'].items():
            assert p.sha(path) == digest,path
        self.frozen,self.inputs,self.ops,hashes,self.input_terms = p.read_inputs(args)
        assert str(Path(args.checkpoint)/'manifest.json') == self.source_meta['checkpoint_manifest']
        hashes.update(self.source_meta['source_sha256'])
        hashes[str(self.source_path)] = p.sha(self.source_path)
        summary = Path(args.source_summary)
        assert summary.stat().st_size <= 8*MIB
        summary_meta = json.loads(summary.read_text())
        assert all(summary_meta[k] == self.source_meta[k] for k in ('source_sha256','stage','cursor','normal_rank','extra_rank','saved_terms'))
        hashes[str(summary)] = p.sha(summary)
        for path in (__file__,modes.__file__):
            hashes[str(path)] = p.sha(path)
        self.selected_ops = sorted(set(int(i) for i in args.operators.split(',')))
        assert self.selected_ops and all(0 <= i < 10 for i in self.selected_ops)
        self.source_states = {}
        for idx,value in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            a,o = json.loads(value)
            self.source_states[idx] = (tuple(a),tuple(o))
        assert len(self.source_states) <= 71052
        # Use the controlled actual K-triplet, not arbitrary quotient lifts.
        # Its vectors remain explicit U words by the source-bound projection.
        p4_summary = Path(args.p4_summary)
        p4_vectors = Path(args.p4_vectors)
        assert p4_summary.stat().st_size <= 8*MIB and p4_vectors.stat().st_size <= 16*MIB
        control = json.loads(p4_summary.read_text())
        assert control['status'] == 'exact_P4_triplet_and_lower_controls_passed'
        assert Path(control['vectors_file']).resolve() == p4_vectors.resolve()
        assert control['vectors_sha256'] == p.sha(p4_vectors)
        decoder = zlib.decompressobj(31)
        bundle_bytes = decoder.decompress(p4_vectors.read_bytes(),32*MIB+1)
        assert len(bundle_bytes) <= 32*MIB and decoder.eof and not decoder.unconsumed_tail
        bundle = json.loads(bundle_bytes)
        del bundle_bytes
        assert bundle['format'] == 'exact-p4-triplet-v1' and len(bundle['fields']) == 3
        for graph in (control['source_sha256'],bundle['source_sha256']):
            for path,digest in graph.items():
                assert p.sha(path) == digest,path
                assert path not in hashes or hashes[path] == digest
                hashes[path] = digest
        hashes[str(p4_summary)] = p.sha(p4_summary)
        hashes[str(p4_vectors)] = p.sha(p4_vectors)
        self.p4_fields,self.extra_weights = {},{}
        for field in bundle['fields']:
            assert field['grade'] == 4 and len(field['vector']) <= 12000
            vector = {(tuple(a),tuple(o)):p.x.A(c) for a,o,c in field['vector']}
            vector = {s:c for s,c in vector.items() if c}
            weight = tuple(field['weight'])
            assert vector and all(p.x.grade(s) == 4 and p.x.weight(s) == weight for s in vector)
            assert field['id'] not in self.p4_fields
            self.p4_fields[field['id']] = vector
            self.extra_weights[field['id']] = weight
        del bundle
        assert self.extra_weights == {'P4_plus':(0,2),'P4_zero':(0,0),'P4_minus':(0,-2)}
        self.source_rows = [('rows',idx,(w0,w1)) for idx,w0,w1 in
                            self.source.execute('SELECT id,w0,w1 FROM rows ORDER BY id')]
        self.source_rows += [('P4',name,self.extra_weights[name]) for name in ('P4_plus','P4_zero','P4_minus')]
        assert len(self.source_rows) == 6010
        self.op_weights = []
        for vector,_ in self.ops:
            weights = {p.x.weight(s) for s in vector}
            assert len(weights) == 1
            self.op_weights.append(weights.pop())
        self.current_weights = [p.x.weight(next(iter(c))) for c in p.x.LEFT+p.x.RIGHT]
        self.target_words,self.selected_weights = [],set()
        for op in self.selected_ops:
            for idx,weight in sorted(self.extra_weights.items()):
                result_weight = tuple(a+b for a,b in zip(self.op_weights[op],weight))
                self.target_words.append({'kind':'S2_zero_P4_canonical','operator':op,'mode':0,
                                          'source4_table':'P4','source4_id':idx,
                                          'weight':result_weight})
                self.selected_weights.add(result_weight)
        self.tasks = []
        for op in range(7):
            operator_weight = self.current_weights[op] if op < 6 else (0,0)
            for table,idx,weight in self.source_rows:
                w = tuple(a+b for a,b in zip(operator_weight,weight))
                if w in self.selected_weights:
                    self.tasks.append({'kind':'grade4_descendant','operator':op,
                                       'mode':-1 if op < 6 else 0,'source4_table':table,
                                       'source4_id':idx,'weight':w})
        self.descendant_tasks = len(self.tasks)
        for left in self.frozen['order']['2']:
            lw = p.x.weight(next(iter(self.inputs[left])))
            for right in self.frozen['order']['3']:
                rw = p.x.weight(next(iter(self.inputs[right])))
                w = tuple(a+b for a,b in zip(lw,rw))
                if w in self.selected_weights:
                    self.tasks.append({'kind':'S2_minus1_S3','mode':-1,
                                       'exact_left':left,'exact_right':right,'weight':w})
        assert len(self.tasks) <= 30000,'Reviewed selected-column task bound'
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
        self.db.execute('CREATE TABLE IF NOT EXISTS rows (id INTEGER PRIMARY KEY,w0 INTEGER,w1 INTEGER,pivot INTEGER,nnz INTEGER,raw BLOB,reduced BLOB,word TEXT,digest TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS targets (id INTEGER PRIMARY KEY,w0 INTEGER,w1 INTEGER,raw BLOB,word TEXT,digest TEXT,residual BLOB)')
        self.db.commit()
        self.states,self.ids,self.weights,self.info,self.blocks = [],{},{},[],{}
        self.cache,self.cache_terms = OrderedDict(),0
        previous = self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if previous:
            self.meta = json.loads(previous[0])
            assert self.meta['format'] == FORMAT and self.meta['source_sha256'] == hashes
            assert self.meta['operators'] == self.selected_ops
            assert self.meta['task_digest'] == hashlib.sha256(compact(self.tasks).encode()).hexdigest()
            assert self.meta['status'] not in ('targets_contained','explicit_columns_exhausted')
            for idx,value in self.db.execute('SELECT id,value FROM states ORDER BY id'):
                assert idx == len(self.states)
                a,o = json.loads(value)
                state = (tuple(a),tuple(o))
                assert p.x.grade(state) == 5
                self.states.append(state)
                self.ids[state] = idx
                self.weights[idx] = p.x.weight(state)
            for idx,w0,w1,pivot,nnz in self.db.execute('SELECT id,w0,w1,pivot,nnz FROM rows ORDER BY id'):
                assert idx == len(self.info)
                self.info.append(((w0,w1),pivot,nnz))
                assert pivot not in self.blocks.setdefault((w0,w1),{})
                self.blocks[(w0,w1)][pivot] = idx
            assert len(self.info) == self.meta['normal_rank']
        else:
            assert not self.db.execute('SELECT 1 FROM rows LIMIT 1').fetchone()
            self.meta = {'format':FORMAT,'source_sha256':hashes,'operators':self.selected_ops,
                         'prime':p.PRIME,'roots':[231543,1000],'cursor':0,'targets_ready':False,
                         'normal_rank':0,'saved_terms':0,'status':'running','history':[],
                         'task_digest':hashlib.sha256(compact(self.tasks).encode()).hexdigest(),
                         'total_tasks':len(self.tasks),'descendant_tasks':self.descendant_tasks,
                         'target_count':len(self.target_words),'target_contained_count':0}

    def source_vector(self,table,idx):
        if table == 'P4':
            return self.p4_fields[idx]
        assert table == 'rows'
        blob,digest = self.source.execute(f'SELECT raw,digest FROM {table} WHERE id=?',(idx,)).fetchone()
        pairs = decode(blob,digest)
        assert len(pairs) <= 20000
        return {self.source_states[i]:p.x.A(c) for i,c in pairs}

    def intern_vector(self,vector,weight):
        if len(vector) > MAX_ROW_TERMS:
            raise p.Stop('40000-term candidate cap')
        raw = {}
        for state,c in vector.items():
            if not c:
                continue
            assert p.x.grade(state) == 5 and p.x.weight(state) == weight
            idx = self.ids.get(state)
            if idx is None:
                idx = len(self.states)
                if idx >= MAX_STATES:
                    raise p.Stop('120000 encountered grade-five state cap')
                self.states.append(state)
                self.ids[state] = idx
                self.weights[idx] = weight
                self.db.execute('INSERT INTO states VALUES (?,?)',(idx,compact(state)))
            raw[idx] = int(c)
        return raw

    def row(self,idx):
        if idx in self.cache:
            self.cache.move_to_end(idx)
            return self.cache[idx]
        blob, = self.db.execute('SELECT reduced FROM rows WHERE id=?',(idx,)).fetchone()
        row = dict(decode(blob))
        assert len(row) == self.info[idx][2] <= MAX_ROW_TERMS
        while self.cache and self.cache_terms+len(row) > CACHE_TERMS:
            _,old = self.cache.popitem(last=False)
            self.cache_terms -= len(old)
        self.cache[idx] = row
        self.cache_terms += len(row)
        return row

    def reduce(self,raw,weight):
        out = dict(raw)
        for pivot,idx in sorted(self.blocks.get(weight,{}).items(),key=lambda item:self.states[item[0]]):
            factor = out.get(pivot,0)
            if factor:
                for state,c in self.row(idx).items():
                    value = (out.get(state,0)-factor*c) % p.PRIME
                    if value:
                        out[state] = value
                    else:
                        out.pop(state,None)
        return out

    def accept(self,vector,word):
        weight = tuple(word['weight'])
        raw = self.intern_vector(vector,weight)
        residual = self.reduce(raw,weight)
        if residual:
            if len(residual) > MAX_ROW_TERMS or self.meta['saved_terms']+len(raw)+len(residual) > MAX_SAVED_TERMS:
                raise p.Stop('Reviewed raw/echelon term cap')
            if len(self.blocks.get(weight,{})) >= 4096:
                raise p.Stop('4096 rows per selected Cartan block cap')
            pivot = min(residual,key=lambda i:self.states[i])
            inverse = pow(residual[pivot],-1,p.PRIME)
            residual = {i:c*inverse % p.PRIME for i,c in residual.items()}
            raw_blob,raw_digest = encode(sorted(raw.items()))
            reduced_blob,_ = encode(sorted(residual.items()))
            idx = len(self.info)
            self.db.execute('INSERT INTO rows VALUES (?,?,?,?,?,?,?,?,?)',
                            (idx,*weight,pivot,len(residual),raw_blob,reduced_blob,compact(word),raw_digest))
            self.info.append((weight,pivot,len(residual)))
            self.blocks.setdefault(weight,{})[pivot] = idx
            self.meta['normal_rank'] += 1
            self.meta['saved_terms'] += len(raw)+len(residual)

    def build_targets(self):
        if self.meta['targets_ready']:
            return
        for idx,word in enumerate(self.target_words):
            if self.db.execute('SELECT 1 FROM targets WHERE id=?',(idx,)).fetchone():
                continue
            vector = p.x.mode(self.ops[word['operator']][0],0,
                              self.source_vector('P4',word['source4_id']))
            raw = self.intern_vector(vector,tuple(word['weight']))
            blob,digest = encode(sorted(raw.items()))
            self.db.execute('INSERT INTO targets VALUES (?,?,?,?,?,?,?)',
                            (idx,*word['weight'],blob,compact(word),digest,None))
            self.boundary()
        self.meta['targets_ready'] = True
        self.save('selected grade-five targets computed')

    def check_targets(self):
        contained = 0
        for idx,w0,w1,blob,digest in self.db.execute('SELECT id,w0,w1,raw,digest FROM targets ORDER BY id'):
            raw = dict(decode(blob,digest))
            residual = self.reduce(raw,(w0,w1))
            packed,_ = encode(sorted(residual.items()))
            self.db.execute('UPDATE targets SET residual=? WHERE id=?',(packed,idx))
            contained += not residual
        self.meta['target_contained_count'] = contained
        return contained == len(self.target_words)

    def boundary(self):
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss >= 1024*1024:
            raise p.Stop('1 GiB RSS candidate-boundary review stop')
        if monotonic()-self.last_save >= 20:
            self.save('periodic selected-column checkpoint')

    def save(self,reason,status='running'):
        self.meta.update({'status':status,'input_S2_S3_terms':self.input_terms,
                          'known_grade5_states':len(self.states),'selected_weights':sorted(self.selected_weights),
                          'Cartan_ranks':{str(w):len(rows) for w,rows in sorted(self.blocks.items())},
                          'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          'seconds_this_call':monotonic()-self.started,
                          'scope':'Only explicit normal columns K(-1)/T of saved raw N4 plus canonical P4, and full S2(-1)S3. No complete characteristic-zero N5 span or new-generator claim. Target containment is finite-prime only.',
                          'provenance':'Source4 rows references denote raw normal words; P4 references denote the source-bound exact projected triplet. Exact S2/S3 references are bound to frozen checkpoint24. Every accepted normal column stores its raw vector, echelon vector, word and pivot.'})
        self.meta['history'].append({'reason':reason,'cursor':self.meta['cursor'],'rank':len(self.info),
                                     'contained':self.meta['target_contained_count'],
                                     'seconds_this_call':monotonic()-self.started})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(compact(self.meta),))
        self.db.commit()
        temporary = self.output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump({**self.meta,'sqlite_file':str(self.path)},stream,indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.output)
        p.clear_caches()
        self.last_save = monotonic()
        print({'reason':reason,'status':status,'rank':len(self.info),'cursor':self.meta['cursor'],
               'total':len(self.tasks),'contained':self.meta['target_contained_count'],
               'seconds':monotonic()-self.started},flush=True)

    def run(self):
        self.build_targets()
        if self.check_targets():
            self.meta['explicit_column_family_exhausted'] = False
            self.save('All selected targets already contained at the saved cursor','targets_contained')
            return
        currents,omega = p.x.LEFT+p.x.RIGHT,p.x.omega()
        last_checked_rank = -1
        while self.meta['cursor'] < len(self.tasks):
            word = self.tasks[self.meta['cursor']]
            if word['kind'] == 'grade4_descendant':
                right = self.source_vector(word['source4_table'],word['source4_id'])
                op = word['operator']
                left = currents[op] if op < 6 else omega
            else:
                left,right = self.inputs[word['exact_left']],self.inputs[word['exact_right']]
            self.accept(p.x.mode(left,word['mode'],right),word)
            self.meta['cursor'] += 1
            self.boundary()
            if (self.meta['cursor'] == self.descendant_tasks or len(self.info)-last_checked_rank >= 100):
                last_checked_rank = len(self.info)
                if self.check_targets():
                    self.meta['explicit_column_family_exhausted'] = False
                    self.save('All selected targets contained in the current finite-prime normal-word span','targets_contained')
                    return
        self.meta['explicit_column_family_exhausted'] = True
        passed = self.check_targets()
        self.save('Explicit selected column family exhausted',
                  'targets_contained' if passed else 'explicit_columns_exhausted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--p4-summary',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--p4-vectors',default='hi_cft_20260923_next_structure_p4_controls.vectors.json.gz')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--operators',default='7')
    parser.add_argument('--output',default='hi_cft_20260923_next_n5_selected_pilot.json')
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('grade-five hard call alarm')))
    signal.alarm(args.seconds)
    assert p.g3.install_prime(p.PRIME) == [231543,1000]
    install_modes()
    pilot = None
    try:
        pilot = Pilot(args)
        pilot.save('initialized selected grade-five pilot')
        pilot.run()
    except p.Stop as error:
        signal.alarm(0)
        if pilot is None:
            raise
        pilot.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if pilot is not None:
            pilot.db.rollback()
            print({'status':'interrupted','action':'Last atomic selected-grade-five checkpoint retained'},flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if pilot is not None:
            pilot.db.close()
            pilot.source.close()


if __name__ == '__main__':
    main()
