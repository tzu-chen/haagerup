"""Exact selected-normal-word relation certificates in one Cartan block.

Root-only guarded consumer. Reconstruct raw mode-word DAGs over FastField,
solve a square pivot-coordinate system, then verify every full sparse
residual. No modular upper-rank or containment inference is used.
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

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as e4
import hi_cft_20260923_next_fast_field as fast
from hi_cft_20260923_next_grade4_disk import row_stream


MIB = 1024**2
PRIME = 1000003
MAX_RECORD = 16*MIB
MAX_TERMS = 12000
MAX_SAVED_TERMS = 2000000
VECTOR_BITS = 2048
MATRIX_BITS = 4096
CACHE_BYTES = 128*MIB


class BudgetStop(Exception):
    pass


def compact(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))


def sha(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(MIB),b''):
            result.update(block)
    return result.hexdigest()


def load_json(path):
    path = Path(path)
    assert path.stat().st_size < 8*MIB
    return json.loads(path.read_text())


def pack(value):
    data = compact(value).encode()
    if len(data) > MAX_RECORD:
        raise BudgetStop('16 MiB record cap')
    return zlib.compress(data,1),hashlib.sha256(data).hexdigest()


def unpack(blob,digest=None):
    decoder = zlib.decompressobj()
    data = decoder.decompress(blob,MAX_RECORD+1)
    assert len(data) <= MAX_RECORD and decoder.eof and not decoder.unconsumed_tail
    if digest is not None:
        assert hashlib.sha256(data).hexdigest() == digest
    return json.loads(data)


def height(value):
    return max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in value)


def specialization(value):
    out = 0
    for q,r in zip(value,(1,231543,1000,231543000)):
        denominator = int(q.denominator) % PRIME
        assert denominator
        out += int(q.numerator)*pow(denominator,-1,PRIME)*r
    return out % PRIME


def clear_modes():
    for function in (x.creation,x.vertex,x.basis_mode):
        function.cache_clear()


class Consumer:
    def __init__(self,args):
        self.args = args
        self.started = self.last_save = monotonic()
        self.weight = tuple(int(v) for v in args.weight.split(','))
        assert len(self.weight) == 2
        self.output = Path(args.output)
        self.path = self.output.with_suffix('.sqlite')
        self.source_path = Path(args.database).resolve()
        assert self.source_path.stat().st_size <= 512*MIB
        assert not Path(str(self.source_path)+'-journal').exists(),'Close the modular producer first'
        self.pilot = sqlite3.connect(self.source_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.pilot.execute('PRAGMA cache_size=-4096')
        self.pilot.execute('PRAGMA mmap_size=0')
        self.pm = json.loads(self.pilot.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.pm['format'] == 'n4-normal-span-prime-v1' and self.pm['prime'] == PRIME
        bindings = dict(self.pm['source_sha256'])
        for path,digest in bindings.items():
            assert sha(path) == digest,path
        bindings[str(self.source_path)] = sha(self.source_path)
        for path in (__file__,fast.__file__):
            bindings[str(path)] = sha(path)
        control = Path('hi_cft_20260923_next_fast_field_check.json')
        checked = load_json(control)
        assert checked['status'] == 'exact_field_and_mode_equivalence_passed'
        adapter_hashes = {Path(path).name:digest for path,digest in checked['source_sha256'].items()}
        assert adapter_hashes[Path(fast.__file__).name] == sha(fast.__file__)
        assert adapter_hashes[Path(x.__file__).name] == sha(x.__file__)
        bindings[str(control)] = sha(control)
        self.manifest_path = Path(self.pm['checkpoint_manifest'])
        self.frozen = load_json(self.manifest_path)
        assert self.frozen['completed_grade3'] and self.frozen['dimensions']['3'] == 956
        self.columns = [idx for idx, in self.pilot.execute('SELECT id FROM rows WHERE w0=? AND w1=? ORDER BY id',self.weight)]
        self.r = len(self.columns)
        assert 0 < self.r <= args.max_rank <= 320,'Review rank/memory before a larger block'
        self.pivot_states = []
        self.state_ids = {}
        for idx,value in self.pilot.execute('SELECT id,value FROM states ORDER BY id'):
            a,o = json.loads(value)
            self.state_ids[idx] = (tuple(a),tuple(o))
        assert len(self.state_ids) <= 71052
        for idx in self.columns:
            pivot, = self.pilot.execute('SELECT pivot FROM rows WHERE id=?',(idx,)).fetchone()
            state = self.state_ids[pivot]
            assert x.grade(state) == 4 and x.weight(state) == self.weight
            self.pivot_states.append(state)
        assert len(set(self.pivot_states)) == self.r
        fields = load_json('hi_cft_20260923_c8_exact_fields.json')['fields']
        self.ops = [x.read_field(row) for row in fields[:-1]]
        neutral = x.read_field(fields[-1])
        self.ops += [neutral,x.vadd((1,x.omega()),(-1,x.sugawara(x.LEFT,1)),
                                   (-1,x.sugawara(x.RIGHT,39)),(-1,neutral))]
        assert len(self.ops) == 10
        self.op_weights = []
        for vector in self.ops:
            weights = {x.weight(s) for s in vector}
            assert len(weights) == 1
            self.op_weights.append(weights.pop())
        self.currents,self.omega = x.LEFT+x.RIGHT,x.omega()
        self.db = sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-8192')
        self.db.execute('PRAGMA mmap_size=0')
        self.db.execute('PRAGMA temp_store=FILE')
        assert self.db.execute('PRAGMA page_size').fetchone()[0] == 4096
        self.db.execute('PRAGMA max_page_count=131072')
        self.db.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS vectors (name TEXT PRIMARY KEY,record BLOB,digest TEXT,terms INTEGER,bits INTEGER)')
        self.db.execute('CREATE TABLE IF NOT EXISTS relations (name TEXT PRIMARY KEY,record BLOB,digest TEXT,passed INTEGER)')
        self.db.commit()
        previous = self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if previous:
            self.meta = json.loads(previous[0])
            assert self.meta['format'] == 'exact-n4-selected-block-v1'
            assert self.meta['source_sha256'] == bindings
            assert tuple(self.meta['weight']) == self.weight and self.meta['columns'] == self.columns
        else:
            assert not self.db.execute('SELECT 1 FROM vectors LIMIT 1').fetchone()
            self.meta = {'format':'exact-n4-selected-block-v1','weight':self.weight,
                         'columns':self.columns,'source_sha256':bindings,'rank':self.r,
                         'input_import_complete':False,'input_weights':{},'saved_terms':0,
                         'verified_targets':0,'failed_targets':0,'status':'running','history':[],
                         'largest_vector_bits':0,'largest_matrix_bits':0}
        self.cache,self.cache_bytes = OrderedDict(),0
        self.import_inputs()
        self.targets = []
        for op,w in enumerate(self.op_weights):
            for name in self.frozen['order']['3'][634:]:
                v = self.meta['input_weights'][name]
                if tuple(a+b for a,b in zip(w,v)) == self.weight:
                    self.targets.append((op,name))
        assert len(self.targets) <= 400
        self.save('exact block initialized')

    def boundary(self):
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss >= 1400*1024:
            raise BudgetStop('1400 MiB RSS review boundary')
        if monotonic()-self.last_save > 20:
            self.save('periodic exact checkpoint')

    def save(self,reason,status='running'):
        self.meta.update({'status':status,'cache_bytes_estimate':self.cache_bytes,
                          'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          'seconds_this_call':monotonic()-self.started,
                          'pivot_coordinates_from_modular_certificate':True,
                          'characteristic_zero_normal_rank_upper_bound_claimed':False,
                          'scope':'Exact identities in a selected subset of actual normal words. Only full sparse zero residuals certify containment.'})
        self.meta['history'].append({'reason':reason,'verified_targets':self.meta['verified_targets'],
                                     'failed_targets':self.meta['failed_targets'],
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
        clear_modes()
        self.last_save = monotonic()
        print({'reason':reason,'rank':self.r,'verified_targets':self.meta['verified_targets'],
               'failed_targets':self.meta['failed_targets'],'seconds':monotonic()-self.started},flush=True)

    def import_inputs(self):
        if self.meta['input_import_complete']:
            return
        for filename in self.frozen['block_files']:
            if not filename.startswith(('grade2_','grade3_')):
                continue
            path = self.manifest_path.parent/filename
            assert sha(path) == self.frozen['files_sha256'][filename]
            for row in row_stream(path):
                name = 'input:'+row['id']
                self.meta['input_weights'][row['id']] = row['weight']
                if not self.db.execute('SELECT 1 FROM vectors WHERE name=?',(name,)).fetchone():
                    assert len(row['vector']) <= MAX_TERMS
                    bits = row['coefficient_bits']
                    assert bits <= VECTOR_BITS
                    blob,digest = pack(row['vector'])
                    self.db.execute('INSERT INTO vectors VALUES (?,?,?,?,?)',(name,blob,digest,len(row['vector']),bits))
                    self.meta['saved_terms'] += len(row['vector'])
                    assert self.meta['saved_terms'] <= MAX_SAVED_TERMS
                self.boundary()
        assert set(self.meta['input_weights']) == set(self.frozen['order']['2']+self.frozen['order']['3'])
        self.meta['input_import_complete'] = True
        self.save('frozen exact input rows imported')

    def cache_put(self,name,vector,bits):
        cost = len(vector)*(512+8*((bits+7)//8))+4096
        while self.cache and self.cache_bytes+cost > CACHE_BYTES:
            _,(_,old_cost) = self.cache.popitem(last=False)
            self.cache_bytes -= old_cost
        if cost <= CACHE_BYTES:
            self.cache[name] = (vector,cost)
            self.cache_bytes += cost

    def store_vector(self,name,vector):
        assert len(vector) <= MAX_TERMS
        bits = max((height(c) for c in vector.values()),default=0)
        if bits > VECTOR_BITS:
            raise BudgetStop('2048-bit raw-vector coefficient cap')
        if self.meta['saved_terms']+len(vector) > MAX_SAVED_TERMS:
            raise BudgetStop('Two-million saved exact-term cap')
        record = [[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(vector.items())]
        blob,digest = pack(record)
        self.db.execute('INSERT INTO vectors VALUES (?,?,?,?,?)',(name,blob,digest,len(vector),bits))
        self.meta['saved_terms'] += len(vector)
        self.meta['largest_vector_bits'] = max(self.meta['largest_vector_bits'],bits)
        self.cache_put(name,vector,bits)
        self.boundary()
        return vector

    def vector(self,name):
        if name in self.cache:
            self.cache.move_to_end(name)
            return self.cache[name][0]
        record = self.db.execute('SELECT record,digest,terms,bits FROM vectors WHERE name=?',(name,)).fetchone()
        if record:
            blob,digest,terms,bits = record
            rows = unpack(blob,digest)
            assert len(rows) == terms <= MAX_TERMS and bits <= VECTOR_BITS
            vector = {(tuple(a),tuple(o)):x.A(c) for a,o,c in rows}
            assert len(vector) == terms
            self.cache_put(name,vector,bits)
            return vector
        assert name.startswith('normal:')
        idx = int(name.split(':')[1])
        raw_blob,raw_digest,word_json = self.pilot.execute('SELECT raw,digest,word FROM rows WHERE id=?',(idx,)).fetchone()
        word = json.loads(word_json)
        kind = word['kind']
        if kind == 'current_lowering':
            assert word['normal_row'] < idx and word['current'] in (2,5) and word['mode'] == 0
            source = self.vector('normal:'+str(word['normal_row']))
            left,n = self.currents[word['current']],0
        else:
            source = self.vector('input:'+word['exact_input'])
            if kind == 'normal_descendant':
                op = word['operator']
                assert 0 <= op < 7
                left,n = (self.currents[op],-1) if op < 6 else (self.omega,0)
                assert word['exact_input'] in self.frozen['order']['3'] and word['mode'] == n
            else:
                assert kind == 'normal_S2_product' and word['mode'] == -1
                assert 0 <= word['operator'] < 10
                assert word['exact_input'] in self.frozen['order']['2']
                left,n = self.ops[word['operator']],-1
        vector = x.mode(left,n,source)
        assert all(x.grade(s) == 4 for s in vector)
        expected = {self.state_ids[i]:c for i,c in unpack(raw_blob,raw_digest)}
        actual = {s:v for s,c in vector.items() if (v:=specialization(c))}
        assert actual == expected,'Exact raw mode word does not specialize to the pilot vector'
        return self.store_vector(name,vector)

    def matrix(self):
        matrix = [[fast.ZERO for _ in self.columns] for _ in self.columns]
        for j,idx in enumerate(self.columns):
            vector = self.vector('normal:'+str(idx))
            assert {x.weight(s) for s in vector} == {self.weight}
            for i,s in enumerate(self.pivot_states):
                matrix[i][j] = vector.get(s,fast.ZERO)
            self.boundary()
        self.save('all selected exact raw columns reconstructed')
        return matrix

    def factor(self,matrix):
        permutation = list(range(self.r))
        for i in range(self.r):
            pivot = next((j for j in range(i,self.r) if matrix[j][i]),None)
            assert pivot is not None,'Selected minor must be nonzero over the number field'
            if pivot != i:
                matrix[i],matrix[pivot] = matrix[pivot],matrix[i]
                permutation[i],permutation[pivot] = permutation[pivot],permutation[i]
            inverse = matrix[i][i].inv()
            for j in range(i+1,self.r):
                if matrix[j][i]:
                    factor = matrix[j][i]*inverse
                    matrix[j][i] = factor
                    for k in range(i+1,self.r):
                        if matrix[i][k]:
                            matrix[j][k] -= factor*matrix[i][k]
                    bits = max(height(c) for c in matrix[j])
                    self.meta['largest_matrix_bits'] = max(self.meta['largest_matrix_bits'],bits)
                    if bits > MATRIX_BITS:
                        raise BudgetStop('4096-bit exact pivot-matrix cap; switch solver, do not raise memory ceilings')
                self.boundary()
            if i % 16 == 15:
                print({'factor_pivots':i+1,'rank':self.r,'seconds':monotonic()-self.started},flush=True)
        self.save('exact pivot matrix factored')
        return permutation

    def solve(self,matrix,permutation,target):
        rhs = [target.get(self.pivot_states[i],fast.ZERO) for i in permutation]
        for i in range(self.r):
            for j in range(i):
                if matrix[i][j] and rhs[j]:
                    rhs[i] -= matrix[i][j]*rhs[j]
            if height(rhs[i]) > MATRIX_BITS:
                raise BudgetStop('4096-bit forward-solve coefficient cap')
        for i in reversed(range(self.r)):
            for j in range(i+1,self.r):
                if matrix[i][j] and rhs[j]:
                    rhs[i] -= matrix[i][j]*rhs[j]
            rhs[i] /= matrix[i][i]
            if height(rhs[i]) > MATRIX_BITS:
                raise BudgetStop('4096-bit backward-solve coefficient cap')
        if max((height(c) for c in rhs),default=0) > MATRIX_BITS:
            raise BudgetStop('4096-bit relation-coefficient cap')
        return rhs

    def verify_target(self,matrix,permutation,op,name):
        key = 'A%d_zero_%s'%(op,name)
        previous = self.db.execute('SELECT passed FROM relations WHERE name=?',(key,)).fetchone()
        if previous:
            assert previous[0],'Earlier failed selected-span identity requires a new consumer/subset'
            return
        source = self.vector('input:'+name)
        target = x.mode(self.ops[op],0,source)
        assert len(target) <= MAX_TERMS
        assert all(x.grade(s) == 4 and x.weight(s) == self.weight for s in target)
        if max((height(c) for c in target.values()),default=0) > VECTOR_BITS:
            raise BudgetStop('2048-bit exact target coefficient cap')
        coefficients = self.solve(matrix,permutation,target)
        residual = dict(target)
        for idx,c in zip(self.columns,coefficients):
            if c:
                for state,value in self.vector('normal:'+str(idx)).items():
                    x.add(residual,state,-c*value)
            self.boundary()
        target_record = [[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(target.items())]
        record = {'word':{'operator':op,'mode':0,'exact_input':name},
                  'normal_word_coefficients':[[idx,[str(q) for q in c]] for idx,c in zip(self.columns,coefficients) if c],
                  'target_sha256':hashlib.sha256(compact(target_record).encode()).hexdigest(),
                  'target_terms':len(target),'exact_residual_zero':not residual,
                  'residual':[[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(residual.items())]}
        blob,digest = pack(record)
        self.db.execute('INSERT INTO relations VALUES (?,?,?,?)',(key,blob,digest,int(not residual)))
        self.meta['verified_targets' if not residual else 'failed_targets'] += 1
        self.save('full sparse exact target verification')
        if residual:
            raise BudgetStop('Target is outside the selected exact normal-word span; no upper-span claim')

    def run(self):
        matrix = self.matrix()
        permutation = self.factor(matrix)
        self.meta['selected_exact_minor_invertible'] = True
        selected = self.targets[:self.args.max_targets] if self.args.max_targets else self.targets
        for op,name in selected:
            self.verify_target(matrix,permutation,op,name)
        self.meta['all_block_targets_count'] = len(self.targets)
        self.meta['all_block_targets_verified'] = self.meta['verified_targets'] == len(self.targets)
        self.save('selected block target list completed','complete' if self.meta['all_block_targets_verified'] else 'partial_complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n4_strong_pilot.sqlite')
    parser.add_argument('--weight',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--max-rank',type=int,default=64)
    parser.add_argument('--max-targets',type=int,default=0)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900 and 0 <= args.max_targets <= 400
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('exact block hard alarm')))
    signal.alarm(args.seconds)
    fast.install(x)
    x.creation = lru_cache(maxsize=128)(e4.creation.__wrapped__)
    e4.creation = x.creation
    x.vertex = lru_cache(maxsize=256)(e4.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=256)(e4.basis_mode.__wrapped__)
    consumer = None
    try:
        consumer = Consumer(args)
        consumer.run()
    except BudgetStop as error:
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if consumer is not None:
            consumer.db.rollback()
            print({'status':'interrupted','action':'Prior committed exact vectors and identities retained; pivot LU is recomputed on resume.'},flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close()
            consumer.pilot.close()


if __name__ == '__main__':
    main()
