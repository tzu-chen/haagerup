"""Root-only exact relations for at most three closed N5 pilot targets.

Selected actual normal words are lifted over Q(sqrt(13),sqrt(-3)), solved
on their pivot coordinates using FLINT, and verified on EVERY sparse state.
No characteristic-zero upper rank or full-N5 exhaustion is asserted.
Native solves also require an external process timeout in the root launch.
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

import hi_cft_20260923_next_n4_h4_flint as h4
import hi_cft_20260923_proof_general_modes_v2 as modes


b = h4.b
FORMAT = 'exact-selected-n5-relations-v1'
MIB = 1024**2
MAX_RECORD = 32*MIB
MAX_TERMS = 40000
MAX_SAVED_TERMS = 2000000
CACHE_BYTES = 128*MIB


def unpack(blob,digest=None):
    decoder = zlib.decompressobj()
    data = decoder.decompress(blob,MAX_RECORD+1)
    assert len(data) <= MAX_RECORD and decoder.eof and not decoder.unconsumed_tail
    if digest:
        assert hashlib.sha256(data).hexdigest() == digest
    return json.loads(data)


def pack(value):
    data = b.compact(value).encode()
    if len(data) > MAX_RECORD:
        raise b.BudgetStop('32 MiB exact N5 record cap')
    return zlib.compress(data,1),hashlib.sha256(data).hexdigest()


def installed_modes():
    modes.vertex.cache_clear()
    modes.basis_mode.cache_clear()
    modes.old.creation.cache_clear()
    modes.MAX_GRADE = 5
    b.x.creation = lru_cache(maxsize=64)(modes.old.creation.__wrapped__)
    modes.old.creation = b.x.creation
    modes.vertex = lru_cache(maxsize=64)(modes.vertex.__wrapped__)
    modes.basis_mode = lru_cache(maxsize=128)(modes.basis_mode.__wrapped__)
    b.x.vertex,b.x.basis_mode = modes.vertex,modes.basis_mode


class ExactSelected:
    def __init__(self,args):
        self.args,self.started = args,monotonic()
        self.last_save = self.started
        self.output = Path(args.output)
        self.path = self.output.with_suffix('.sqlite')
        source_path = Path(args.database).resolve()
        assert source_path.stat().st_size <= 512*MIB
        assert not Path(str(source_path)+'-journal').exists(),'Close the N5 producer first'
        self.source = sqlite3.connect(source_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.source.execute('PRAGMA cache_size=-4096')
        self.source.execute('PRAGMA mmap_size=0')
        self.pm = json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.pm['format'] == 'selected-n5-normal-prime-v1'
        assert self.pm['prime'] == b.PRIME and self.pm['roots'] == [231543,1000]
        assert self.pm['targets_ready'] and 0 < self.pm['target_count'] <= 3
        bindings = dict(self.pm['source_sha256'])
        for path,digest in bindings.items():
            assert b.sha(path) == digest,path
        if 'mode_cache_v2' in self.pm:
            lineage = self.pm['mode_cache_v2']
            assert lineage['format'] == 'selected-n5-prime-mode-cache-v2'
            assert lineage['controls']['all_equal_to_original_mode']
            for path,digest in lineage['source_sha256'].items():
                assert b.sha(path) == digest,path
                assert path not in bindings or bindings[path] == digest
                bindings[path] = digest
            ancestor = lineage['ancestor_database']
            assert b.sha(ancestor) == lineage['ancestor_database_sha256']
            assert ancestor not in bindings or bindings[ancestor] == lineage['ancestor_database_sha256']
            bindings[ancestor] = lineage['ancestor_database_sha256']
        bindings[str(source_path)] = b.sha(source_path)
        source_summary = Path(args.source_summary)
        summary = b.load_json(source_summary)
        assert all(summary[k] == self.pm[k] for k in ('source_sha256','cursor','normal_rank','targets_ready','target_count'))
        bindings[str(source_summary)] = b.sha(source_summary)
        resolved = {str(Path(path).resolve()):digest for path,digest in bindings.items()}
        assert resolved[str(Path(args.grade4_database).resolve())] == b.sha(args.grade4_database)
        assert resolved[str(Path(args.p4_controls).resolve())] == b.sha(args.p4_controls)
        for path in (__file__,h4.__file__,b.__file__,modes.__file__,h4.native.__file__):
            bindings[str(Path(path).resolve())] = b.sha(path)

        self.states = {}
        for idx,value in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx == len(self.states) and idx < 120000
            a,o = json.loads(value)
            state = (tuple(a),tuple(o))
            assert b.x.grade(state) == 5
            self.states[idx] = state
        assert len(self.states) == self.pm['known_grade5_states']
        self.blocks = {}
        for idx,w0,w1,pivot in self.source.execute('SELECT id,w0,w1,pivot FROM rows ORDER BY id'):
            assert pivot in self.states and b.x.weight(self.states[pivot]) == (w0,w1)
            self.blocks.setdefault((w0,w1),[]).append((idx,self.states[pivot]))
        assert sum(map(len,self.blocks.values())) == self.pm['normal_rank']
        self.targets = []
        for idx,w0,w1,word in self.source.execute('SELECT id,w0,w1,word FROM targets ORDER BY id'):
            assert idx == len(self.targets)
            recipe = json.loads(word)
            assert recipe['kind'] == 'S2_zero_P4_canonical' and recipe['source4_table'] == 'P4'
            assert recipe['mode'] == 0 and tuple(recipe['weight']) == (w0,w1)
            self.targets.append((idx,(w0,w1),recipe))
        assert len(self.targets) == self.pm['target_count']

        # The grade-four provider owns a separate derived cache. Its normal:<id>
        # namespace and word graph remain unchanged; N5 uses grade5:<id> below.
        grade4_path = Path(args.grade4_database).resolve()
        connection = sqlite3.connect(grade4_path.as_uri()+'?mode=ro&immutable=1',uri=True)
        try:
            assert not Path(str(grade4_path)+'-journal').exists()
            w0,w1 = connection.execute('SELECT w0,w1 FROM rows GROUP BY w0,w1 ORDER BY COUNT(*),w0,w1 LIMIT 1').fetchone()
        finally:
            connection.close()
        provider_args = argparse.Namespace(database=args.grade4_database,p4_controls=args.p4_controls,
                                           weight=f'{w0},{w1}',output=str(self.output.with_suffix('.grade4.json')),
                                           max_rank=300,max_targets=0,batch=3,seconds=args.seconds)
        self.provider = h4.Consumer(provider_args)
        provider_extension = {'format':'N5-grade4-provider-v1','source_sha256':bindings}
        previous = self.provider.meta.get('N5_provider_extension')
        if previous is not None:
            assert previous == provider_extension
        else:
            assert not self.provider.meta['verified_targets'] and not self.provider.meta['failed_targets']
            self.provider.meta['N5_provider_extension'] = provider_extension
            self.provider.save('N5 exact raw-DAG provider bound')
        self.p4 = {info['id']:self.provider.p4[key] for key,info in self.provider.p4_info.items()}
        assert set(self.p4) == {'P4_plus','P4_zero','P4_minus'}
        self.ops,self.currents,self.omega = self.provider.ops,self.provider.currents,self.provider.omega
        self.flint = self.provider.flint

        self.db = sqlite3.connect(self.path)
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-8192')
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
            assert self.db.execute('SELECT COUNT(*) FROM relations').fetchone()[0] == self.meta['verified_targets']+self.meta['failed_targets']
        else:
            assert not self.db.execute('SELECT 1 FROM vectors LIMIT 1').fetchone()
            self.meta = {'format':FORMAT,'source_sha256':bindings,'saved_terms':0,'verified_targets':0,
                         'failed_targets':0,'target_count':len(self.targets),'status':'running','history':[],
                         'largest_vector_bits':0,'largest_relation_bits':0,'completed_blocks':[],
                         'provider_file':str(self.provider.path)}
        self.save('exact selected N5 consumer initialized')

    def boundary(self):
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss >= 1400*1024:
            raise b.BudgetStop('1400 MiB RSS review boundary')
        if monotonic()-self.last_save >= 20:
            self.save('periodic exact N5 checkpoint')

    def save(self,reason,status='running'):
        self.meta.update({'status':status,'seconds_this_call':monotonic()-self.started,
                          'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          'scope':'Exact identities in selected actual normal words. No upper-rank, whole-N5 exhaustion, or standalone properness claim.',
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
               'failed_targets':self.meta['failed_targets'],'seconds':monotonic()-self.started},flush=True)

    def cache_put(self,name,vector,bits):
        cost = len(vector)*(512+8*((bits+7)//8))+4096
        while self.cache and self.cache_bytes+cost > CACHE_BYTES:
            _,(_,old) = self.cache.popitem(last=False)
            self.cache_bytes -= old
        if cost <= CACHE_BYTES:
            self.cache[name] = (vector,cost)
            self.cache_bytes += cost

    def store(self,name,vector):
        if len(vector) > MAX_TERMS:
            raise b.BudgetStop('40000-term exact N5 vector cap')
        bits = max((b.height(c) for c in vector.values()),default=0)
        if bits > b.VECTOR_BITS:
            raise b.BudgetStop('2048-bit exact N5 vector cap')
        if self.meta['saved_terms']+len(vector) > MAX_SAVED_TERMS:
            raise b.BudgetStop('Two-million retained N5 exact-term cap')
        record = [[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(vector.items())]
        blob,digest = pack(record)
        self.db.execute('INSERT INTO vectors VALUES (?,?,?,?,?)',(name,blob,digest,len(vector),bits))
        self.meta['saved_terms'] += len(vector)
        self.meta['largest_vector_bits'] = max(self.meta['largest_vector_bits'],bits)
        self.cache_put(name,vector,bits)
        self.boundary()
        return vector

    def source4(self,word):
        table,idx = word['source4_table'],word['source4_id']
        if table == 'P4':
            return self.p4[idx]
        assert table == 'rows' and isinstance(idx,int) and idx >= 0
        return self.provider.vector('normal:'+str(idx))

    def vector(self,name):
        if name in self.cache:
            self.cache.move_to_end(name)
            return self.cache[name][0]
        row = self.db.execute('SELECT record,digest,terms,bits FROM vectors WHERE name=?',(name,)).fetchone()
        if row:
            blob,digest,terms,bits = row
            record = unpack(blob,digest)
            assert len(record) == terms <= MAX_TERMS and bits <= b.VECTOR_BITS
            vector = {(tuple(a),tuple(o)):b.fast.FastField(c) for a,o,c in record}
            assert len(vector) == terms
            self.cache_put(name,vector,bits)
            return vector
        kind,idx = name.split(':')
        idx = int(idx)
        assert kind in ('grade5','target')
        table = 'rows' if kind == 'grade5' else 'targets'
        word_json,raw_blob,digest = self.source.execute(f'SELECT word,raw,digest FROM {table} WHERE id=?',(idx,)).fetchone()
        word = json.loads(word_json)
        if kind == 'target':
            assert word['kind'] == 'S2_zero_P4_canonical' and word['mode'] == 0
            assert word['source4_table'] == 'P4' and 0 <= word['operator'] < 10
            left,right,n = self.ops[word['operator']],self.source4(word),0
        elif word['kind'] == 'grade4_descendant':
            op = word['operator']
            assert 0 <= op < 7 and word['mode'] == (-1 if op < 6 else 0)
            left,right,n = self.currents[op] if op < 6 else self.omega,self.source4(word),word['mode']
        else:
            assert word['kind'] == 'S2_minus1_S3' and word['mode'] == -1
            assert word['exact_left'] in self.provider.frozen['order']['2']
            assert word['exact_right'] in self.provider.frozen['order']['3']
            left = self.provider.vector('input:'+word['exact_left'])
            right = self.provider.vector('input:'+word['exact_right'])
            n = -1
        vector = b.x.mode(left,n,right)
        assert all(b.x.grade(s) == 5 and b.x.weight(s) == tuple(word['weight']) for s in vector)
        expected = {self.states[i]:c for i,c in unpack(raw_blob,digest)}
        actual = {s:residue for s,c in vector.items() if (residue:=b.specialization(c))}
        assert actual == expected,('Exact N5 word disagrees with source specialization',name)
        return self.store(name,vector)

    def verify(self,idx,weight,word,columns,target,coefficients):
        assert len(coefficients) == len(columns)
        bits = max((b.height(c) for c in coefficients),default=0)
        if bits > b.MATRIX_BITS:
            raise b.BudgetStop('4096-bit exact N5 relation cap')
        residual = dict(target)
        for column,c in zip(columns,coefficients):
            if c:
                for state,value in self.vector('grade5:'+str(column)).items():
                    b.x.add(residual,state,-c*value)
            self.boundary()
        record = {'source_target_id':idx,'word':word,'weight':weight,
                  'normal_column_coefficients':[[column,[str(q) for q in c]] for column,c in zip(columns,coefficients) if c],
                  'exact_residual_zero':not residual,'target_terms':len(target),
                  'residual':[[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(residual.items())]}
        blob,digest = pack(record)
        self.db.execute('INSERT INTO relations VALUES (?,?,?,?)',(idx,blob,digest,int(not residual)))
        self.meta['verified_targets' if not residual else 'failed_targets'] += 1
        self.meta['largest_relation_bits'] = max(self.meta['largest_relation_bits'],bits)
        self.save('full exact grade-five sparse residual checked')
        if residual:
            raise b.BudgetStop('Target outside the selected exact column span; no full-N5 upper-bound claim')

    def run(self):
        groups = {}
        for idx,weight,word in self.targets:
            old = self.db.execute('SELECT passed FROM relations WHERE id=?',(idx,)).fetchone()
            if old:
                assert old[0],'A previous exact residual is nonzero'
                continue
            if self.args.weight and weight != tuple(map(int,self.args.weight.split(','))):
                continue
            groups.setdefault(weight,[]).append((idx,word))
        for weight,targets in sorted(groups.items(),key=lambda item:(len(self.blocks.get(item[0],[])),item[0])):
            selected = self.blocks.get(weight,[])
            rank = len(selected)
            if rank > self.args.max_rank:
                self.meta['rank_guard'] = {'weight':weight,'rank':rank,'reviewed_maximum':self.args.max_rank}
                raise b.BudgetStop('Selected N5 block exceeds reviewed native rank gate')
            columns,pivots = [i for i,_ in selected],[s for _,s in selected]
            assert len(set(pivots)) == rank
            exact_targets = [self.vector('target:'+str(idx)) for idx,_ in targets]
            if rank:
                matrix = [[b.fast.ZERO for _ in columns] for _ in columns]
                for j,column in enumerate(columns):
                    vector = self.vector('grade5:'+str(column))
                    for i,state in enumerate(pivots):
                        matrix[i][j] = vector.get(state,b.fast.ZERO)
                    self.boundary()
                self.save('all exact N5 columns reconstructed for block '+str(weight))
                rhs = [[target.get(state,b.fast.ZERO) for target in exact_targets] for state in pivots]
                matrix_bits = max((b.height(c) for row in matrix for c in row),default=0)
                # Four copies of the dense regular-representation entries,
                # including rounded numerator/denominator limbs. This is a
                # conservative preflight estimate, not a FLINT workspace
                # guarantee; the process address cap remains authoritative.
                native_estimate = 4*(4*rank)**2*(64+2*((matrix_bits+11)//8))
                self.meta['native_preflight'] = {'weight':weight,'rank':rank,
                    'matrix_coefficient_bits':matrix_bits,'estimated_bytes':native_estimate,
                    'reviewed_estimate_limit_bytes':512*MIB}
                if native_estimate > 512*MIB:
                    raise b.BudgetStop('Native exact solve preflight exceeds 512 MiB estimate; review this block')
                self.save('native exact N5 block resource preflight passed')
                coefficients = self.flint.solve(matrix,rhs)
                del matrix,rhs
            else:
                coefficients = []
            for j,((idx,word),target) in enumerate(zip(targets,exact_targets)):
                self.verify(idx,weight,word,columns,target,[row[j] for row in coefficients])
            self.meta['completed_blocks'].append({'weight':weight,'rank':rank,'targets':[idx for idx,_ in targets]})
            del exact_targets,coefficients
            self.save('selected exact N5 block completed')
        complete = self.meta['verified_targets'] == len(self.targets)
        self.meta['all_source_targets_verified'] = complete
        self.save('requested exact N5 targets completed','complete' if complete else 'partial_complete')

    def close(self,rollback=False):
        if rollback:
            self.db.rollback()
            self.provider.db.rollback()
        self.db.close()
        self.source.close()
        self.provider.db.close()
        self.provider.pilot.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n5_selected_pilot.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n5_selected_pilot.json')
    parser.add_argument('--grade4-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--p4-controls',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--output',default='hi_cft_20260923_next_n5_exact_selected.json')
    parser.add_argument('--weight')
    parser.add_argument('--max-rank',type=int,default=300)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert 0 < args.max_rank <= 300 and 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('exact N5 Python alarm')))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    installed_modes()
    consumer = None
    rollback = False
    try:
        consumer = ExactSelected(args)
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
        print({'status':'interrupted','action':'Prior exact N5 vectors and relations retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.close(rollback)


if __name__ == '__main__':
    main()
