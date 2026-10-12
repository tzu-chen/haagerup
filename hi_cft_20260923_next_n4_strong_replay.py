"""Read-only independent N4 SQLite rank and short-word-DAG replay.

Root launches through safe_run with AS<=3GiB. No vertex modes are recomputed.
Only earlier independently verified echelon rows may be elimination inputs.
Their immutable SQLite copies provide bounded-cache backing storage.
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
import zlib

import hi_cft_20260923_c8_exact as x
from hi_cft_20260923_next_grade4_disk import row_stream


PRIME = 1000003
MIB = 1024**2
CACHE_TERMS = 500000


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def digest(value):
    return hashlib.sha256(compact(value).encode()).hexdigest()


def sha(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(MIB), b''):
            result.update(block)
    return result.hexdigest()


def unpack(blob):
    decoder = zlib.decompressobj()
    text = decoder.decompress(blob, 8*MIB+1)
    assert len(text) <= 8*MIB and decoder.eof and not decoder.unconsumed_tail
    return json.loads(text)


def load_small_json(path):
    path = Path(path)
    assert path.stat().st_size <= 8*MIB
    return json.loads(path.read_text())


def unique_weight(vector):
    weights = {x.weight(s) for s in vector}
    assert len(weights) == 1
    return weights.pop()


class Replay:
    def __init__(self, path):
        self.path = Path(path).resolve()
        assert self.path.stat().st_size <= 512*MIB
        assert not Path(str(self.path)+'-journal').exists(), 'Producer must be closed before replay'
        self.connection = sqlite3.connect(self.path.as_uri()+'?mode=ro&immutable=1', uri=True)
        self.connection.execute('PRAGMA cache_size=-8192')
        self.connection.execute('PRAGMA mmap_size=0')
        self.meta = json.loads(self.connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.meta['format'] == 'n4-normal-span-prime-v1'
        assert self.meta['prime'] == PRIME
        assert self.meta['status'] in ('running', 'bounded_stop', 'complete')
        assert 231543**2 % PRIME == 13 and 1000**2 % PRIME == PRIME-3
        self.source_hashes = self.meta['source_sha256']
        for path, expected in self.source_hashes.items():
            assert sha(path) == expected, path
        self.initial_hash = sha(self.path)
        source_path = Path(self.meta['checkpoint_manifest'])
        self.source = load_small_json(source_path)
        assert self.source['completed_grade3']
        assert self.source['dimensions']['2'] == 120 and self.source['dimensions']['3'] == 956
        assert any(h['stage'] == 'grade3 translation descendants' and h['dimensions']['3'] == 634
                   for h in self.source['history'])
        self.input_weights = {}
        for name in self.source['block_files']:
            if name.startswith(('grade2_', 'grade3_')):
                path = source_path.parent/name
                assert str(path) in self.source_hashes
                for row in row_stream(path):
                    assert row['id'] not in self.input_weights
                    self.input_weights[row['id']] = tuple(row['weight'])
        assert set(self.input_weights) == set(self.source['order']['2']+self.source['order']['3'])
        self.s2 = set(self.source['order']['2'])
        self.s3 = set(self.source['order']['3'])
        self.p3 = set(self.source['order']['3'][634:])
        fields = load_small_json('hi_cft_20260923_c8_exact_fields.json')['fields']
        self.operator_weights = [unique_weight(x.read_field(field)) for field in fields[:-1]]+[(0,0),(0,0)]
        assert len(self.operator_weights) == 10
        self.current_weights = [unique_weight(c) for c in x.LEFT+x.RIGHT]
        self.states, self.weights = [], []
        for idx, value in self.connection.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx == len(self.states) and idx < 71052
            a, o = json.loads(value)
            state = (tuple(a), tuple(o))
            assert x.grade(state) == 4
            self.states.append(state)
            self.weights.append(x.weight(state))
        assert len(set(self.states)) == len(self.states) == self.meta['known_B4_states']
        self.cache, self.cache_terms, self.verified = OrderedDict(), 0, {}
        self.normal_blocks, self.extra_blocks = {}, {}
        self.normal_weights, self.extra_weights = [], []
        self.saved_terms, self.max_raw, self.max_reduced = 0, 0, 0

    def vector(self, pairs, weight):
        assert pairs == sorted(pairs) and 0 < len(pairs) <= 20000
        out = dict(pairs)
        assert len(out) == len(pairs)
        assert all(0 <= i < len(self.states) and 0 < c < PRIME and self.weights[i] == weight
                   for i, c in out.items())
        return out

    def cache_put(self, key, vector):
        while self.cache and self.cache_terms+len(vector) > CACHE_TERMS:
            _, old = self.cache.popitem(last=False)
            self.cache_terms -= len(old)
        self.cache[key] = vector
        self.cache_terms += len(vector)

    def prior_row(self, key):
        assert key in self.verified
        if key in self.cache:
            self.cache.move_to_end(key)
            return self.cache[key]
        table, idx = key
        pairs = unpack(self.connection.execute(f'SELECT reduced FROM {table} WHERE id=?', (idx,)).fetchone()[0])
        assert digest(pairs) == self.verified[key]
        vector = dict(pairs)
        self.cache_put(key, vector)
        return vector

    @staticmethod
    def subtract(out, coefficient, row):
        if coefficient:
            for idx, value in row.items():
                new = (out.get(idx, 0)-coefficient*value) % PRIME
                if new:
                    out[idx] = new
                else:
                    out.pop(idx, None)

    def reduce(self, vector, blocks, weight):
        for pivot, key in sorted(blocks.get(weight, {}).items(), key=lambda item: self.states[item[0]]):
            self.subtract(vector, vector.get(pivot, 0), self.prior_row(key))

    def check_word(self, word, idx, weight, extra):
        mode = word['mode']
        if extra:
            assert word['kind'] == 'S2_zero_P3' and mode == 0
            assert word['exact_input'] in self.p3
            assert 0 <= word['operator'] < 10
            source_weight = self.input_weights[word['exact_input']]
            operator_weight = self.operator_weights[word['operator']]
        elif word['kind'] == 'current_lowering':
            source = word['normal_row']
            assert 0 <= source < idx and word['current'] in (2,5) and mode == 0
            source_weight = self.normal_weights[source]
            operator_weight = self.current_weights[word['current']]
        elif word['kind'] == 'normal_descendant':
            assert word['exact_input'] in self.s3
            op = word['operator']
            assert 0 <= op < 7 and mode == (-1 if op < 6 else 0)
            source_weight = self.input_weights[word['exact_input']]
            operator_weight = self.current_weights[op] if op < 6 else (0,0)
        else:
            assert word['kind'] == 'normal_S2_product' and mode == -1
            assert word['exact_input'] in self.s2 and 0 <= word['operator'] < 10
            source_weight = self.input_weights[word['exact_input']]
            operator_weight = self.operator_weights[word['operator']]
        assert tuple(a+b for a,b in zip(source_weight,operator_weight)) == weight

    def replay_table(self, table, extra):
        weights = self.extra_weights if extra else self.normal_weights
        blocks = self.extra_blocks if extra else self.normal_blocks
        for idx, w0, w1, pivot, nnz, raw_blob, reduced_blob, word_json, raw_digest in self.connection.execute(f'SELECT * FROM {table} ORDER BY id'):
            assert idx == len(weights)
            weight = (w0,w1)
            raw_pairs, reduced_pairs = unpack(raw_blob), unpack(reduced_blob)
            assert digest(raw_pairs) == raw_digest
            raw, expected = self.vector(raw_pairs,weight), self.vector(reduced_pairs,weight)
            assert len(expected) == nnz
            self.check_word(json.loads(word_json),idx,weight,extra)
            reduced = dict(raw)
            self.reduce(reduced,self.normal_blocks,weight)
            if extra:
                self.reduce(reduced,self.extra_blocks,weight)
            assert reduced
            actual_pivot = min(reduced,key=lambda i:self.states[i])
            assert pivot == actual_pivot
            inverse = pow(reduced[pivot],-1,PRIME)
            reduced = {i:c*inverse % PRIME for i,c in reduced.items()}
            assert reduced == expected
            key = (table,idx)
            assert pivot not in blocks.setdefault(weight,{})
            blocks[weight][pivot] = key
            weights.append(weight)
            self.verified[key] = digest(sorted(reduced.items()))
            self.cache_put(key,reduced)
            self.saved_terms += len(raw)+len(reduced)
            self.max_raw = max(self.max_raw,len(raw))
            self.max_reduced = max(self.max_reduced,len(reduced))
            assert self.saved_terms <= 16000000
            assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 768*1024
            if (idx+1) % 1000 == 0:
                print({'table':table,'verified_rows':idx+1},flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n4_strong_pilot.sqlite')
    parser.add_argument('--output',default='hi_cft_20260923_next_n4_strong_replay.json')
    args = parser.parse_args()
    output = Path(args.output)
    assert not output.exists(),'Refusing overwrite'
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second replay cap')))
    signal.alarm(600)
    started = monotonic()
    audit = Replay(args.database)
    try:
        audit.replay_table('rows',False)
        audit.replay_table('extras',True)
        normal, extra = len(audit.normal_weights),len(audit.extra_weights)
        assert normal == audit.meta['normal_rank'] and extra == audit.meta['extra_rank']
        assert normal+extra == audit.meta['union_rank_lower_bound']
        assert audit.saved_terms == audit.meta['saved_terms']
        if 'contradiction_rank_lower_bound' in audit.meta:
            assert audit.meta['contradiction_rank_lower_bound'] == normal+extra >= 6011
        assert sha(audit.path) == audit.initial_hash
        result = {'status':'PASS','normal_rank_independently_verified':normal,
                  'union_rank_independently_verified':normal+extra,'prime':PRIME,
                  'short_mode_word_graph_verified':True,'source_hashes_verified':True,
                  'vertex_actions_recomputed':False,'normal_span_exhaustion_replayed':False,
                  'containment_certified_in_characteristic_zero':False,
                  'scope':'Independent fixed-prime rank and source/word-graph replay; no vertex-mode recomputation or characteristic-zero containment claim.',
                  'conditional_dimension_6010_exceeded':normal+extra >= 6011,
                  'raw_and_reduced_terms':audit.saved_terms,'maximum_raw_terms':audit.max_raw,
                  'maximum_reduced_terms':audit.max_reduced,'states':len(audit.states),
                  'database_sha256':audit.initial_hash,'database':str(audit.path),
                  'source_sha256':{**audit.source_hashes,__file__:sha(__file__)},
                  'seconds':monotonic()-started,
                  'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        temporary = output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump(result,stream,indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(output)
        print({k:result[k] for k in ('status','normal_rank_independently_verified','union_rank_independently_verified','seconds','peak_rss_KiB')},flush=True)
    finally:
        audit.connection.close()
        signal.alarm(0)


if __name__ == '__main__':
    main()
