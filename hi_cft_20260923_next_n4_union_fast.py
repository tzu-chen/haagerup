"""Root-only finite-prime A0P3 checks against the closed N4+P4 word span.

Exact int64 dot products accelerate elimination inside small Cartan blocks.
No floating arithmetic is used.  This remains a modular membership pilot,
never a characteristic-zero containment or properness certificate.
"""
import argparse
from collections import OrderedDict
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import numpy as np

import hi_cft_20260923_next_n4_strong_pilot as p

P = p.PRIME
MAX_RANK = 320
MAX_WIDTH = 4096
CACHE_BYTES = 64*1024**2


class Stop(Exception):
    pass


class Checker:
    def __init__(self, args):
        self.args = args
        self.started = self.last_save = monotonic()
        path = Path(args.database).resolve()
        assert path.stat().st_size <= 512*p.MIB
        assert not Path(str(path)+'-journal').exists()
        self.source = sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1', uri=True)
        self.source.execute('PRAGMA cache_size=-4096')
        self.source.execute('PRAGMA mmap_size=0')
        self.pm = json.loads(self.source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert self.pm['normal_span_complete'] and self.pm['prime'] == P
        assert self.pm['normal_rank']+self.pm['extra_rank'] == 6010
        for source, digest in self.pm['source_sha256'].items():
            assert p.sha(source) == digest
        args.checkpoint = str(Path(self.pm['checkpoint_manifest']).parent)
        self.frozen, self.inputs, self.ops, _, terms = p.read_inputs(args)
        assert terms <= 300000
        self.states = {}
        for idx, record in self.source.execute('SELECT id,value FROM states ORDER BY id'):
            a, o = json.loads(record)
            self.states[idx] = (tuple(a), tuple(o))
        assert len(self.states) <= 71052
        self.state_ids = {s: i for i, s in self.states.items()}
        self.blocks = {}
        for table in ('rows', 'extras'):
            for idx, w0, w1, pivot in self.source.execute(f'SELECT id,w0,w1,pivot FROM {table} ORDER BY id'):
                self.blocks.setdefault((w0,w1), []).append((table, idx, pivot))
        assert sum(map(len, self.blocks.values())) == 6010
        self.work = []
        for op, (left, _) in enumerate(self.ops):
            weights = {p.x.weight(s) for s in left}
            assert len(weights) == 1
            lw = weights.pop()
            for name in self.frozen['order']['3'][634:]:
                rw = p.x.weight(next(iter(self.inputs[name])))
                self.work.append((tuple(a+b for a,b in zip(lw,rw)),op,name))
        self.work.sort()
        assert len(self.work) == 3220
        self.cache, self.cache_bytes = OrderedDict(), 0
        self.output = Path(args.output)
        self.db = sqlite3.connect(self.output.with_suffix('.sqlite'))
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('PRAGMA cache_size=-4096')
        self.db.execute('PRAGMA mmap_size=0')
        assert self.db.execute('PRAGMA page_size').fetchone()[0] == 4096
        self.db.execute('PRAGMA max_page_count=16384')
        self.db.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY,value TEXT)')
        self.db.execute('CREATE TABLE IF NOT EXISTS checks (id INTEGER PRIMARY KEY,word TEXT,raw_digest TEXT,residual TEXT)')
        self.db.commit()
        bindings = {**self.pm['source_sha256'], str(path): p.sha(path), str(Path(__file__).resolve()): p.sha(__file__)}
        saved = self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if saved:
            self.meta = json.loads(saved[0])
            assert self.meta['format'] == 'n4-union-int64-v1'
            assert self.meta['source_sha256'] == bindings
            assert self.meta['status'] != 'complete'
        else:
            assert not self.db.execute('SELECT 1 FROM checks LIMIT 1').fetchone()
            self.meta = {'format':'n4-union-int64-v1', 'source_sha256':bindings,
                         'cursor':0, 'seconds':0, 'mode_seconds':0, 'reduction_seconds':0,
                         'history':[], 'status':'running', 'normal_rank':self.pm['normal_rank'],
                         'extra_rank':self.pm['extra_rank'], 'total_targets':3220,
                         'scope':'Finite-prime membership in 6010 actual U words. No characteristic-zero containment or upper-rank claim.'}
        self.save('initialized or resumed')

    def block(self, weight):
        if weight in self.cache:
            self.cache.move_to_end(weight)
            return self.cache[weight][0]
        descriptors = self.blocks.get(weight, [])
        assert len(descriptors) <= MAX_RANK
        if not descriptors:
            return None
        support = set()
        for table, idx, _ in descriptors:
            blob, = self.source.execute(f'SELECT reduced FROM {table} WHERE id=?', (idx,)).fetchone()
            support.update(i for i, _ in p.unpack(blob))
        assert len(support) <= MAX_WIDTH
        ids = sorted(support)
        lookup = {idx: j for j,idx in enumerate(ids)}
        r, width = len(descriptors), len(ids)
        matrix = np.zeros((r,width), dtype=np.int64)
        pivots = []
        for row, (table, idx, pivot) in enumerate(descriptors):
            blob, = self.source.execute(f'SELECT reduced FROM {table} WHERE id=?', (idx,)).fetchone()
            for sid, c in p.unpack(blob):
                assert 0 < c < P
                matrix[row,lookup[sid]] = c
            pivots.append(lookup[pivot])
            assert matrix[row,pivots[-1]] == 1
            assert not np.any(matrix[row,pivots[:-1]])
        # Every sum below has at most320 terms, each below p^2.
        # Both signed subtraction and nonnegative dot products fit int64.
        assert r*(P-1)**2 < 2**62
        result = (matrix, lookup, ids, pivots)
        size = matrix.nbytes+256*width+128*r
        while self.cache and self.cache_bytes+size > CACHE_BYTES:
            _, (_, old_size) = self.cache.popitem(last=False)
            self.cache_bytes -= old_size
        if size <= CACHE_BYTES:
            self.cache[weight] = (result,size)
            self.cache_bytes += size
        return result

    def reduce(self, vector, weight):
        block = self.block(weight)
        if block is None:
            return dict(vector)
        matrix, lookup, ids, pivots = block
        r = len(pivots)
        raw = np.zeros(len(ids), dtype=np.int64)
        outside = {}
        for state, value in vector.items():
            sid = self.state_ids.get(state)
            column = lookup.get(sid)
            if column is None:
                outside[state] = int(value)
            else:
                raw[column] = int(value)
        coefficients = np.zeros(r, dtype=np.int64)
        for j in range(r):
            coefficients[j] = (int(raw[pivots[j]])-int(np.dot(coefficients[:j],matrix[:j,pivots[j]]))) % P
        residual = (raw-coefficients@matrix) % P
        assert not np.any(residual[pivots])
        for j in np.flatnonzero(residual):
            outside[self.states[ids[int(j)]]] = int(residual[j])
        return outside

    def save(self, reason, status='running'):
        now = monotonic()
        self.meta['seconds'] += now-self.last_save
        self.last_save = now
        self.meta.update(status=status, reason=reason,
                         peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                         sqlite_file=str(self.output.with_suffix('.sqlite')))
        self.meta['history'].append({'cursor':self.meta['cursor'], 'seconds':self.meta['seconds'], 'reason':reason})
        self.db.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(p.compact(self.meta),))
        self.db.commit()
        temporary = self.output.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(self.meta,indent=2)+'\n')
        temporary.replace(self.output)
        p.clear_caches()
        print({'status':status, 'cursor':self.meta['cursor'], 'seconds':self.meta['seconds'],
               'mode_seconds':self.meta['mode_seconds'], 'reduction_seconds':self.meta['reduction_seconds'],
               'reason':reason},flush=True)

    def run(self):
        while self.meta['cursor'] < len(self.work):
            index = self.meta['cursor']
            weight, op, name = self.work[index]
            tick = monotonic()
            target = p.x.mode(self.ops[op][0],0,self.inputs[name])
            self.meta['mode_seconds'] += monotonic()-tick
            assert len(target) <= 20000
            assert all(p.x.grade(s) == 4 and p.x.weight(s) == weight for s in target)
            tick = monotonic()
            residual = self.reduce(target,weight)
            self.meta['reduction_seconds'] += monotonic()-tick
            record = [[list(s[0]),list(s[1]),int(c)] for s,c in sorted(target.items())]
            out = [[list(s[0]),list(s[1]),int(c)] for s,c in sorted(residual.items())]
            self.db.execute('INSERT INTO checks VALUES (?,?,?,?)',
                            (index,p.compact((op,name)),hashlib.sha256(p.compact(record).encode()).hexdigest(),p.compact(out)))
            self.meta['cursor'] += 1
            if residual:
                self.meta['failure'] = {'word':[op,name], 'weight':weight, 'residual_terms':len(residual),
                                        'union_rank_lower_bound':6011}
                self.save('Target outside the 6010-word union span','failed')
                return
            if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 768*1024:
                raise Stop('768 MiB RSS boundary')
            if monotonic()-self.started >= self.args.seconds:
                raise Stop('requested time boundary')
            if monotonic()-self.last_save >= 20:
                self.save('periodic membership boundary')
        self.save('All3220 A0P3 targets belong to the modular 6010-word union span','complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--output',default='hi_cft_20260923_next_n4_union_fast.json')
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    checker = None
    try:
        assert p.g3.install_prime(P) == [231543,1000]
        p.x.creation = lru_cache(maxsize=128)(p.e4.creation.__wrapped__)
        p.e4.creation = p.x.creation
        p.x.vertex = lru_cache(maxsize=512)(p.e4.vertex.__wrapped__)
        p.x.basis_mode = lru_cache(maxsize=512)(p.e4.basis_mode.__wrapped__)
        checker = Checker(args)
        checker.run()
    except Stop as error:
        signal.alarm(0)
        checker.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if checker is None:
            raise
        checker.db.rollback()
        print({'status':'interrupted','action':'prior atomic checkpoint retained'},flush=True)
    finally:
        signal.alarm(0)
        if checker is not None:
            checker.db.close()
            checker.source.close()


if __name__ == '__main__':
    main()
