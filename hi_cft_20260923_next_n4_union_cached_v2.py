"""Root-only source-bound resume with finite-prime whole-field mode caching.

Copies the closed fast N4 checker database to a NEW output, preserves its
existing source_sha256 binding, and separately binds this wrapper/cache
helper and the original checker database under mode_cache_v2.
"""
import argparse
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3

import hi_cft_20260923_next_n4_union_fast as old
import hi_cft_20260923_next_prime_mode_cache as helper


def wrapper_hashes():
    return {str(Path(path).resolve()):old.p.sha(path) for path in (__file__,helper.__file__,old.__file__)}


def migrate(args):
    origin = Path(args.import_checker).resolve()
    destination = Path(args.output).with_suffix('.sqlite')
    assert destination.resolve() != origin
    assert origin.stat().st_size <= 64*old.p.MIB
    assert not Path(str(origin)+'-journal').exists(),'Close the original checker before migration'
    digest = old.p.sha(origin)
    bindings = wrapper_hashes()
    if destination.exists():
        connection = sqlite3.connect(destination)
        try:
            meta = json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            lineage = meta['mode_cache_v2']
            assert lineage['source_sha256'] == bindings
            assert lineage['ancestor_database_sha256'] == digest
        finally:
            connection.close()
        return
    source = sqlite3.connect(origin.as_uri()+'?mode=ro&immutable=1',uri=True)
    source.execute('PRAGMA cache_size=-4096')
    source.execute('PRAGMA mmap_size=0')
    meta = json.loads(source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
    assert meta['format'] == 'n4-union-int64-v1' and meta['status'] != 'complete'
    assert 'failure' not in meta
    for path,expected in meta['source_sha256'].items():
        assert old.p.sha(path) == expected,path
    assert source.execute('SELECT count(*) FROM checks').fetchone()[0] == meta['cursor']
    assert not source.execute("SELECT 1 FROM checks WHERE residual != '[]' LIMIT 1").fetchone()
    meta['mode_cache_v2'] = {'format':'prime-composite-mode-cache-v2','source_sha256':bindings,
                           'ancestor_database':str(origin),'ancestor_database_sha256':digest,
                           'ancestor_metadata_sha256':hashlib.sha256(old.p.compact(meta).encode()).hexdigest(),
                           'imported_cursor':meta['cursor'],'controls':None}
    meta['status'] = 'running'
    temporary = destination.with_suffix('.sqlite.importing')
    if temporary.exists():
        temporary.unlink()
    journal = Path(str(temporary)+'-journal')
    if journal.exists():
        journal.unlink()
    target = sqlite3.connect(temporary)
    try:
        source.backup(target,pages=256)
        target.execute('PRAGMA synchronous=FULL')
        target.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(old.p.compact(meta),))
        target.commit()
    finally:
        target.close()
        source.close()
    os.replace(temporary,destination)
    assert old.p.sha(origin) == digest


def controls(checker,cache):
    # Five distinct left fields, each tested on a full vector and a rescaled
    # vector. The second call exercises cache hits and plain-int coefficients.
    names = checker.frozen['order']['3'][634:]
    zero = [name for name in names if old.p.x.weight(next(iter(checker.inputs[name]))) == (0,0)]
    assert zero
    records = []
    nonzero = 0
    for j,op in enumerate((0,4,7,8,9)):
        name = zero[j % len(zero)]
        left,right = checker.ops[op][0],checker.inputs[name]
        for scale in (1,7):
            vector = right if scale == 1 else {s:int(c)*scale % old.P for s,c in right.items()}
            expected = {s:int(c) for s,c in cache.original_mode(left,0,vector).items() if c}
            actual = cache.mode(left,0,vector)
            assert actual == expected,('Composite cache oracle mismatch',op,name,scale)
            nonzero += bool(actual)
            record = [[list(s[0]),list(s[1]),c] for s,c in sorted(actual.items())]
            records.append({'operator':op,'exact_input':name,'scale':scale,'mode':0,
                            'terms':len(actual),'sha256':hashlib.sha256(old.p.compact(record).encode()).hexdigest()})
    assert len(records) == 10 and nonzero >= 3
    assert cache.statistics()['basis_cache_hits'] > 0
    checker.meta['mode_cache_v2']['controls'] = {'whole_vector_comparisons':10,'nonzero_comparisons':nonzero,
                                               'all_equal_to_original_mode':True,'records':records}


class CachedChecker(old.Checker):
    def save(self,reason,status='running'):
        if hasattr(self,'mode_cache'):
            self.meta['mode_cache_v2']['cache_statistics'] = self.mode_cache.statistics()
        super().save(reason,status)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--import-checker',default='hi_cft_20260923_next_n4_union_fast.sqlite')
    parser.add_argument('--output',default='hi_cft_20260923_next_n4_union_cached_v2.json')
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('cached N4 hard alarm')))
    signal.alarm(args.seconds)
    checker = None
    try:
        migrate(args)
        assert old.p.g3.install_prime(old.P) == [231543,1000]
        old.p.x.creation = lru_cache(maxsize=128)(old.p.e4.creation.__wrapped__)
        old.p.e4.creation = old.p.x.creation
        old.p.x.vertex = lru_cache(maxsize=512)(old.p.e4.vertex.__wrapped__)
        old.p.x.basis_mode = lru_cache(maxsize=512)(old.p.e4.basis_mode.__wrapped__)
        checker = CachedChecker(args)
        assert checker.meta['mode_cache_v2']['source_sha256'] == wrapper_hashes()
        cache = helper.PrimeModeCache(old.p.x,old.P,max_terms=300000,max_entries=50000)
        checker.mode_cache = cache
        for left,_ in checker.ops:
            cache.register(left)
        controls(checker,cache)
        checker.save('Ten whole-vector composite-cache oracle checks passed')
        # Install only after fields have been loaded and controls have passed.
        old.p.x.mode = cache.mode
        checker.run()
    except (old.Stop,helper.CacheLimit) as error:
        signal.alarm(0)
        if checker is None:
            raise
        checker.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if checker is not None:
            checker.db.rollback()
            print({'status':'interrupted','action':'Prior cached-checker atomic checkpoint retained'},flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if checker is not None:
            checker.db.close()
            checker.source.close()


if __name__ == '__main__':
    main()
