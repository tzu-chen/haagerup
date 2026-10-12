"""Root-only new-output resume of the selected N5 pilot with prime mode caching.

The old selected-pilot source bindings stay unchanged. Wrapper/helper and
closed ancestor database hashes are separately bound under mode_cache_v2.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3

import hi_cft_20260923_next_n5_selected_pilot as old
import hi_cft_20260923_next_prime_mode_cache as helper


def wrapper_hashes():
    return {str(Path(path).resolve()):old.p.sha(path)
            for path in (__file__,helper.__file__,old.__file__)}


def migrate(args):
    origin = Path(args.import_pilot).resolve()
    destination = Path(args.output).with_suffix('.sqlite')
    assert destination.resolve() != origin
    assert origin.stat().st_size <= 512*old.MIB
    assert not Path(str(origin)+'-journal').exists(),'Close the original N5 writer first'
    digest,bindings = old.p.sha(origin),wrapper_hashes()
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
    assert meta['format'] == old.FORMAT and meta['prime'] == old.p.PRIME
    assert meta['status'] not in ('targets_contained','explicit_columns_exhausted')
    assert meta['targets_ready'] and meta['target_count'] == 3
    assert meta['operators'] == [7]
    assert source.execute('SELECT count(*) FROM rows').fetchone()[0] == meta['normal_rank']
    assert source.execute('SELECT count(*) FROM targets').fetchone()[0] == 3
    for path,digest_expected in meta['source_sha256'].items():
        assert old.p.sha(path) == digest_expected,path
    metadata_digest = hashlib.sha256(old.compact(meta).encode()).hexdigest()
    meta['mode_cache_v2'] = {'format':'selected-n5-prime-mode-cache-v2',
                           'source_sha256':bindings,'ancestor_database':str(origin),
                           'ancestor_database_sha256':digest,
                           'ancestor_metadata_sha256':metadata_digest,
                           'imported_cursor':meta['cursor'],'controls':None}
    meta['status'] = 'running'
    temporary = destination.with_suffix('.sqlite.importing')
    if temporary.exists():
        temporary.unlink()
    target = sqlite3.connect(temporary)
    try:
        source.backup(target,pages=256)
        target.execute('PRAGMA synchronous=FULL')
        target.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(old.compact(meta),))
        target.commit()
    finally:
        target.close()
        source.close()
    os.replace(temporary,destination)
    assert old.p.sha(origin) == digest


def controls(pilot,cache):
    # Two S2(-1)S3 cases, one K(-1)rawN4 case, two A0P4 cases.
    # Each is checked at scales1 and7: ten original-oracle comparisons.
    neutral2 = [name for name in pilot.frozen['order']['2']
                if old.p.x.weight(next(iter(pilot.inputs[name]))) == (0,0)]
    neutral3 = [name for name in pilot.frozen['order']['3']
                if old.p.x.weight(next(iter(pilot.inputs[name]))) == (0,0)]
    neutral2.sort(key=lambda name:(len(pilot.inputs[name]),name))
    neutral3.sort(key=lambda name:(len(pilot.inputs[name]),name))
    assert len(neutral2) >= 2 and neutral3
    cases = [('S2_minus1_S3',pilot.inputs[name],-1,pilot.inputs[neutral3[0]],
              {'left':name,'right':neutral3[0]}) for name in neutral2[:2]]
    row_id, = pilot.source.execute('SELECT id FROM rows ORDER BY id LIMIT 1').fetchone()
    cases.append(('K_minus1_rawN4',old.p.x.LEFT[0],-1,pilot.source_vector('rows',row_id),
                  {'current':0,'source4_id':row_id}))
    for field in ('P4_plus','P4_zero'):
        cases.append(('S2_zero_P4',pilot.ops[7][0],0,pilot.p4_fields[field],
                      {'operator':7,'P4':field}))
    records,nonzero = [],0
    for kind,left,n,right,recipe in cases:
        for scale in (1,7):
            vector = right if scale == 1 else {s:int(c)*scale % old.p.PRIME for s,c in right.items()}
            expected = {s:int(c) for s,c in cache.original_mode(left,n,vector).items() if c}
            actual = cache.mode(left,n,vector)
            assert actual == expected,('N5 composite cache oracle mismatch',kind,recipe,scale)
            nonzero += bool(actual)
            record = [[list(s[0]),list(s[1]),c] for s,c in sorted(actual.items())]
            records.append({'kind':kind,'recipe':recipe,'mode':n,'scale':scale,
                            'terms':len(actual),'sha256':hashlib.sha256(old.compact(record).encode()).hexdigest()})
    assert len(records) == 10 and nonzero >= 6
    assert cache.statistics()['basis_cache_hits'] > 0
    pilot.meta['mode_cache_v2']['controls'] = {'whole_vector_comparisons':10,
                                             'nonzero_comparisons':nonzero,
                                             'all_equal_to_original_mode':True,'records':records}


class CachedPilot(old.Pilot):
    def save(self,reason,status='running'):
        if hasattr(self,'mode_cache'):
            self.meta['mode_cache_v2']['cache_statistics'] = self.mode_cache.statistics()
        super().save(reason,status)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--import-pilot',default='hi_cft_20260923_next_n5_selected_pilot.sqlite')
    parser.add_argument('--source-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--p4-summary',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--p4-vectors',default='hi_cft_20260923_next_structure_p4_controls.vectors.json.gz')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--operators',default='7')
    parser.add_argument('--output',default='hi_cft_20260923_next_n5_cached_v2.json')
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    assert args.operators == '7' and 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('cached N5 hard alarm')))
    signal.alarm(args.seconds)
    pilot = None
    try:
        migrate(args)
        assert old.p.g3.install_prime(old.p.PRIME) == [231543,1000]
        old.install_modes()
        pilot = CachedPilot(args)
        assert pilot.meta['mode_cache_v2']['source_sha256'] == wrapper_hashes()
        cache = helper.PrimeModeCache(old.p.x,old.p.PRIME,max_terms=300000,max_entries=50000)
        pilot.mode_cache = cache
        for name in pilot.frozen['order']['2']:
            cache.register(pilot.inputs[name])
        for left in old.p.x.LEFT+old.p.x.RIGHT:
            cache.register(left)
        for left,_ in pilot.ops:
            cache.register(left)
        # Pilot.run creates one additional omega dictionary, registered lazily.
        assert cache.statistics()['registered_left_fields'] <= 136
        controls(pilot,cache)
        pilot.save('Ten grade-five whole-mode cache oracle checks passed')
        old.p.x.mode = cache.mode
        pilot.run()
    except (old.p.Stop,helper.CacheLimit) as error:
        signal.alarm(0)
        if pilot is None:
            raise
        pilot.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if pilot is not None:
            pilot.db.rollback()
            print({'status':'interrupted','action':'Prior cached-N5 atomic checkpoint retained'},flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if pilot is not None:
            pilot.db.close()
            pilot.source.close()


if __name__ == '__main__':
    main()
