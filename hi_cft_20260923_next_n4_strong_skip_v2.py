"""Source-bound migration of the closed N4 pilot, skipping stable descendants.

Root-only consumer. The frozen producer remains unchanged. New database,
old database SHA256, exact lower-current closure premise, and new source
hashes record why a block of redundant lowering candidates is skipped.
All original numerical, memory, cache, disk and alarm caps remain in force.
"""
import argparse
from functools import lru_cache
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3

import hi_cft_20260923_next_n4_strong_pilot as p


NOTE = Path('hi_cft_20260923_next_n4_strong_skip_v2.md')


def migrate(args,old_hashes,new_hashes):
    destination = Path(args.output).with_suffix('.sqlite')
    origin = Path(args.input_database).resolve()
    assert destination.resolve() != origin
    assert origin.stat().st_size <= 512*p.MIB
    assert not Path(str(origin)+'-journal').exists(),'Close the original producer before migration'
    original_digest = p.sha(origin)
    if destination.exists():
        connection = sqlite3.connect(destination)
        previous = json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        connection.close()
        assert previous['source_sha256'] == new_hashes
        assert previous['migration_v2']['source_database_sha256'] == original_digest
        return
    source = sqlite3.connect(origin.as_uri()+'?mode=ro&immutable=1',uri=True)
    source.execute('PRAGMA cache_size=-4096')
    source.execute('PRAGMA mmap_size=0')
    meta = json.loads(source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
    assert meta['format'] == p.FORMAT and meta['prime'] == p.PRIME
    assert meta['source_sha256'] == old_hashes
    assert 2 <= meta['stage'] < 5,'Migration requires completed normal seeding and an unfinished test/closure stage'
    completed = [h for h in meta['history'] if h['reason'] == 'stage complete' and h['stage'] == 1]
    assert len(completed) == 1
    base_rank = completed[0]['rank']
    assert 0 < base_rank <= meta['normal_rank']
    for expected,(idx,word_json) in enumerate(source.execute('SELECT id,word FROM rows WHERE id<? ORDER BY id',(base_rank,))):
        assert idx == expected
        word = json.loads(word_json)
        assert word['kind'] == 'normal_descendant'
        assert word['exact_input'].startswith('r3_')
        assert word['mode'] == (-1 if word['operator'] < 6 else 0)
    assert source.execute('SELECT COUNT(*) FROM rows WHERE id<?',(base_rank,)).fetchone()[0] == base_rank
    before = meta['closure_cursor']
    after = max(before,2*base_rank) if meta['stage'] == 2 else before
    meta['closure_cursor'] = after
    meta['source_sha256'] = new_hashes
    meta['status'] = 'running'
    meta['migration_v2'] = {'source_database':str(origin),'source_database_sha256':original_digest,
                           'source_metadata_sha256':p.hashlib.sha256(p.compact(json.loads(source.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])).encode()).hexdigest(),
                           'ancestor_source_sha256':old_hashes,'descendant_rank':base_rank,
                           'closure_cursor_before':before,'closure_cursor_after':after,
                           'skipped_unprocessed_lowering_candidates':after-before,
                           'proof_note':str(NOTE),'proof_note_sha256':p.sha(NOTE),
                           'reason':'The first descendant span K(-1)S3+T S3 is invariant under both lowering zero modes, by exact frozen S3 lowering closure and the current/translation commutators.'}
    temporary = destination.with_suffix('.sqlite.importing')
    if temporary.exists():
        temporary.unlink()
    target = sqlite3.connect(temporary)
    try:
        source.backup(target,pages=256)
        target.execute('PRAGMA synchronous=FULL')
        target.execute('INSERT OR REPLACE INTO meta VALUES (1,?)',(p.compact(meta),))
        target.commit()
    finally:
        target.close()
        source.close()
    os.replace(temporary,destination)
    assert p.sha(origin) == original_digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-database',default='hi_cft_20260923_next_n4_strong_pilot.sqlite')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--output',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--seconds',type=int,default=600)
    parser.add_argument('--stop-on-first-residual',action='store_true')
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('v2 hard call alarm')))
    signal.alarm(args.seconds)
    db = None
    try:
        assert p.g3.install_prime(p.PRIME) == [231543,1000]
        p.x.creation = lru_cache(maxsize=128)(p.e4.creation.__wrapped__)
        p.e4.creation = p.x.creation
        p.x.vertex = lru_cache(maxsize=512)(p.e4.vertex.__wrapped__)
        p.x.basis_mode = lru_cache(maxsize=512)(p.e4.basis_mode.__wrapped__)
        meta,rows,operators,old_hashes,terms = p.read_inputs(args)
        assert meta['closed_lower3'] == meta['dimensions']['3'] == 956
        new_hashes = {**old_hashes,str(__file__):p.sha(__file__),str(NOTE):p.sha(NOTE)}
        migrate(args,old_hashes,new_hashes)
        db = p.Database(args,(meta,rows,operators,new_hashes,terms))
        db.save('v2 authenticated migration; invariant descendant lowering skipped')
        p.run(db)
    except p.Stop as error:
        signal.alarm(0)
        if db is None:
            raise
        db.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        if db is not None:
            db.conn.rollback()
            print({'status':'interrupted','action':'Prior atomic v2 checkpoint retained'},flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if db is not None:
            db.conn.close()


if __name__ == '__main__':
    main()
