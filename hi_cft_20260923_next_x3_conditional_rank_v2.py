"""Import frozen X3 v1 prefix and continue with a measured 4m-term budget.

Root-only safe_run job; hard AS<=3 GiB, RSS review1 GiB, alarm<=600s.
V1 producer and all its input sources remain immutable and source-bound.
The inherited sparse rank/mode algorithms are unchanged. JSONL import and
resume stream one bounded line at a time, never the entire vector file.
"""
import argparse
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_next_x3_conditional_rank as v1


FORMAT = 'x3-word-span-v2'
TERM_CAP = 4000000
MAX_RECORD_BYTES = 2*1024**2
MAX_RECORD_FILE_BYTES = 384*1024**2
MAX_SUMMARY_BYTES = 16*1024**2


def read_summary(path):
    path = Path(path)
    assert path.stat().st_size < MAX_SUMMARY_BYTES
    return json.loads(path.read_text())


def atomic_summary(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix+'.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def bounded_lines(stream, committed_bytes):
    assert 0 <= committed_bytes <= MAX_RECORD_FILE_BYTES
    while stream.tell() < committed_bytes:
        line = stream.readline(MAX_RECORD_BYTES+1)
        assert len(line) <= MAX_RECORD_BYTES, 'Individual JSONL record cap'
        assert line.endswith(b'\n') and stream.tell() <= committed_bytes
        yield line
    assert stream.tell() == committed_bytes


def import_v1(args, inherited_hashes, source_hashes):
    """Copy only the authenticated prefix; never mutate v1 checkpoint files."""
    output = Path(args.output)
    records_path = output.with_suffix('.vectors.jsonl')
    old_path = Path(args.import_checkpoint)
    assert output.resolve() != old_path.resolve()
    old = read_summary(old_path)
    assert old['format'] == 'x3-word-span-v1'
    assert old['source_sha256'] == inherited_hashes
    assert old['prime'] == v1.PRIME
    assert old['combined_terms'] <= 2000000
    old_records = Path(old['records_file'])
    assert records_path.resolve() != old_records.resolve()
    assert old_records.stat().st_size >= old['records_bytes']
    assert old['records_bytes'] <= MAX_RECORD_FILE_BYTES
    ancestry = {'certificate_file': str(old_path),
                'certificate_sha256': v1.file_hash(old_path),
                'producer_file': str(Path(v1.__file__)),
                'producer_sha256': v1.file_hash(v1.__file__),
                'records_file': str(old_records),
                'records_bytes': old['records_bytes'],
                'records_prefix_sha256': old['records_sha256'],
                'imported_rank': old['rank_lower_bound'],
                'imported_combined_terms': old['combined_terms'],
                'old_term_cap': 2000000, 'new_term_cap': TERM_CAP}
    if output.exists():
        current = read_summary(output)
        assert current['v1_ancestry'] == ancestry
        return ancestry

    # A crash between records-rename and summary-rename can leave exactly
    # this imported prefix. Authenticate it rather than overwriting it.
    if records_path.exists():
        assert records_path.stat().st_size == old['records_bytes']
        assert v1.file_hash(records_path) == old['records_sha256']
    else:
        temporary = records_path.with_suffix(records_path.suffix+'.import.tmp')
        prefix_hash = hashlib.sha256()
        with old_records.open('rb') as source, temporary.open('wb') as target:
            for line in bounded_lines(source, old['records_bytes']):
                prefix_hash.update(line)
                target.write(line)
            target.flush()
            os.fsync(target.fileno())
        assert prefix_hash.hexdigest() == old['records_sha256']
        temporary.replace(records_path)
    copied = dict(old)
    copied.update({'format': FORMAT, 'source_sha256': source_hashes,
                   'records_file': str(records_path), 'status': 'bounded_stop',
                   'combined_term_cap': TERM_CAP, 'stop_rank': args.stop_rank,
                   'v1_ancestry': ancestry,
                   'import_scope': 'Unchanged raw/echelon rows and word DAG from the authenticated v1 prefix; no modes or eliminations recomputed during import.'})
    atomic_summary(output, copied)
    return ancestry


class Database(v1.Database):
    def __init__(self, args, inputs, operators, source_hashes, ancestry):
        self.ancestry = ancestry
        super().__init__(args, inputs, operators, source_hashes)
        self.meta['v1_ancestry'] = ancestry
        self.meta['stop_rank'] = args.stop_rank
        self.meta['import_scope'] = 'Frozen v1 prefix imported without recomputing its mode words or elimination rows; subsequent records use the same source-hashed mode/rank algorithms.'

    def load(self):
        saved = read_summary(self.output)
        assert saved['format'] == FORMAT
        assert saved['source_sha256'] == self.source_hashes
        assert saved['v1_ancestry'] == self.ancestry
        assert saved['prime'] == v1.PRIME and saved['combined_terms'] <= TERM_CAP
        assert Path(saved['records_file']) == self.records_path
        assert saved['status'] != 'complete', 'All listed words already exhausted'
        assert saved['rank_lower_bound'] < self.args.stop_rank, 'Requested threshold already reached'
        self.states = [(tuple(a), tuple(o)) for a, o in saved['states']]
        self.ids = {s: i for i, s in enumerate(self.states)}
        assert len(self.ids) == len(self.states) <= v1.AMBIENT
        assert all(v1.x.grade(s) == 3 for s in self.states)
        self.weights = [v1.x.weight(s) for s in self.states]
        self.records = self.records_path.open('r+b')
        for line in bounded_lines(self.records, saved['records_bytes']):
            self.hash.update(line)
            row = json.loads(line)
            assert row['id'] == len(self.raw)
            assert v1.digest(row['vector']) == row['vector_sha256']
            assert v1.digest(row['echelon_row']) == row['echelon_row_sha256']
            raw, reduced = dict(row['vector']), dict(row['echelon_row'])
            assert len(raw) == len(row['vector'])
            assert len(reduced) == len(row['echelon_row'])
            weight, pivot = tuple(row['Cartan_weight']), row['pivot_state_id']
            for vector in (raw, reduced):
                assert vector and all(0 <= i < len(self.states) and 0 < c < v1.PRIME
                                      for i, c in vector.items())
                assert all(self.weights[i] == weight for i in vector)
            assert reduced[pivot] == 1
            assert min(reduced, key=lambda i: self.states[i]) == pivot
            assert pivot not in self.rows.setdefault(weight, {})
            self.raw.append(raw)
            self.rows[weight][pivot] = reduced
            self.raw_terms += len(raw)
            self.row_terms += len(reduced)
        assert self.hash.hexdigest() == saved['records_sha256']
        assert len(self.raw) == saved['rank_lower_bound']
        assert self.input_terms+self.raw_terms+self.row_terms == saved['combined_terms']
        self.records.truncate(saved['records_bytes'])
        self.records.seek(saved['records_bytes'])
        self.meta = {key: saved[key] for key in self.meta}
        self.meta['status'] = 'running'

    def boundary(self):
        if len(self.raw) >= self.args.stop_rank:
            raise v1.Saturated()
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 1024**2:
            raise v1.BudgetStop('1 GiB RSS review budget reached')
        if monotonic()-self.started >= self.args.seconds:
            raise v1.BudgetStop('time boundary reached')
        if monotonic()-self.last_save >= 30:
            self.save('periodic candidate boundary')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='hi_cft_20260923_next_x3_conditional_rank_v2.json')
    parser.add_argument('--import-checkpoint', default='hi_cft_20260923_next_x3_conditional_rank.json')
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--stop-rank', type=int, choices=(10630, 10631), default=10630,
                        help='10630 certifies conditional equality;10631 tests one rank increase beyond it')
    args = parser.parse_args()
    assert 0 < args.seconds <= 600
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('per-call hard alarm')))
    signal.alarm(args.seconds)
    assert v1.g3.install_prime(v1.PRIME) == [231543, 1000]
    v1.x.creation = v1.g3.creation
    v1.x.vertex = lru_cache(maxsize=4096)(v1.g3.vertex.__wrapped__)
    v1.x.basis_mode = lru_cache(maxsize=4096)(v1.g3.basis_mode.__wrapped__)
    inputs, operators, inherited_hashes = v1.frozen_inputs()
    source_hashes = dict(inherited_hashes)
    source_hashes[str(Path(__file__))] = v1.file_hash(__file__)
    source_hashes[str(Path(args.import_checkpoint))] = v1.file_hash(args.import_checkpoint)
    ancestry = import_v1(args, inherited_hashes, source_hashes)
    # The inherited save/consume methods intentionally bind these two
    # revised bookkeeping constants; TARGET remains the mathematical10630.
    v1.TERM_CAP, v1.FORMAT = TERM_CAP, FORMAT
    db = Database(args, inputs, operators, source_hashes, ancestry)
    try:
        db.save('v2 initialization or committed-prefix reload')
        v1.run(db)
    except v1.Saturated:
        signal.alarm(0)
        db.save('requested threshold reached; finite-field lower rank only', 'saturated')
    except v1.BudgetStop as error:
        signal.alarm(0)
        db.save(str(error), 'bounded_stop')
    except (TimeoutError, MemoryError) as error:
        signal.alarm(0)
        saved = read_summary(db.output)
        saved['status'] = 'bounded_stop'
        saved['last_interruption'] = str(error)
        atomic_summary(db.output, saved)
        print({'status': 'bounded_stop', 'committed_rank': saved['rank_lower_bound'],
               'reason': str(error)}, flush=True)
    finally:
        signal.alarm(0)
        db.records.close()


if __name__ == '__main__':
    main()
