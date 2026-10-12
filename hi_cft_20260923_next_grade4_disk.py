"""Disk-backed continuation of the frozen exact grade-four calculation.

Exact arithmetic and generation order are unchanged. Logical Cartan blocks
live in an indexed SQLite row store; only a bounded LRU of decoded rows is
resident. Oversized blocks are streamed row by row. A SQLite transaction
commits accepted rows, provenance, and the matching generation cursor together.
The old checkpoint is read-only. Run exclusively via hi_cft_safe_run.py.
"""
import argparse
from collections import OrderedDict
import gzip
import json
import os
from functools import lru_cache
from pathlib import Path
import resource
import signal
import sqlite3
import sys
from time import monotonic
import zlib

import hi_cft_20260923_next_grade4_exact as old

x = old.x
FORMAT = 'exact-cartan-sqlite-v1'
MIB = 1024 ** 2
MAX_ROW_JSON = 8 * MIB
MAX_ROW_TERMS = 12000


def row_stream(path):
    """Read the frozen compact block JSON without loading its rows array."""
    decoder = json.JSONDecoder()
    with gzip.open(path, 'rt', encoding='utf-8') as f:
        buffer = ''
        marker = '"rows":['
        while marker not in buffer:
            chunk = f.read(65536)
            if not chunk:
                raise ValueError('missing rows array: ' + str(path))
            buffer += chunk
            if len(buffer) > 131072:
                raise ValueError('oversized block header')
        buffer = buffer.split(marker, 1)[1]
        while True:
            buffer = buffer.lstrip(' \r\n\t,')
            if buffer.startswith(']'):
                assert (buffer[1:] + f.read(32)).strip() == '}'
                return
            try:
                row, end = decoder.raw_decode(buffer)
            except json.JSONDecodeError:
                if len(buffer) >= MAX_ROW_JSON:
                    raise old.BudgetStop('input JSON row exceeded 8 MiB cap')
                chunk = f.read(min(65536, MAX_ROW_JSON - len(buffer)))
                if not chunk:
                    raise ValueError('truncated JSON row')
                buffer += chunk
                continue
            if end > MAX_ROW_JSON:
                raise old.BudgetStop('input JSON row exceeded 8 MiB cap')
            yield row
            buffer = buffer[end:]


def encode_row(row):
    text = json.dumps(row, separators=(',', ':'))
    if len(text) > MAX_ROW_JSON:
        raise old.BudgetStop('serialized row exceeded 8 MiB cap')
    return gzip.compress(text.encode('utf-8'), compresslevel=1)


def decode_row(blob):
    # Bounded output even if a store is corrupt. The digest/source checks are
    # still required; this prevents a decompression bomb from allocating first.
    decoder = zlib.decompressobj(31)
    text = decoder.decompress(blob, MAX_ROW_JSON + 1)
    if len(text) > MAX_ROW_JSON or not decoder.eof or decoder.unconsumed_tail:
        raise old.BudgetStop('compressed row exceeds bounded decoder')
    return json.loads(text)


def estimate_row_bytes(row, nnz=None):
    """Conservative resident accounting, deliberately overcounting shared ints."""
    nnz = len(row['vector']) if nnz is None else nnz
    bits = row.get('coefficient_bits', 2048)
    recipe_size = len(json.dumps({k: v for k, v in row.items() if k != 'vector'}))
    # 1024 covers dict slots, state/oscillator tuples, A and four Fractions;
    # another eight full-height integers cover all rational numerators/denoms.
    return nnz * (1024 + 8 * ((bits + 7) // 8)) + 8 * recipe_size + 4096


class RowProxy:
    def __init__(self, db):
        self.db = db

    def __getitem__(self, name):
        return self.db.get_row(name)

    def __contains__(self, name):
        return name in self.db.row_info


class DiskDatabase(old.Database):
    def __init__(self, args):
        self.args = args
        self.directory = Path(args.store_dir)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.started = self.last_save = monotonic()
        self.steps = 0
        self.stop = False
        self.fields = {}
        self.rows = RowProxy(self)
        self.row_info = {}
        self.blocks = {i: {} for i in range(1, 5)}
        self.order = {i: [] for i in range(1, 5)}
        self.cache = OrderedDict()
        self.cache_bytes = 0
        self.cache_limit = args.cache_mib * MIB
        self.nnz = 0
        self.source_hashes = old.sources()
        self.source_hashes[str(Path(__file__))] = old.sha(__file__)
        self.sql = sqlite3.connect(self.directory / 'span.sqlite3', isolation_level=None)
        self.sql.execute('PRAGMA journal_mode=DELETE')
        self.sql.execute('PRAGMA synchronous=FULL')
        self.sql.execute('PRAGMA cache_size=-8192')
        self.sql.execute('PRAGMA temp_store=FILE')
        self.sql.execute('PRAGMA mmap_size=0')
        page_size, = self.sql.execute('PRAGMA page_size').fetchone()
        self.sql.execute('PRAGMA max_page_count=%d' % (1024 * MIB // page_size))
        self.sql.executescript('''
            CREATE TABLE IF NOT EXISTS state (id INTEGER PRIMARY KEY CHECK(id=1), value TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS fields (id TEXT PRIMARY KEY, ordinal INTEGER NOT NULL, data BLOB NOT NULL);
            CREATE TABLE IF NOT EXISTS rows (
                id TEXT PRIMARY KEY, grade INTEGER NOT NULL, w0 INTEGER NOT NULL, w1 INTEGER NOT NULL,
                pivot TEXT NOT NULL, nnz INTEGER NOT NULL, resident_estimate INTEGER NOT NULL, data BLOB NOT NULL);
            CREATE INDEX IF NOT EXISTS by_block ON rows(grade,w0,w1);
        ''')
        saved = self.sql.execute('SELECT value FROM state WHERE id=1').fetchone()
        self.sql.execute('BEGIN IMMEDIATE')
        if saved:
            self.meta = json.loads(saved[0])
            assert self.meta['format'] == FORMAT
            assert self.meta['sources'] == self.source_hashes, 'frozen source changed'
            self.order = {int(g): v for g, v in self.meta['order'].items()}
            for name, grade, a, b, pivot, terms, estimate in self.sql.execute(
                    'SELECT id,grade,w0,w1,pivot,nnz,resident_estimate FROM rows'):
                self.index_row(name, grade, (a, b), pivot, terms, estimate)
            for _, _, blob in self.sql.execute('SELECT id,ordinal,data FROM fields ORDER BY ordinal'):
                row = decode_row(blob)
                row['vector'] = old.unpacked(row['vector'])
                self.fields[row['id']] = row
            assert self.nnz == self.meta['sparse_terms']
        else:
            if any(self.sql.execute('SELECT id FROM rows LIMIT 1')):
                raise RuntimeError('row store without valid state')
            source_root = Path(args.import_checkpoint)
            source_name = (source_root / 'CURRENT').read_text().strip()
            assert '/' not in source_name and source_name.startswith('checkpoint_')
            self.source_dir = source_root / source_name
            src = json.loads((self.source_dir / 'manifest.json').read_text())
            assert src['format'] == old.FORMAT and src['completed_grade3']
            assert src['sources'] == old.sources()
            assert not src['completed_grade4'] and src['phase'] == 'grade4'
            self.meta = {'format': FORMAT, 'sources': self.source_hashes, 'phase': 'import',
                         'stage': 0, 'cursor': 0, 'history': [], 'audits': {},
                         'completed_grade3': False, 'completed_grade4': False,
                         'import_source': str(self.source_dir), 'import_manifest_sha256': old.sha(self.source_dir / 'manifest.json'),
                         'import_cursor': 0, 'import_row_cursor': 0, 'finite_span_only': True}
            self.save('empty import store initialized')
        if self.meta['phase'] == 'import':
            self.source_dir = Path(self.meta['import_source'])

    def index_row(self, name, grade, w, pivot_json, terms, estimate):
        a, osc = json.loads(pivot_json)
        pivot = tuple(a), tuple(osc)
        block = self.blocks[grade].setdefault(w, {})
        assert pivot not in block and name not in self.row_info
        block[pivot] = name
        self.row_info[name] = (grade, w, terms, estimate)
        self.nnz += terms

    def put_raw_row(self, row):
        name, grade, w = row['id'], row['grade'], tuple(row['weight'])
        assert row['vector'] and len(row['vector']) <= MAX_ROW_TERMS
        # Frozen packed vectors are sorted by exact state tuples.
        a, osc, _ = row['vector'][0]
        pivot = json.dumps([a, osc], separators=(',', ':'))
        estimate = estimate_row_bytes(row)
        self.sql.execute('INSERT INTO rows VALUES(?,?,?,?,?,?,?,?)',
                         (name, grade, *w, pivot, len(row['vector']), estimate, encode_row(row)))
        self.index_row(name, grade, w, pivot, len(row['vector']), estimate)

    def remember(self, name, row):
        grade, w, _, size = self.row_info[name]
        key = grade, w
        if size > self.cache_limit:
            return  # One large row is processed transiently, never cached.
        while self.cache_bytes + size > self.cache_limit:
            oldest = next(iter(self.cache))
            block = self.cache[oldest]
            if oldest == key:
                _, (_, n) = block.popitem(last=False)
                self.cache_bytes -= n
                if not block:
                    del self.cache[oldest]
            else:
                self.cache_bytes -= sum(n for _, n in block.values())
                del self.cache[oldest]
        block = self.cache.setdefault(key, OrderedDict())
        assert name not in block
        block[name] = row, size
        self.cache.move_to_end(key)
        self.cache_bytes += size

    def get_row(self, name):
        grade, w, _, _ = self.row_info[name]
        key = grade, w
        block = self.cache.get(key)
        if block is not None and name in block:
            self.cache.move_to_end(key)
            block.move_to_end(name)
            return block[name][0]
        blob, = self.sql.execute('SELECT data FROM rows WHERE id=?', (name,)).fetchone()
        row = decode_row(blob)
        row['vector'] = old.unpacked(row['vector'])
        self.remember(name, row)
        return row

    def add(self, grade, vector, recipe):
        if not vector:
            return None
        weights = {x.weight(s) for s in vector}
        assert len(weights) == 1 and all(x.grade(s) == grade for s in vector)
        w = next(iter(weights))
        block = self.blocks[grade].setdefault(w, {})
        out = vector.copy()
        elimination = []
        elimination_height = 0
        for pivot, name in sorted(block.items()):
            if pivot in out:
                c = out[pivot]
                elimination_height = max(elimination_height, old.coefficient_bits(c))
                elimination.append([old.coefficient(c), name])
                old.subtract(out, c, self.get_row(name)['vector'])
        if not out:
            return None
        if len(out) > MAX_ROW_TERMS:
            raise old.BudgetStop('single sparse row exceeds 12000-term cap')
        if len(self.order[grade]) >= (7000 if grade == 4 else 1600):
            raise old.BudgetStop('unchanged finite-span rank cap reached')
        scale = out[min(out)].inv()
        out = {s: c * scale for s, c in out.items()}
        height = max(elimination_height, old.coefficient_bits(scale),
                     max(old.coefficient_bits(a) for a in out.values()))
        if height > self.args.max_coefficient_bits:
            raise old.BudgetStop('unchanged coefficient bit-length cap reached')
        name = 'r%d_%06d' % (grade, len(self.order[grade]))
        row = {'id': name, 'grade': grade, 'weight': list(w), 'recipe': recipe,
               'elimination': elimination, 'scale': old.coefficient(scale),
               'vector': out, 'coefficient_bits': height}
        packed_row = {**row, 'vector': old.packed(out)}
        self.put_raw_row(packed_row)
        del packed_row
        self.order[grade].append(name)
        self.meta['largest_saved_coefficient_bits'] = max(
            self.meta.get('largest_saved_coefficient_bits', 0), height)
        self.remember(name, row)
        return name

    def save(self, reason):
        self.meta.update({'reason': reason, 'order': {str(g): v for g, v in self.order.items()},
                          'dimensions': self.counts(), 'sparse_terms': self.nnz,
                          'cache_resident_estimate': self.cache_bytes,
                          'invocation_seconds': monotonic() - self.started,
                          'invocation_steps': self.steps,
                          'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
        # All row writes since the preceding checkpoint and this exact cursor
        # are committed in one transaction. The SQLite state is authoritative.
        text = json.dumps(self.meta, separators=(',', ':'))
        self.sql.execute('INSERT OR REPLACE INTO state VALUES(1,?)', (text,))
        self.sql.execute('COMMIT')
        display = self.directory / 'manifest.json.partial'
        display.write_text(json.dumps(self.meta, indent=2) + '\n')
        display.replace(self.directory / 'manifest.json')
        pointer = self.directory / 'CURRENT.partial'
        pointer.write_text('span.sqlite3\n')
        pointer.replace(self.directory / 'CURRENT')
        self.sql.execute('BEGIN IMMEDIATE')
        old.clear_mode_caches()
        self.last_save = monotonic()
        print(json.dumps({'checkpoint': str(self.directory), 'reason': reason,
                          'dimensions': self.counts(), 'sparse_terms_on_disk': self.nnz,
                          'decoded_cache_estimate_MiB': self.cache_bytes / MIB}), flush=True)

    def import_checkpoint(self):
        source_manifest = self.source_dir / 'manifest.json'
        assert old.sha(source_manifest) == self.meta['import_manifest_sha256']
        src = json.loads(source_manifest.read_text())
        assert src['sources'] == old.sources()
        if not self.fields:
            field_path = self.source_dir / src['field_file']
            assert old.sha(field_path) == src['files_sha256'][src['field_file']]
            with gzip.open(field_path, 'rt') as f:
                text = f.read(16 * MIB + 1)
            assert len(text) <= 16 * MIB, 'field JSON cap'
            for i, row in enumerate(json.loads(text)):
                self.sql.execute('INSERT INTO fields VALUES(?,?,?)', (row['id'], i, encode_row(row)))
                row['vector'] = old.unpacked(row['vector'])
                self.fields[row['id']] = row
            self.save('field provenance imported')
        files = src['block_files']
        for i in range(self.meta['import_cursor'], len(files)):
            self.boundary()
            path = self.source_dir / files[i]
            assert old.sha(path) == src['files_sha256'][files[i]], ('input block hash', files[i])
            for j, row in enumerate(row_stream(path)):
                if j < self.meta.get('import_row_cursor', 0):
                    continue
                self.boundary()
                self.put_raw_row(row)
                self.order[row['grade']].append(row['id'])
                self.meta['import_row_cursor'] = j + 1
            self.meta['import_cursor'] = i + 1
            self.meta['import_row_cursor'] = 0
            self.steps += 1
            # Per-block import commits avoid repeating a large import on timeout.
            self.save('imported ' + files[i])
        assert self.nnz == src['sparse_terms']
        assert set(self.row_info) == {name for names in src['order'].values() for name in names}
        self.order = {int(g): names for g, names in src['order'].items()}
        import_record = {k: v for k, v in self.meta.items() if k.startswith('import_')}
        # Carry the exact old stage/cursor: the existing 836 S4 vectors survive.
        self.meta = {**src, **import_record, 'format': FORMAT, 'sources': self.source_hashes,
                     'storage': 'SQLite logical Cartan blocks; streaming row fallback',
                     'original_sources': src['sources']}
        self.save('frozen exact checkpoint imported; generation cursor retained')

    def close(self):
        # A successful save has already committed. Never commit an unfinished
        # operation merely because the Python context is exiting.
        self.sql.execute('ROLLBACK')
        self.sql.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--store-dir', required=True)
    ap.add_argument('--import-checkpoint', default='hi_cft_20260923_next_grade4_checkpoint')
    ap.add_argument('--phase', choices=('import', 'grade4', 'audit', 'replay'), required=True)
    ap.add_argument('--seconds', type=int, default=300)
    ap.add_argument('--max-steps', type=int, default=100000000)
    ap.add_argument('--checkpoint-seconds', type=int, default=45)
    ap.add_argument('--max-coefficient-bits', type=int, default=2048)
    ap.add_argument('--soft-rss-mib', type=int, default=1800)
    ap.add_argument('--cache-mib', type=int, default=384)
    args = ap.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    assert 0 < cap <= 6 * 1024 ** 3 and len(os.sched_getaffinity(0)) <= 2
    assert 1 <= args.seconds <= 1800 and 10 <= args.checkpoint_seconds <= 120
    assert 64 <= args.soft_rss_mib < cap / MIB
    assert 16 <= args.cache_mib <= 512 and 1 <= args.max_coefficient_bits <= 2048
    old.install()
    x.creation = lru_cache(maxsize=128)(old.e4.creation.__wrapped__)
    x.vertex = lru_cache(maxsize=512)(old.e4.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=1024)(old.e4.basis_mode.__wrapped__)
    db = DiskDatabase(args)

    def stop(*_):
        db.stop = True

    signal.signal(signal.SIGINT, stop)
    signal.signal(signal.SIGTERM, stop)
    try:
        if db.meta['phase'] == 'import':
            db.import_checkpoint()
        if args.phase == 'grade4' and not db.meta['completed_grade4']:
            old.grade4(db)
        elif args.phase == 'audit':
            assert db.meta['completed_grade4']
            if db.meta['phase'] != 'complete':
                old.audits(db)
        elif args.phase == 'replay':
            old.replay(db)
        db.save('requested phase complete')
    except old.BudgetStop as exc:
        db.record('bounded stop: ' + str(exc))
        db.save('bounded stop: ' + str(exc))
        return 75
    finally:
        db.close()
    return 0


if __name__ == '__main__':
    sys.exit(main())
