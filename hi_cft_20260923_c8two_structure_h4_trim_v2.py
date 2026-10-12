"""Root-only H4 continuation with reconstructible caches dropped before FLINT.

Copy a closed targeted-v1 directory into a separately authenticated lineage.
The frozen target loop, native solver and full integer residual are unchanged.
"""
import argparse
import gc
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
import weakref

import hi_cft_20260923_c8two_targeted_h4 as old
import hi_cft_20260923_c8two_structure_saturation as auth

b, bulk = old.b, old.bulk
MIB = 1024**2
STATE = {}


def prepare(origin, destination, request):
    origin, destination, request = map(lambda p: Path(p).resolve(), (origin, destination, request))
    assert origin.is_dir() and origin != destination
    assert origin not in destination.parents and destination not in origin.parents
    assert not any(origin.glob('*-journal')) and not any(origin.glob('*-wal'))
    files = sorted(p for p in origin.iterdir() if p.suffix in ('.json', '.sqlite'))
    assert files and len(files) <= 200
    assert all(p.is_file() and not p.is_symlink() and p.stat().st_size <= 512*MIB for p in files)
    assert sum(p.stat().st_size for p in files) <= 4*1024**3
    legacy = json.loads((origin/'targeted_policy.json').read_text())
    summary = json.loads((origin/'summary.json').read_text())
    assert legacy['format'] == 'targeted-H4-integer-residual-v1'
    assert summary['policy'] == legacy
    assert summary['status'] in ('interrupted_exact_checkpoints_retained', 'bounded_stop',
                                 'all_requested_exact_H4_targets_passed')
    verified = {}
    auth.nested_graphs(legacy, verified)
    assert legacy['source_sha256'][str(request)] == b.sha(request)
    sources = {str(Path(p).resolve()): b.sha(p) for p in
               (__file__, old.__file__, old.v.__file__, old.v.integer.__file__,
                old.v.old.__file__, old.v.old.helper.__file__, auth.__file__, request)}
    lineage = {'format': 'targeted-H4-pre-native-cache-trim-v2',
               'source_sha256': sources,
               'ancestor_directory': str(origin),
               'ancestor_files_sha256': {str(p): b.sha(p) for p in files},
               'legacy_targeted_policy': legacy,
               'scope': 'Only reconstructible caches are discarded before the unchanged native solve.'}
    manifest = destination/'pre_native_trim_lineage.json'
    if destination.exists():
        assert manifest.exists() and json.loads(manifest.read_text()) == lineage
    else:
        temporary = destination.with_name(destination.name+'.importing')
        assert not temporary.exists()
        temporary.mkdir()
        for source in files:
            digest = hashlib.sha256()
            with source.open('rb') as src, (temporary/source.name).open('xb') as dst:
                while chunk := src.read(MIB):
                    digest.update(chunk)
                    dst.write(chunk)
            assert digest.hexdigest() == lineage['ancestor_files_sha256'][str(source)]
            assert b.sha(temporary/source.name) == digest.hexdigest()
        bulk.atomic_json(temporary/'pre_native_trim_lineage.json', lineage)
        temporary.replace(destination)
    return lineage, legacy


class TrimmedSolve:
    """Keep the original native solver API; hold the consumer only weakly."""
    def __init__(self, native, consumer):
        self.native, self.owner = native, weakref.ref(consumer)

    @property
    def version(self):
        return self.native.version

    def solve(self, matrix, rhs):
        owner = self.owner()
        assert owner is not None
        owner.trim_before_native(matrix, rhs)
        return self.native.solve(matrix, rhs)


class Consumer(old.Consumer):
    def __init__(self, args, serial_policy, targeted_policy, selection):
        assert targeted_policy == STATE['legacy']
        super().__init__(args, serial_policy, targeted_policy, selection)
        previous = self.meta.get('pre_native_trim_v2')
        if previous is not None:
            assert previous['policy'] == STATE['lineage']
        else:
            self.meta['pre_native_trim_v2'] = {'policy': STATE['lineage'], 'events': []}
        self.flint = TrimmedSolve(self.flint, self)
        self.save('pre-native cache-trim lineage authenticated')

    def trim_before_native(self, matrix, rhs):
        # The caller already holds the complete matrix, RHS and exact targets.
        # Clearing these memoization tables cannot modify any retained vector.
        assert len(matrix) == len(rhs) == self.r
        assert all(len(row) == self.r for row in matrix)
        assert rhs and 0 < len(rhs[0]) <= 16 and all(len(row) == len(rhs[0]) for row in rhs)
        sizes = {'whole_action': self.exact_cache.bytes,
                 'raw_vectors': self.cache_bytes,
                 'integer_columns': self.integer_engine.bytes}
        counts = {'whole_action': len(self.exact_cache.cache),
                  'raw_vectors': len(self.cache),
                  'integer_columns': len(self.integer_engine.cache)}
        self.exact_cache.cache.clear()
        self.exact_cache.bytes = 0
        self.cache.clear()
        self.cache_bytes = 0
        self.integer_engine.cache.clear()
        self.integer_engine.bytes = 0
        # Denominators are also reconstructible; retaining them is unnecessary.
        self.integer_engine.denominators.clear()
        b.clear_modes()
        collected = gc.collect()
        assert not self.exact_cache.cache and self.exact_cache.bytes == 0
        assert not self.cache and self.cache_bytes == 0
        assert not self.integer_engine.cache and self.integer_engine.bytes == 0
        event = {'rank': self.r, 'rhs_count': len(rhs[0]),
                 'cleared_estimated_bytes': sizes, 'cleared_entries': counts,
                 'gc_collected': collected,
                 'peak_rss_KiB_before_native': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        self.meta['pre_native_trim_v2']['events'].append(event)
        assert len(self.meta['pre_native_trim_v2']['events']) <= 1000
        self.save('reconstructible caches released before unchanged native solve')
        self.boundary()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--import-directory', default='hi_cft_20260923_c8two_targeted_h4_bulk')
    parser.add_argument('--output-directory', default='hi_cft_20260923_c8two_targeted_h4_trimmed_v2')
    parser.add_argument('--request', default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--seconds', type=int, default=600)
    args, remaining = parser.parse_known_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    STATE['lineage'], STATE['legacy'] = prepare(args.import_directory, args.output_directory, args.request)
    old.Consumer = Consumer
    sys.argv = [old.__file__, '--request', args.request, '--output-directory', args.output_directory,
                '--seconds', str(args.seconds), '--batch', str(STATE['legacy']['batch']), *remaining]
    old.main()


if __name__ == '__main__':
    main()
