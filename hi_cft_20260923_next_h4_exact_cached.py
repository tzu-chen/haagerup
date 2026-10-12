"""New-output continuation of exact H4 bulk with bounded exact action caching.

Copies a CLOSED bulk checkpoint directory, authenticates every source file,
and retains the original exact full-residual consumer. Root-only execution.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import sys

import hi_cft_20260923_next_structure_h4_bulk as bulk
import hi_cft_20260923_next_exact_mode_cache as helper

b = bulk.b
STATE = {}


def prepare(origin,destination):
    origin,destination = Path(origin).resolve(),Path(destination).resolve()
    assert origin != destination and origin.is_dir()
    assert not list(origin.glob('*-journal')),'Close the original bulk writer first'
    files = sorted(path for path in origin.iterdir() if path.suffix in ('.json','.sqlite'))
    assert files and len(files) <= 200
    total = sum(path.stat().st_size for path in files)
    assert total <= 4*1024**3 and all(path.stat().st_size <= 512*1024**2 for path in files)
    bindings = {str(path):b.sha(path) for path in files}
    policy = {'format':'exact-H4-whole-action-cache-v1',
              'source_sha256':{str(Path(p).resolve()):b.sha(p) for p in (__file__,helper.__file__)},
              'ancestor_directory':str(origin),'ancestor_files_sha256':bindings,
              'ancestor_bytes':total}
    manifest = destination/'exact_cache_lineage.json'
    if destination.exists():
        assert manifest.exists() and json.loads(manifest.read_text()) == policy
    else:
        temporary = destination.with_name(destination.name+'.importing')
        assert not temporary.exists()
        temporary.mkdir()
        for path in files:
            shutil.copyfile(path,temporary/path.name)
            assert b.sha(temporary/path.name) == bindings[str(path)]
        bulk.atomic_json(temporary/'exact_cache_lineage.json',policy)
        temporary.replace(destination)
    return policy


class Consumer(bulk.Consumer):
    def __init__(self,args,policy):
        super().__init__(args,policy)
        if 'cache' not in STATE:
            STATE['cache'] = helper.ExactModeCache(b.x,b.fast.FastField)
        self.exact_cache = STATE['cache']
        for left in [*self.ops,*self.currents,self.omega]:
            self.exact_cache.register(left)
        expected = STATE['policy']
        previous = self.meta.get('exact_whole_action_cache')
        if previous is not None:
            assert previous['policy'] == expected
        if 'controls' not in STATE:
            controls = []
            # Full-field comparisons against the unchanged oracle at several
            # mode numbers and a genuinely nonrational number-field scale.
            right = self.omega
            for op,left in enumerate(self.ops):
                n = op % 3-1
                for scale in (b.fast.ONE,b.fast.FastField((1,1,0,0))):
                    vector = {s:c*scale for s,c in right.items()}
                    oracle = self.exact_cache.original_mode(left,n,vector)
                    actual = self.exact_cache.mode(left,n,vector)
                    assert actual == oracle,('Exact whole-action oracle mismatch',op,n)
                    assert actual,('Oracle control must be nonzero',op,n)
                    controls.append({'operator':op,'mode':n,'terms':len(actual)})
            assert len(controls) == 20
            assert self.exact_cache.statistics()['basis_hits'] > 0
            STATE['controls'] = controls
        self.meta['exact_whole_action_cache'] = {'policy':expected,'oracle_controls':STATE['controls']}
        b.x.mode = self.exact_cache.mode
        self.save('exact action cache authenticated and oracle controls passed')

    def save(self,reason,status='running'):
        if hasattr(self,'exact_cache') and 'exact_whole_action_cache' in self.meta:
            self.meta['exact_whole_action_cache']['statistics'] = self.exact_cache.statistics()
        super().save(reason,status)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--import-directory',default='hi_cft_20260923_next_h4_bulk')
    parser.add_argument('--output-directory',default='hi_cft_20260923_next_h4_cached_bulk')
    parser.add_argument('--seconds',type=int,default=600)
    args,remaining = parser.parse_known_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    STATE['policy'] = prepare(args.import_directory,args.output_directory)
    # The external timeout bounds copying plus native calls. Bulk additionally
    # retains its own Python timer and all the source consumer's memory gates.
    bulk.Consumer = Consumer
    sys.argv = [__file__,'--output-directory',args.output_directory,'--seconds',str(args.seconds),*remaining]
    bulk.main()


if __name__ == '__main__':
    main()
