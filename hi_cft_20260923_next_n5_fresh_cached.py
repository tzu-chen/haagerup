"""Fresh selected-operator N5 prime pilot with the audited composite cache.

All inherited basis/term/task/RSS limits are unchanged. Sources are added
to the ordinary source_sha256 graph so exact consumers authenticate them.
"""
import argparse
import hashlib
from pathlib import Path
import resource
import signal

import hi_cft_20260923_next_n5_selected_pilot as old
import hi_cft_20260923_next_prime_mode_cache as helper


def controls(pilot,cache):
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
    # Include an actual selected left family, even when it differs fromop7.
    op = pilot.selected_ops[0]
    for field in ('P4_plus','P4_zero'):
        cases.append(('S2_zero_P4',pilot.ops[op][0],0,pilot.p4_fields[field],
                      {'operator':op,'P4':field}))
    records,nonzero = [],0
    for kind,left,n,right,recipe in cases:
        for scale in (1,7):
            vector = right if scale == 1 else {s:int(c)*scale % old.p.PRIME for s,c in right.items()}
            expected = {s:int(c) for s,c in cache.original_mode(left,n,vector).items() if c}
            actual = cache.mode(left,n,vector)
            assert actual == expected,('fresh N5 composite cache oracle mismatch',kind,recipe,scale)
            nonzero += bool(actual)
            record = [[list(s[0]),list(s[1]),c] for s,c in sorted(actual.items())]
            records.append({'kind':kind,'recipe':recipe,'mode':n,'scale':scale,
                            'terms':len(actual),'sha256':hashlib.sha256(old.compact(record).encode()).hexdigest()})
    assert len(records) == 10 and nonzero >= 2
    assert cache.statistics()['basis_cache_hits'] > 0
    return {'whole_vector_comparisons':10,'nonzero_comparisons':nonzero,
            'all_equal_to_original_mode':True,'records':records}


class CachedPilot(old.Pilot):
    def save(self,reason,status='running'):
        if hasattr(self,'mode_cache'):
            self.meta['fresh_mode_cache']['statistics'] = self.mode_cache.statistics()
        super().save(reason,status)

    def run(self):
        self.build_targets()
        if self.check_targets():
            self.meta['explicit_column_family_exhausted'] = False
            self.save('All selected targets already contained','targets_contained')
            return
        currents,omega = old.p.x.LEFT+old.p.x.RIGHT,old.p.x.omega()
        checked_rank,checked_cursor = len(self.info),self.meta['cursor']
        while self.meta['cursor'] < len(self.tasks):
            word = self.tasks[self.meta['cursor']]
            if word['kind'] == 'grade4_descendant':
                right = self.source_vector(word['source4_table'],word['source4_id'])
                op = word['operator']
                left = currents[op] if op < 6 else omega
            else:
                left,right = self.inputs[word['exact_left']],self.inputs[word['exact_right']]
            self.accept(old.p.x.mode(left,word['mode'],right),word)
            self.meta['cursor'] += 1
            self.boundary()
            # Check on task progress too: a stalled rank must not leave a
            # successful target containment stale for hundreds of mode calls.
            if (self.meta['cursor'] == self.descendant_tasks or
                    len(self.info)-checked_rank >= 100 or
                    self.meta['cursor']-checked_cursor >= 100):
                checked_rank,checked_cursor = len(self.info),self.meta['cursor']
                if self.check_targets():
                    self.meta['explicit_column_family_exhausted'] = False
                    self.save('Selected targets contained in actual normal words','targets_contained')
                    return
        self.meta['explicit_column_family_exhausted'] = True
        passed = self.check_targets()
        self.save('Explicit selected column family exhausted',
                  'targets_contained' if passed else 'explicit_columns_exhausted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--p4-summary',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--p4-vectors',default='hi_cft_20260923_next_structure_p4_controls.vectors.json.gz')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--operators',default='6')
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    selected = sorted(set(map(int,args.operators.split(','))))
    assert selected and set(selected) <= set(range(9))
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    # Only the process-local reader is adapted. The frozen module and existing
    # output files remain unchanged; resume recreates the same binding graph.
    original_reader = old.p.read_inputs
    extra_sources = {str(Path(path).resolve()):old.p.sha(path)
                     for path in (__file__,helper.__file__,old.__file__)}
    def read_with_sources(options):
        frozen,inputs,ops,hashes,terms = original_reader(options)
        hashes = dict(hashes)
        for path,digest in extra_sources.items():
            assert path not in hashes or hashes[path] == digest
            hashes[path] = digest
        return frozen,inputs,ops,hashes,terms
    old.p.read_inputs = read_with_sources
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('fresh cached N5 alarm')))
    signal.alarm(args.seconds)
    pilot = None
    try:
        assert old.p.g3.install_prime(old.p.PRIME) == [231543,1000]
        old.install_modes()
        pilot = CachedPilot(args)
        policy = {'format':'fresh-selected-N5-composite-cache-v1','source_sha256':extra_sources}
        if 'fresh_mode_cache' in pilot.meta:
            assert pilot.meta['fresh_mode_cache']['policy'] == policy
        else:
            assert pilot.meta['cursor'] == 0 and pilot.meta['normal_rank'] == 0
            pilot.meta['fresh_mode_cache'] = {'policy':policy,'controls':None}
        cache = helper.PrimeModeCache(old.p.x,old.p.PRIME,max_terms=300000,max_entries=50000)
        pilot.mode_cache = cache
        for name in pilot.frozen['order']['2']:
            cache.register(pilot.inputs[name])
        for left in old.p.x.LEFT+old.p.x.RIGHT:
            cache.register(left)
        for left,_ in pilot.ops:
            cache.register(left)
        assert cache.statistics()['registered_left_fields'] <= 136
        pilot.meta['fresh_mode_cache']['controls'] = controls(pilot,cache)
        pilot.save('Ten fresh selected-N5 whole-mode oracle checks passed')
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
            print({'status':'interrupted','action':'Prior fresh cached-N5 atomic checkpoint retained'},flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if pilot is not None:
            pilot.db.close()
            pilot.source.close()


if __name__ == '__main__':
    main()
