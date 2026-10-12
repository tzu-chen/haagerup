"""Exact direct N5 relations using a prime-suggested subset of normal words.

The subset is only a candidate. Full characteristic-zero sparse residuals
from the frozen v1 consumer decide whether it actually contains each target.
All frozen providers, native solves, modes and arithmetic stay unchanged.
"""
import argparse
from pathlib import Path
import resource
import signal

import hi_cft_20260923_c8two_n5_direct_exact as old
import hi_cft_20260923_c8two_n5_prime_support as support

b = old.b


class Consumer(old.Consumer):
    def __init__(self,args):
        selected = support.extract(args.database,args.source_summary)
        protected = {Path(filename).resolve() for filename in selected['source_sha256']}
        protected.add(Path(__file__).resolve())
        output = Path(args.output)
        for path in (output,output.with_suffix('.sqlite'),output.with_suffix('.json.tmp'),
                     output.with_suffix('.grade4.json'),output.with_suffix('.grade4.sqlite'),
                     output.with_suffix('.grade4.json.tmp')):
            assert path.resolve() not in protected
        super().__init__(args)
        assert tuple(selected['weight']) == self.weight
        assert selected['source_normal_rank'] == len(self.blocks[self.weight])
        assert selected['target_count'] == len(self.targets)
        # Exclude performance-only fields so interrupted/repeated extraction
        # yields the identical source-bound mathematical policy on resume.
        policy = {key:value for key,value in selected.items() if key not in ('seconds','peak_rss_KiB')}
        policy['adapter_source_sha256'] = {str(Path(__file__).resolve()):b.sha(__file__)}
        policy['exact_selection_rule'] = 'Union of nonzero prime relation supports; exact full residual still required'
        previous = self.meta.get('prime_support_selection_v2')
        if previous is None:
            assert not self.meta['verified_targets'] and not self.meta['failed_targets']
            self.meta['prime_support_selection_v2'] = policy
        else:
            assert previous == policy
        self.blocks = {self.weight:[(column,self.states[pivot]) for column,pivot in
            zip(selected['selected_columns'],selected['selected_pivot_state_ids'])]}
        assert len(self.blocks[self.weight]) == selected['selected_rank'] <= args.max_rank
        self.meta['prime_support_selection_timing'] = {
            'seconds':selected['seconds'],'peak_rss_KiB':selected['peak_rss_KiB']}
        self.save('Prime-suggested exact column subset authenticated')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',required=True)
    parser.add_argument('--source-summary',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--max-rank',type=int,default=300)
    parser.add_argument('--seconds',type=int,default=600)
    args = parser.parse_args()
    args.weight = None
    assert 0 < args.max_rank <= 300 and 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('Direct N5 v2 exact Python alarm')))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    old.raw.installed_modes()
    consumer,rollback = None,False
    try:
        consumer = Consumer(args)
        consumer.run()
    except b.BudgetStop as error:
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.save(str(error),'bounded_stop')
    except (TimeoutError,MemoryError):
        signal.alarm(0)
        rollback = True
        if consumer is None:
            raise
        print({'status':'interrupted','action':'Prior direct N5 v2 exact checkpoints retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.close(rollback)


if __name__ == '__main__':
    main()
