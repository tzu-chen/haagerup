"""Exact direct N5 recipe adapter for primitive-left products; root-only."""
import argparse
from pathlib import Path
import resource
import signal

import hi_cft_20260923_c8two_n5_direct_exact_v2 as old

b = old.b


class Consumer(old.Consumer):
    def __init__(self,args):
        output = Path(args.output)
        protected = Path(__file__).resolve()
        assert all(path.resolve() != protected for path in
            (output,output.with_suffix('.sqlite'),output.with_suffix('.json.tmp'),
             output.with_suffix('.grade4.json'),output.with_suffix('.grade4.sqlite'),
             output.with_suffix('.grade4.json.tmp')))
        super().__init__(args)
        assert self.pm['candidate_counts']['left_family'] == 'ten_original_primitive_fields'
        policy = {'format':'direct-N5-primitive-exact-recipes-v1',
            'source_sha256':{str(Path(__file__).resolve()):b.sha(__file__)},
            'new_recipe':'provider.ops[operator](-1) provider.input[exact_right]',
            'scope':'Selected candidate normal words; full exact residual required'}
        previous = self.meta.get('primitive_exact_recipe_extension')
        if previous is None:
            assert not self.meta['verified_targets'] and not self.meta['failed_targets']
            self.meta['primitive_exact_recipe_extension'] = policy
        else:
            assert previous == policy
        self.save('Primitive exact normal recipe extension authenticated')

    def ordinary(self,word,kind):
        if word['kind'] == 'S2_primitive_minus1_S3':
            assert kind == 'grade5' and word['mode'] == -1 and 0 <= word['operator'] < 10
            assert word['exact_right'] in self.provider.frozen['order']['3']
            right = self.provider.vector('input:'+word['exact_right'])
            return self.bounded(b.x.mode(self.ops[word['operator']],-1,right))
        return super().ordinary(word,kind)


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
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('Primitive N5 exact Python alarm')))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    old.old.raw.installed_modes()
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
        print({'status':'interrupted','action':'Prior primitive N5 exact checkpoints retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.close(rollback)


if __name__ == '__main__':
    main()
