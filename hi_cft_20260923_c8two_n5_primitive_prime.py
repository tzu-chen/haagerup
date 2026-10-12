"""Direct N5 projector using primitive-left candidate products; root-only."""
import argparse
from pathlib import Path
import resource
import signal
from types import SimpleNamespace

import hi_cft_20260923_c8two_n5_direct_prime as old
import hi_cft_20260923_c8two_n5_primitive_inputs as inputs

p,helper = old.p,old.helper


class BoundInputs(inputs.Inputs):
    def __init__(self,args):
        super().__init__(args)
        self.hashes[str(Path(__file__).resolve())] = p.sha(__file__)


class Consumer(old.Consumer):
    def __init__(self,args):
        # Process-local dependency injection; frozen source files are untouched.
        old.inputs = SimpleNamespace(Inputs=BoundInputs,__file__=inputs.__file__)
        super().__init__(args)
        policy = {'format':'direct-N5-primitive-left-candidates-v1',
            'source_sha256':{str(Path(filename).resolve()):p.sha(filename)
                             for filename in (__file__,inputs.__file__)},
            'scope':'A projected positive normal-word subset, not an exhaustion claim'}
        previous = self.meta.get('primitive_left_variant')
        if previous is not None:
            assert previous == policy
        else:
            self.meta['primitive_left_variant'] = policy
        self.save('Primitive-left normal candidate policy bound')

    def oracle_controls(self):
        super().oracle_controls()
        word = next((word for word in self.tasks if word['kind'] == 'S2_primitive_minus1_S3'),None)
        records = []
        if word is not None:
            for scale in (1,7):
                def original(left,n,right):
                    return self.mode_cache.original_mode(left,n,{s:c*scale for s,c in right.items()})
                def cached(left,n,right):
                    return self.mode_cache.mode(left,n,{s:c*scale for s,c in right.items()})
                expected = old.highest.bounded(self.data.evaluate(word,original))
                actual = old.highest.bounded(self.data.evaluate(word,cached))
                assert actual == expected
                records.append({'recipe':word,'scale':scale,'terms':len(actual),
                                'digest':old.vector_digest(actual)})
        self.meta['controls']['primitive_product_original_mode_comparisons'] = records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--p4-summary',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--p4-vectors',default='hi_cft_20260923_next_structure_p4_controls.vectors.json.gz')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--operators',default='0,1,2,3,4,5,6,7,8')
    parser.add_argument('--weight',required=True)
    parser.add_argument('--order',choices=('interleaved','products_first','descendants_first'),default='interleaved')
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=int,default=300)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    consumer = None
    try:
        assert p.g3.install_prime(p.PRIME) == [231543,1000]
        old.old.install_modes()
        consumer = Consumer(args)
        consumer.run()
    except (p.Stop,helper.CacheLimit,TimeoutError,MemoryError) as error:
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.db.rollback()
        print({'status':'bounded_interruption','reason':str(error),
               'action':'Prior atomic primitive recipe checkpoint retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close();consumer.data.db.close()


if __name__ == '__main__':
    main()
