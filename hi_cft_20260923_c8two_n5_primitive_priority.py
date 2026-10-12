"""Prioritize primitive products and E/E/translation descendants; root-only.

All candidates from the frozen primitive family remain. Only their order
changes; the frozen primitive exact recipe adapter remains applicable.
"""
import argparse
from pathlib import Path
import resource
import signal

import hi_cft_20260923_c8two_n5_primitive_prime as old

p,helper = old.p,old.helper


class PrioritizedInputs(old.BoundInputs):
    def __init__(self,args):
        super().__init__(args)
        self.hashes[str(Path(__file__).resolve())] = p.sha(__file__)

    def build_words(self,weight,operators,order):
        assert order == 'products_first'
        targets,tasks,counts = super().build_words(weight,operators,order)
        products = [word for word in tasks if word['kind'] == 'S2_primitive_minus1_S3']
        descendants = [word for word in tasks if word['kind'] == 'grade4_descendant']
        assert len(products)+len(descendants) == len(tasks)
        priority = {op:index for index,op in enumerate((1,4,6,0,3,2,5))}
        # Python's stable sort preserves the original source ordering within
        # each operator/P4 bucket. No candidate is deleted or duplicated.
        descendants.sort(key=lambda word:(priority[word['operator']],
                                          0 if word['source4_table'] == 'P4' else 1))
        ordered = products+descendants
        assert len(ordered) == len(tasks)
        counts = dict(counts)
        counts['order'] = 'products_then_Eleft_Eright_translation_Hleft_Hright_Fleft_Fright'
        counts['descendant_source_order'] = 'canonical_P4_first_then_original_order'
        return targets,ordered,counts


class Consumer(old.Consumer):
    def __init__(self,args):
        old.BoundInputs = PrioritizedInputs
        super().__init__(args)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-database',default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--source-summary',default='hi_cft_20260923_next_n4_strong_skip_v2.json')
    parser.add_argument('--p4-summary',default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--p4-vectors',default='hi_cft_20260923_next_structure_p4_controls.vectors.json.gz')
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--operators',default='0,1,2,3,4,5,6,7,8')
    parser.add_argument('--weight',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=int,default=300)
    args = parser.parse_args()
    args.order = 'products_first'
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    consumer = None
    try:
        assert p.g3.install_prime(p.PRIME) == [231543,1000]
        old.old.old.install_modes()
        consumer = Consumer(args)
        consumer.run()
    except (p.Stop,helper.CacheLimit,TimeoutError,MemoryError) as error:
        signal.alarm(0)
        if consumer is None:
            raise
        consumer.db.rollback()
        print({'status':'bounded_interruption','reason':str(error),
               'action':'Prior atomic prioritized primitive checkpoint retained'},flush=True)
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close();consumer.data.db.close()


if __name__ == '__main__':
    main()
