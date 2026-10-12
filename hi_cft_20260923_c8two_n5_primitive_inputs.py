"""Positive-subset N5 recipes with only the ten primitive left fields."""
from pathlib import Path

import hi_cft_20260923_c8two_n5_inputs as old

p = old.p


class Inputs(old.Inputs):
    def __init__(self,args):
        super().__init__(args)
        self.hashes[str(Path(__file__).resolve())] = p.sha(__file__)

    def build_words(self,weight,operators,order):
        # Reuse the frozen target and descendant selection literally. The
        # discarded full-S2 recipes are small metadata, never evaluated.
        targets,all_words,_ = super().build_words(weight,operators,'descendants_first')
        descendants = [word for word in all_words if word['kind'] == 'grade4_descendant']
        del all_words
        products = []
        for op,left_weight in enumerate(self.op_weights):
            assert 0 <= op < 10
            for name in self.frozen['order']['3']:
                right_weight = p.x.weight(next(iter(self.inputs[name])))
                if tuple(a+b for a,b in zip(left_weight,right_weight)) == weight:
                    products.append({'kind':'S2_primitive_minus1_S3','operator':op,
                        'mode':-1,'exact_right':name,'weight':list(weight)})
        if order == 'interleaved':
            tasks = []
            for start in range(0,max(len(descendants),len(products)),8):
                tasks.extend(descendants[start:start+8])
                tasks.extend(products[start:start+8])
        elif order == 'products_first':
            tasks = products+descendants
        else:
            assert order == 'descendants_first'
            tasks = descendants+products
        assert 0 < len(tasks) <= 30000
        return targets,tasks,{'descendants':len(descendants),'products':len(products),
            'order':order,'left_family':'ten_original_primitive_fields',
            'scope':'Positive candidate subset; no complete-normal-span assertion'}

    def evaluate(self,word,mode):
        if word['kind'] == 'S2_primitive_minus1_S3':
            assert word['mode'] == -1 and 0 <= word['operator'] < 10
            assert word['exact_right'] in self.frozen['order']['3']
            return mode(self.ops[word['operator']][0],-1,self.inputs[word['exact_right']])
        return super().evaluate(word,mode)
