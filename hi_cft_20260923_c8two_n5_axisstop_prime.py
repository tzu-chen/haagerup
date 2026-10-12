"""Skip identity FE factors after an exact prime zero raising action."""
from pathlib import Path

import hi_cft_20260923_c8two_n5_primitive_priority as old

p = old.p


class Inputs(old.PrioritizedInputs):
    def __init__(self,args):
        super().__init__(args)
        self.hashes[str(Path(__file__).resolve())] = p.sha(__file__)


class Consumer(old.Consumer):
    def __init__(self,args):
        old.PrioritizedInputs = Inputs
        super().__init__(args)

    def project(self,vector):
        out = old.old.old.highest.bounded(dict(vector))
        stopped = set()
        for factor in self.factors:
            if not out:
                break
            if factor['axis'] in stopped:
                continue
            raised = self.action(factor['current_E'],out)
            if not raised:
                stopped.add(factor['axis'])
                continue
            lowered = self.action(factor['current_F'],raised)
            coefficient = factor['coefficient_mod_prime']
            del raised
            for state,value in lowered.items():
                new = (out.get(state,0)+coefficient*value)%p.PRIME
                if new:
                    out[state] = new
                else:
                    out.pop(state,None)
            del lowered
            old.old.old.highest.bounded(out)
        assert all(p.x.grade(s) == 5 and p.x.weight(s) == self.weight for s in out)
        assert not self.action(1,out),'LEFT highest check'
        assert not self.action(4,out),'RIGHT highest check'
        return out


if __name__ == '__main__':
    old.Consumer = Consumer
    old.main()
