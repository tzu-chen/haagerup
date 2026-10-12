"""Exact direct N5 projector with certified identity factors skipped."""
import json
from pathlib import Path

import hi_cft_20260923_c8two_n5_primitive_exact as old

b = old.b
raw = old.old.old.raw


class Consumer(old.Consumer):
    def __init__(self,args):
        output = Path(args.output)
        assert all(path.resolve() != Path(__file__).resolve() for path in
            (output,output.with_suffix('.sqlite'),output.with_suffix('.json.tmp'),
             output.with_suffix('.grade4.json'),output.with_suffix('.grade4.sqlite'),
             output.with_suffix('.grade4.json.tmp')))
        super().__init__(args)
        policy = {'format':'exact-N5-zero-raising-axis-stop-v1',
            'source_sha256':{str(Path(__file__).resolve()):b.sha(__file__)},
            'rule':'If E_axis(v)=0, remaining factors on that axis are identity; other axis retained'}
        previous = self.meta.get('axis_stop_exact_extension')
        if previous is None:
            assert not self.meta['verified_targets'] and not self.meta['failed_targets']
            self.meta['axis_stop_exact_extension'] = policy
        else:
            assert previous == policy
        self.save('Exact zero-raising axis-stop source bound')

    def vector(self,name):
        if name in self.cache:
            self.cache.move_to_end(name)
            return self.cache[name][0]
        previous = self.db.execute('SELECT record,digest,terms,bits FROM vectors WHERE name=?',(name,)).fetchone()
        if previous:
            blob,digest,terms,bits = previous
            record = raw.unpack(blob,digest)
            assert len(record) == terms <= raw.MAX_TERMS and bits <= b.VECTOR_BITS
            vector = {(tuple(a),tuple(o)):b.fast.FastField(c) for a,o,c in record}
            assert len(vector) == terms
            self.cache_put(name,vector,bits)
            return vector
        kind,idx = name.split(':')
        idx = int(idx)
        assert kind in ('grade5','target')
        table = 'rows' if kind == 'grade5' else 'targets'
        word_json,blob,digest = self.source.execute(f'SELECT word,raw,digest FROM {table} WHERE id=?',(idx,)).fetchone()
        word = json.loads(word_json)
        self.validate_word(word)
        vector = self.ordinary(word['normal_recipe'],kind)
        assert all(b.x.grade(s) == 5 and b.x.weight(s) == self.weight for s in vector)
        assert old.old.old.residue_digest(vector) == word['unprojected_sha256'],('Ordinary recipe digest mismatch',name)
        stopped = set()
        for factor in self.factors:
            if not vector:
                break
            if factor['axis'] in stopped:
                continue
            raised = self.bounded(b.x.mode(self.currents[factor['current_E']],0,vector))
            if not raised:
                stopped.add(factor['axis'])
                continue
            feedback = self.bounded(b.x.mode(self.currents[factor['current_F']],0,raised))
            coefficient = b.fast.FastField(-1)/factor['eigenvalue']
            out = dict(vector)
            for state,value in feedback.items():
                b.x.add(out,state,coefficient*value)
            del raised,feedback
            vector = self.bounded(out)
        assert all(b.x.grade(s) == 5 and b.x.weight(s) == self.weight for s in vector)
        expected = {self.states[i]:c for i,c in raw.unpack(blob,digest)}
        actual = {s:residue for s,c in vector.items() if (residue:=b.specialization(c))}
        assert actual == expected,('Projected recipe specialization mismatch',name)
        if kind == 'target':
            assert not self.bounded(b.x.mode(self.currents[1],0,vector))
            assert not self.bounded(b.x.mode(self.currents[4],0,vector))
            self.meta['exact_highest_target_checks'][str(idx)] = True
        return self.store(name,vector)


if __name__ == '__main__':
    old.Consumer = Consumer
    old.main()
