"""Bounded immutable inputs and normal recipes for direct projected N5."""
from collections import OrderedDict
import json
from pathlib import Path
import sqlite3
import zlib

import hi_cft_20260923_next_n5_selected_pilot as old

p = old.p
MIB = 1024**2


class Inputs:
    def __init__(self,args):
        self.path = Path(args.source_database).resolve()
        assert self.path.stat().st_size <= 512*MIB
        assert not Path(str(self.path)+'-journal').exists()
        self.db = sqlite3.connect(self.path.as_uri()+'?mode=ro&immutable=1',uri=True)
        self.db.execute('PRAGMA cache_size=-4096')
        self.db.execute('PRAGMA mmap_size=0')
        meta = json.loads(self.db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert meta['format'] == p.FORMAT and meta['prime'] == p.PRIME
        assert meta['normal_span_complete'] and meta['normal_rank'] == 6007 and meta['extra_rank'] == 3
        assert meta['union_rank_lower_bound'] == 6010
        self.frozen,self.inputs,self.ops,hashes,self.input_terms = p.read_inputs(args)
        assert str(Path(args.checkpoint)/'manifest.json') == meta['checkpoint_manifest']
        for filename,digest in meta['source_sha256'].items():
            assert p.sha(filename) == digest
            assert filename not in hashes or hashes[filename] == digest
            hashes[filename] = digest
        summary_path = Path(args.source_summary).resolve()
        assert summary_path.stat().st_size <= 8*MIB
        summary = json.loads(summary_path.read_text())
        for key in ('source_sha256','stage','cursor','normal_rank','extra_rank','saved_terms'):
            assert summary[key] == meta[key]
        hashes[str(self.path)],hashes[str(summary_path)] = p.sha(self.path),p.sha(summary_path)
        self.states = {}
        for idx,value in self.db.execute('SELECT id,value FROM states ORDER BY id'):
            assert idx == len(self.states) and idx < 71052
            a,o = json.loads(value)
            self.states[idx] = (tuple(a),tuple(o))
        assert len(set(self.states.values())) == len(self.states)
        control_path,vector_path = Path(args.p4_summary).resolve(),Path(args.p4_vectors).resolve()
        assert control_path.stat().st_size <= 8*MIB and vector_path.stat().st_size <= 16*MIB
        control = json.loads(control_path.read_text())
        assert control['status'] == 'exact_P4_triplet_and_lower_controls_passed'
        assert Path(control['vectors_file']).resolve() == vector_path
        assert p.sha(vector_path) == control['vectors_sha256']
        decoder = zlib.decompressobj(31)
        data = decoder.decompress(vector_path.read_bytes(),32*MIB+1)
        assert len(data) <= 32*MIB and decoder.eof and not decoder.unconsumed_tail
        bundle = json.loads(data)
        del data
        assert bundle['format'] == 'exact-p4-triplet-v1'
        assert len(bundle['fields']) == 3
        assert bundle['source_sha256'] == control['source_sha256']
        for filename,digest in bundle['source_sha256'].items():
            assert p.sha(filename) == digest
            assert filename not in hashes or hashes[filename] == digest
            hashes[filename] = digest
        self.p4,self.p4_weights = {},{}
        for field in bundle['fields']:
            assert field['grade'] == 4 and len(field['vector']) <= 12000
            vector = {(tuple(a),tuple(o)):p.x.A(c) for a,o,c in field['vector']}
            vector = {s:c for s,c in vector.items() if c}
            weight = tuple(field['weight'])
            assert vector and all(p.x.grade(s) == 4 and p.x.weight(s) == weight for s in vector)
            self.p4[field['id']],self.p4_weights[field['id']] = vector,weight
        del bundle
        assert self.p4_weights == {'P4_plus':(0,2),'P4_zero':(0,0),'P4_minus':(0,-2)}
        self.rows4 = [('rows',idx,(w0,w1)) for idx,w0,w1 in
                      self.db.execute('SELECT id,w0,w1 FROM rows ORDER BY id')]
        self.rows4 += [('P4',name,self.p4_weights[name]) for name in ('P4_plus','P4_zero','P4_minus')]
        assert len(self.rows4) == 6010
        self.currents,self.omega = p.x.LEFT+p.x.RIGHT,p.x.omega()
        self.op_weights = []
        for vector,_ in self.ops:
            weights = {p.x.weight(s) for s in vector}
            assert len(weights) == 1
            self.op_weights.append(weights.pop())
        self.cache,self.cache_terms = OrderedDict(),0
        for filename in (__file__,old.__file__,old.modes.__file__,control_path,vector_path):
            hashes[str(Path(filename).resolve())] = p.sha(filename)
        self.hashes = hashes
        self.paths = {'grade4_database':str(self.path),'grade4_summary':str(summary_path),
                      'p4_summary':str(control_path),'p4_vectors':str(vector_path),
                      'checkpoint':str(Path(args.checkpoint).resolve())}

    def source4(self,table,idx):
        if table == 'P4':
            return self.p4[idx]
        assert table == 'rows' and isinstance(idx,int)
        if idx in self.cache:
            self.cache.move_to_end(idx)
            return self.cache[idx]
        blob,digest = self.db.execute('SELECT raw,digest FROM rows WHERE id=?',(idx,)).fetchone()
        record = old.decode(blob,digest)
        assert len(record) <= 20000
        vector = {self.states[i]:p.x.A(c) for i,c in record}
        assert len(vector) == len(record)
        while self.cache and self.cache_terms+len(vector) > 200000:
            _,previous = self.cache.popitem(last=False)
            self.cache_terms -= len(previous)
        self.cache[idx] = vector
        self.cache_terms += len(vector)
        return vector

    def build_words(self,weight,operators,order):
        targets = []
        for op in operators:
            left_weight = self.op_weights[op]
            for depth,name in enumerate(('P4_plus','P4_zero','P4_minus')):
                # Only actual highest Clebsch--Gordan channels are requested.
                if depth <= min(left_weight[1],2):
                    total = tuple(a+b for a,b in zip(left_weight,self.p4_weights[name]))
                    if total == weight:
                        targets.append({'kind':'S2_zero_P4_canonical','operator':op,'mode':0,
                            'source4_table':'P4','source4_id':name,'weight':list(weight)})
        assert 0 < len(targets) <= 3,'Select a valid highest channel with at most3 targets'
        descendants,products = [],[]
        for op,left in enumerate([*self.currents,self.omega]):
            lw = p.x.weight(next(iter(left)))
            for table,idx,rw in self.rows4:
                if tuple(a+b for a,b in zip(lw,rw)) == weight:
                    descendants.append({'kind':'grade4_descendant','operator':op,
                        'mode':-1 if op < 6 else 0,'source4_table':table,'source4_id':idx,'weight':list(weight)})
        for name2 in self.frozen['order']['2']:
            lw = p.x.weight(next(iter(self.inputs[name2])))
            for name3 in self.frozen['order']['3']:
                rw = p.x.weight(next(iter(self.inputs[name3])))
                if tuple(a+b for a,b in zip(lw,rw)) == weight:
                    products.append({'kind':'S2_minus1_S3','mode':-1,
                        'exact_left':name2,'exact_right':name3,'weight':list(weight)})
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
        return targets,tasks,{'descendants':len(descendants),'products':len(products),'order':order}

    def evaluate(self,word,mode):
        kind = word['kind']
        if kind == 'S2_minus1_S3':
            assert word['mode'] == -1
            assert word['exact_left'] in self.frozen['order']['2'] and word['exact_right'] in self.frozen['order']['3']
            return mode(self.inputs[word['exact_left']],-1,self.inputs[word['exact_right']])
        if kind == 'S2_zero_P4_canonical':
            assert word['mode'] == 0 and word['source4_table'] == 'P4'
            return mode(self.ops[word['operator']][0],0,self.source4('P4',word['source4_id']))
        assert kind == 'grade4_descendant' and 0 <= word['operator'] < 7
        op = word['operator']
        assert word['mode'] == (-1 if op < 6 else 0)
        return mode(self.currents[op] if op < 6 else self.omega,word['mode'],
                    self.source4(word['source4_table'],word['source4_id']))
