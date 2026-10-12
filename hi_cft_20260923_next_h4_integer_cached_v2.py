"""Root-only new-output H4 continuation with exact integer residuals.

The prior whole-action cache policy remains authenticated as legacy lineage;
this adapter and integer helper receive a separate closed-ancestor binding.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import shutil
import signal
import sys
import weakref

import hi_cft_20260923_next_h4_exact_cached as old
import hi_cft_20260923_next_integer_residual as integer

b,bulk = old.b,old.bulk
STATE = {}


def prepare(origin,destination,batch):
    origin,destination = Path(origin).resolve(),Path(destination).resolve()
    assert origin != destination and origin.is_dir()
    assert not list(origin.glob('*-journal')),'Close the previous cached bulk writer first'
    files = sorted(p for p in origin.iterdir() if p.suffix in ('.json','.sqlite'))
    assert files and len(files) <= 200
    assert sum(p.stat().st_size for p in files) <= 4*1024**3
    assert all(p.stat().st_size <= 512*1024**2 for p in files)
    legacy_path = origin/'exact_cache_lineage.json'
    legacy = json.loads(legacy_path.read_text())
    assert legacy['format'] == 'exact-H4-whole-action-cache-v1'
    for graph in (legacy['source_sha256'],legacy['ancestor_files_sha256']):
        for filename,digest in graph.items():
            assert b.sha(filename) == digest,filename
    policy = {'format':'exact-H4-integer-residual-v2','effective_batch':batch,
        'source_sha256':{str(Path(p).resolve()):b.sha(p) for p in
                        (__file__,integer.__file__,old.__file__,old.helper.__file__)},
        'ancestor_directory':str(origin),'ancestor_files_sha256':{str(p):b.sha(p) for p in files},
        'legacy_whole_action_cache_policy':legacy}
    manifest = destination/'integer_residual_lineage.json'
    if destination.exists():
        assert manifest.exists() and json.loads(manifest.read_text()) == policy
    else:
        temporary = destination.with_name(destination.name+'.importing')
        assert not temporary.exists()
        temporary.mkdir()
        for p in files:
            shutil.copyfile(p,temporary/p.name)
            assert b.sha(temporary/p.name) == policy['ancestor_files_sha256'][str(p)]
        bulk.atomic_json(temporary/'integer_residual_lineage.json',policy)
        temporary.replace(destination)
    return policy,legacy


class Consumer(old.Consumer):
    def __init__(self,args,policy):
        super().__init__(args,policy)
        previous = self.meta.get('integer_residual_v2')
        if previous is not None:
            assert previous['policy'] == STATE['policy']
        if 'synthetic_controls' not in STATE:
            STATE['synthetic_controls'] = integer.controls(b.fast.FastField)
        reference = weakref.ref(self)
        self.integer_engine = integer.Residual(b.fast.FastField,
            lambda idx:reference().vector('normal:'+str(idx)),lambda:reference().boundary())
        self.meta['integer_residual_v2'] = {'policy':STATE['policy'],
            'synthetic_controls':STATE['synthetic_controls'],
            'actual_pair_control':STATE.get('actual_pair_control')}
        self.meta['solver']['batch'] = STATE['batch']
        self.save('integer residual lineage and synthetic controls authenticated')

    def save(self,reason,status='running'):
        if hasattr(self,'integer_engine') and 'integer_residual_v2' in self.meta:
            self.meta['integer_residual_v2']['statistics'] = self.integer_engine.statistics()
            self.meta['integer_residual_v2']['actual_pair_control'] = STATE.get('actual_pair_control')
        super().save(reason,status)

    def verify_ready(self,op,name,target,coefficients):
        assert len(coefficients) == self.r
        assert max((b.height(c) for c in coefficients),default=0) <= b.MATRIX_BITS
        try:
            residual = self.integer_engine.residual(target,self.columns,coefficients)
            if 'actual_pair_control' not in STATE:
                getter = lambda idx:self.vector('normal:'+str(idx))
                oracle = integer.oracle(b.fast.FastField,target,self.columns,coefficients,getter)
                assert residual == oracle,'Actual H4 integer/rational residual mismatch'
                state = min(target) if target else min(getter(self.columns[0]))
                perturbed = dict(target)
                b.x.add(perturbed,state,b.fast.FastField(('1/7','2/11','-3/13','5/17')))
                changed = self.integer_engine.residual(perturbed,self.columns,coefficients)
                assert changed == integer.oracle(b.fast.FastField,perturbed,self.columns,coefficients,getter)
                assert changed != residual,'Perturbation must change the full exact residual'
                STATE['actual_pair_control'] = {'operator':op,'input':name,
                    'original_equal':True,'nonzero_perturbation_detected':True,'state':state}
        except integer.Limit as error:
            raise b.BudgetStop(str(error)) from error
        target_record = [[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(target.items())]
        record = {'word':{'operator':op,'mode':0,'exact_input':name},
            'normal_word_coefficients':[[idx,[str(q) for q in c]] for idx,c in zip(self.columns,coefficients) if c],
            'negative_columns_are_exact_P4_fields':True,
            'target_sha256':hashlib.sha256(b.compact(target_record).encode()).hexdigest(),
            'target_terms':len(target),'exact_residual_zero':not residual,
            'residual':[[list(s[0]),list(s[1]),[str(q) for q in c]] for s,c in sorted(residual.items())]}
        blob,digest = b.pack(record)
        self.db.execute('INSERT INTO relations VALUES (?,?,?,?)',('A%d_zero_%s'%(op,name),blob,digest,int(not residual)))
        self.meta['verified_targets' if not residual else 'failed_targets'] += 1
        self.save('full exact integer-cleared H4 residual checked')
        if residual:
            raise b.BudgetStop('Target outside chosen exact H4 column subset; no full-span upper bound claimed')

    def run(self):
        pending = []
        for op,name in self.targets:
            previous = self.db.execute('SELECT passed FROM relations WHERE name=?',('A%d_zero_%s'%(op,name),)).fetchone()
            if previous:
                assert previous[0]
            else:
                pending.append((op,name))
        matrix = self.matrix() if pending else None
        for start in range(0,len(pending),STATE['batch']):
            words,targets = pending[start:start+STATE['batch']],[]
            for op,name in words:
                target = b.x.mode(self.ops[op],0,self.vector('input:'+name))
                if len(target) > 3078:
                    raise b.BudgetStop('Reviewed enlarged-batch target width3078 exceeded')
                assert all(b.x.grade(s) == 4 and b.x.weight(s) == self.weight for s in target)
                assert max((b.height(c) for c in target.values()),default=0) <= b.VECTOR_BITS
                targets.append(target)
                self.boundary()
            rhs = [[target.get(s,b.fast.ZERO) for target in targets] for s in self.pivot_states]
            coefficients = self.flint.solve(matrix,rhs)
            self.meta['selected_exact_minor_invertible'] = True
            for j,((op,name),target) in enumerate(zip(words,targets)):
                self.verify_ready(op,name,target,[row[j] for row in coefficients])
            del targets,rhs,coefficients
        self.meta['all_block_targets_count'] = len(self.targets)
        self.meta['all_block_targets_verified'] = self.meta['verified_targets'] == len(self.targets)
        self.save('selected H4 block targets completed','complete' if self.meta['all_block_targets_verified'] else 'partial_complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--import-directory',default='hi_cft_20260923_next_h4_cached_bulk')
    parser.add_argument('--output-directory',default='hi_cft_20260923_next_h4_integer_bulk_v2')
    parser.add_argument('--integer-batch',type=int,default=32)
    parser.add_argument('--seconds',type=int,default=600)
    args,remaining = parser.parse_known_args()
    assert 1 <= args.integer_batch <= 32 and 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    STATE['policy'],legacy = prepare(args.import_directory,args.output_directory,args.integer_batch)
    STATE['batch'] = args.integer_batch
    # Preserve the validated old cache policy, and bind the new ancestor and
    # residual algorithm separately rather than rewriting exact past records.
    old.STATE['policy'] = legacy
    bulk.Consumer = Consumer
    sys.argv = [__file__,'--output-directory',args.output_directory,'--seconds',str(args.seconds),*remaining]
    bulk.main()


if __name__ == '__main__':
    main()
