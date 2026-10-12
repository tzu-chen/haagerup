"""Per-target prime-support minors for the final exact H4 block; root-only.

Support is only proposed by the prime. Every native result is padded back
to the original normal-word basis and checked by the frozen full residual.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys

import hi_cft_20260923_c8two_h4_normalized as old
import hi_cft_20260923_c8two_n5_prime_support as support

b,bulk = old.b,old.bulk
MIB = 1024**2
STATE = {}


def prepare(origin,destination,request):
    origin,destination,request = map(lambda p:Path(p).resolve(),(origin,destination,request))
    assert origin.is_dir() and origin != destination
    assert origin not in destination.parents and destination not in origin.parents
    assert not any(origin.glob('*-journal')) and not any(origin.glob('*-wal'))
    files = sorted(p for p in origin.iterdir() if p.suffix in ('.json','.sqlite'))
    assert 0 < len(files) <= 200
    assert all(p.is_file() and not p.is_symlink() and p.stat().st_size <= 512*MIB for p in files)
    assert sum(p.stat().st_size for p in files) <= 4*1024**3
    legacy = json.loads((origin/'targeted_policy.json').read_text())
    trim = json.loads((origin/'pre_native_trim_lineage.json').read_text())
    normalization = json.loads((origin/'column_normalization_lineage.json').read_text())
    summary = json.loads((origin/'summary.json').read_text())
    assert summary['policy'] == legacy and summary['status'] in (
        'bounded_stop','interrupted_exact_checkpoints_retained','all_requested_exact_H4_targets_passed')
    assert trim['legacy_targeted_policy'] == legacy
    assert normalization['legacy_trim_policy'] == trim and normalization['legacy_targeted_policy'] == legacy
    old.old.auth.nested_graphs(normalization,{})
    assert legacy['source_sha256'][str(request)] == b.sha(request)
    lineage = {'format':'targeted-H4-per-target-prime-support-v1',
        'source_sha256':{str(Path(path).resolve()):b.sha(path)
                         for path in (__file__,old.__file__,support.__file__,request)},
        'ancestor_directory':str(origin),'ancestor_files_sha256':{str(p):b.sha(p) for p in files},
        'legacy_normalization_policy':normalization,
        'scope':'Prime support proposes an exact subset; only the full original-word residual certifies it',
        'native_preflight_limit_bytes':512*MIB,'rank_limit':300}
    manifest = destination/'per_target_support_lineage.json'
    if destination.exists():
        assert manifest.exists() and json.loads(manifest.read_text()) == lineage
    else:
        temporary = destination.with_name(destination.name+'.importing')
        assert not temporary.exists()
        temporary.mkdir()
        for source in files:
            digest = hashlib.sha256()
            with source.open('rb') as src,(temporary/source.name).open('xb') as dst:
                while chunk := src.read(MIB):
                    digest.update(chunk);dst.write(chunk)
            assert digest.hexdigest() == lineage['ancestor_files_sha256'][str(source)]
            assert b.sha(temporary/source.name) == digest.hexdigest()
        bulk.atomic_json(temporary/'per_target_support_lineage.json',lineage)
        temporary.replace(destination)
    return lineage,normalization,trim,legacy


class Consumer(old.Consumer):
    def __init__(self,args,serial_policy,targeted_policy,selection):
        super().__init__(args,serial_policy,targeted_policy,selection)
        previous = self.meta.get('per_target_prime_support')
        if previous is None:
            self.meta['per_target_prime_support'] = {'policy':STATE['lineage'],'attempts':[]}
        else:
            assert previous['policy'] == STATE['lineage']
        self.save('Per-target exact support lineage authenticated')

    def run(self):
        pending = []
        for op,name in self.targets:
            previous = self.db.execute('SELECT passed FROM relations WHERE name=?',
                                       ('A%d_zero_%s'%(op,name),)).fetchone()
            if previous is None:
                pending.append((op,name))
            else:
                assert previous[0] == 1
        # Bypass the failed normalization pass. All minor and residual
        # coefficients below refer to the original authenticated raw columns.
        matrix = b.Consumer.matrix(self) if pending else None
        self.normalization_scales = [b.fast.ONE]*self.r
        if pending:
            self.meta['per_target_prime_support']['controls'] = support.controls()
            prime = [[b.specialization(value) for value in row] for row in matrix]
        for start in range(0,len(pending),3):
            words = pending[start:start+3]
            targets = []
            for op,name in words:
                target = b.x.mode(self.ops[op],0,self.vector('input:'+name))
                assert len(target) <= 3078
                assert all(b.x.grade(s) == 4 and b.x.weight(s) == self.weight for s in target)
                assert max((b.height(c) for c in target.values()),default=0) <= b.VECTOR_BITS
                targets.append(target)
                self.boundary()
            rhs_prime = [[b.specialization(target.get(state,b.fast.ZERO)) for target in targets]
                         for state in self.pivot_states]
            prime_coefficients = support.solve(prime,rhs_prime)
            for target_index,((op,name),target) in enumerate(zip(words,targets)):
                columns = [j for j,row in enumerate(prime_coefficients) if row[target_index]]
                selected_rows = support.independent_rows(prime,columns)
                k = len(columns)
                assert k <= self.r <= 300 and len(selected_rows) == k
                minor = [[matrix[i][j] for j in columns] for i in selected_rows]
                rhs = [[target.get(self.pivot_states[i],b.fast.ZERO)] for i in selected_rows]
                if k:
                    checked = support.solve([[prime[i][j] for j in columns] for i in selected_rows],
                        [[rhs_prime[i][target_index]] for i in selected_rows])
                    assert checked == [[prime_coefficients[j][target_index]] for j in columns]
                bits = max((b.height(value) for row in minor for value in row),default=0)
                estimate = 4*(4*k)**2*(64+2*((bits+11)//8))
                attempt = {'operator':op,'input':name,'original_rank':self.r,'selected_rank':k,
                    'selected_columns':[self.columns[j] for j in columns],
                    'selected_pivot_positions':selected_rows,
                    'prime_coefficients':[[self.columns[j],prime_coefficients[j][target_index]] for j in columns],
                    'matrix_coefficient_bits':bits,'native_estimated_bytes':estimate,
                    'native_limit_bytes':512*MIB,
                    'scope':'Prime pivot-coordinate solution only; full exact residual required'}
                self.meta['per_target_prime_support']['attempts'].append(attempt)
                self.save('Individual target support and unchanged native gate measured')
                if estimate > 512*MIB:
                    raise b.BudgetStop('Individual H4 support still exceeds512MiB native preflight')
                coefficients = [b.fast.ZERO]*self.r
                if k:
                    # The frozen trim proxy validates dimensions using owner.r;
                    # restore the full basis before any verification/checkpoint.
                    original_rank = self.r
                    try:
                        self.r = k
                        solved = self.flint.solve(minor,rhs)
                    finally:
                        self.r = original_rank
                    for j,row in zip(columns,solved):
                        coefficients[j] = row[0]
                    del solved
                del minor,rhs
                self.verify_ready(op,name,target,coefficients)
            del targets,prime_coefficients,rhs_prime
        self.meta['requested_target_count'] = len(self.targets)
        self.meta['all_requested_targets_verified'] = self.meta['verified_targets'] == len(self.targets)
        self.meta['all_block_targets_count'] = self.original_target_count
        self.meta['all_block_targets_verified'] = self.meta['verified_targets'] == self.original_target_count
        assert self.meta['all_requested_targets_verified'] and not self.meta['failed_targets']
        self.save('All requested support-pruned H4 identities passed','requested_subset_complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--import-directory',default='hi_cft_20260923_c8two_targeted_h4_normalized')
    parser.add_argument('--output-directory',default='hi_cft_20260923_c8two_targeted_h4_support')
    parser.add_argument('--request',default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--seconds',type=int,default=600)
    args,remaining = parser.parse_known_args()
    assert 0 < args.seconds <= 900 and 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    STATE['lineage'],old.STATE['lineage'],old.old.STATE['lineage'],old.old.STATE['legacy'] = prepare(
        args.import_directory,args.output_directory,args.request)
    old.old.old.Consumer = Consumer
    sys.argv = [old.old.old.__file__,'--request',args.request,'--output-directory',args.output_directory,
                '--seconds',str(args.seconds),'--batch',str(old.old.STATE['legacy']['batch']),*remaining]
    old.old.old.main()


if __name__ == '__main__':
    main()
