"""Exact H4 identities selected by a separately authenticated saturation plan.

Fresh outputs only: no closed bulk certificate is changed or relabelled.
The frozen integer residual engine checks every lattice coordinate.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_next_h4_integer_cached_v2 as v

b, bulk = v.b, v.bulk
MIB = 1024**2


class Consumer(v.Consumer):
    def __init__(self, args, serial_policy, targeted_policy, selection):
        super().__init__(args, serial_policy)
        self.original_target_count = len(self.targets)
        self.targets = [word for word in self.targets if word in selection]
        assert self.targets and set(self.targets) == selection
        previous = self.meta.get('targeted_selection')
        record = {'policy': targeted_policy, 'requested_targets': self.targets,
                  'original_block_target_count': self.original_target_count}
        # JSON roundtrip normalizes tuple/list representation for resume.
        record = json.loads(b.compact(record))
        if previous is not None:
            assert previous == record
        self.meta['targeted_selection'] = record
        assert self.meta['verified_targets'] + self.meta['failed_targets'] <= len(self.targets)
        self.save('source-bound targeted H4 selection authenticated')

    def run(self):
        pending = []
        for op, name in self.targets:
            previous = self.db.execute('SELECT passed FROM relations WHERE name=?',
                                       ('A%d_zero_%s' % (op, name),)).fetchone()
            if previous is not None:
                assert previous[0] == 1
            else:
                pending.append((op, name))
        matrix = self.matrix() if pending else None
        if pending:
            bits = max((b.height(c) for row in matrix for c in row), default=0)
            estimate = 4 * (4*self.r)**2 * (64 + 2*((bits+11)//8))
            self.meta['targeted_native_preflight'] = {
                'rank': self.r, 'matrix_coefficient_bits': bits,
                'estimated_bytes': estimate, 'limit_bytes': 512*MIB}
            if estimate > 512*MIB:
                raise b.BudgetStop('Targeted H4 native estimate exceeds 512 MiB')
            self.save('targeted native matrix resource preflight passed')
        for start in range(0, len(pending), self.args.batch):
            words = pending[start:start+self.args.batch]
            targets = []
            for op, name in words:
                target = b.x.mode(self.ops[op], 0, self.vector('input:'+name))
                assert len(target) <= 3078
                assert all(b.x.grade(s) == 4 and b.x.weight(s) == self.weight for s in target)
                assert max((b.height(c) for c in target.values()), default=0) <= b.VECTOR_BITS
                targets.append(target)
                self.boundary()
            rhs = [[target.get(s, b.fast.ZERO) for target in targets] for s in self.pivot_states]
            coefficients = self.flint.solve(matrix, rhs)
            self.meta['selected_exact_minor_invertible'] = True
            for j, ((op, name), target) in enumerate(zip(words, targets)):
                self.verify_ready(op, name, target, [row[j] for row in coefficients])
            del targets, rhs, coefficients
        self.meta['requested_target_count'] = len(self.targets)
        self.meta['all_requested_targets_verified'] = self.meta['verified_targets'] == len(self.targets)
        self.meta['all_block_targets_count'] = self.original_target_count
        self.meta['all_block_targets_verified'] = self.meta['verified_targets'] == self.original_target_count
        assert self.meta['all_requested_targets_verified'] and not self.meta['failed_targets']
        self.save('requested exact H4 subset completed', 'requested_subset_complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request', required=True)
    parser.add_argument('--output-directory', required=True)
    parser.add_argument('--database', default='hi_cft_20260923_next_n4_strong_skip_v2.sqlite')
    parser.add_argument('--p4-controls', default='hi_cft_20260923_next_structure_p4_controls.json')
    parser.add_argument('--max-rank', type=int, default=300)
    parser.add_argument('--batch', type=int, default=8)
    parser.add_argument('--seconds', type=int, default=600)
    args = parser.parse_args()
    assert 1 <= args.batch <= 16 and 0 < args.max_rank <= 300
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    request_path = Path(args.request).resolve()
    assert request_path.stat().st_size <= 4*MIB
    request = json.loads(request_path.read_text())
    requested = request['additional_tests']
    assert isinstance(requested, list) and len(requested) <= 2898
    wanted = {(row['operator'], row['exact_input']) for row in requested}
    assert len(wanted) == len(requested)
    assert all(isinstance(op, int) and 0 <= op <= 8 and isinstance(name, str)
               for op, name in wanted)
    output = Path(args.output_directory).resolve()
    assert output != request_path.parent or not request_path.name.startswith('block_')
    output.mkdir(exist_ok=True)
    args.operators, args.max_targets = list(range(9)), 0
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    b.fast.install(b.x)
    b.x.creation = lru_cache(maxsize=128)(b.e4.creation.__wrapped__)
    b.e4.creation = b.x.creation
    b.x.vertex = lru_cache(maxsize=256)(b.e4.vertex.__wrapped__)
    b.x.basis_mode = lru_cache(maxsize=256)(b.e4.basis_mode.__wrapped__)
    started, consumer, output_authenticated = monotonic(), None, False
    summary = {'format': 'targeted-H4-summary-v1', 'status': 'initializing', 'blocks': []}
    try:
        blocks, zeros, bindings = bulk.plan(args)
        all_words = {word for row in blocks for word in row['targets']}
        assert wanted <= all_words, 'Requested input not in a nonzero reviewed H4 block'
        selected = [{**row, 'targets': [word for word in row['targets'] if word in wanted]}
                    for row in blocks if any(word in wanted for word in row['targets'])]
        assert sum(len(row['targets']) for row in selected) == len(wanted)
        serial_policy = {'format': 'serial-exact-h4-v1', 'source_sha256': bindings,
                         'operators': args.operators,
                         'plan_sha256': hashlib.sha256(b.compact([blocks, zeros]).encode()).hexdigest(),
                         'omitted_neutral_family_derived_from_total_stress': True}
        sources = {str(Path(path).resolve()): b.sha(path) for path in
                   (__file__, v.__file__, v.integer.__file__, v.old.__file__,
                    v.old.helper.__file__, bulk.__file__, request_path)}
        policy = {'format': 'targeted-H4-integer-residual-v1', 'source_sha256': sources,
                  'serial_policy': serial_policy, 'batch': args.batch,
                  'requested_targets': sorted(wanted)}
        policy = json.loads(b.compact(policy))
        manifest = output/'targeted_policy.json'
        if manifest.exists():
            assert json.loads(manifest.read_text()) == policy
        else:
            assert not list(output.glob('*.sqlite')), 'Fresh output or identical policy required'
            bulk.atomic_json(manifest, policy)
        output_authenticated = True
        v.old.STATE['policy'], v.STATE['policy'] = policy, policy
        v.STATE['batch'] = args.batch
        summary.update({'status': 'running', 'policy': policy, 'requested_count': len(wanted)})
        for row in selected:
            args.weight = ','.join(map(str, row['weight']))
            args.output = str(output/('block_'+bulk.tag(row['weight'])+'.json'))
            assert Path(args.output).resolve() not in {Path(path).resolve() for path in sources}
            consumer = Consumer(args, serial_policy, policy, set(row['targets']))
            assert consumer.r == row['rank']
            consumer.run()
            summary['blocks'].append({'weight': row['weight'], 'rank': row['rank'],
                                      'verified_targets': consumer.meta['verified_targets'],
                                      'output': args.output})
            consumer.db.close()
            consumer.pilot.close()
            consumer = None
            b.clear_modes()
            summary['seconds_this_call'] = monotonic()-started
            bulk.atomic_json(output/'summary.json', summary)
        assert sum(row['verified_targets'] for row in summary['blocks']) == len(wanted)
        summary['status'] = 'all_requested_exact_H4_targets_passed'
    except (TimeoutError, MemoryError):
        signal.alarm(0)
        if consumer is not None:
            consumer.db.rollback()
        summary['status'] = 'interrupted_exact_checkpoints_retained'
    except b.BudgetStop as error:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.rollback()
        summary.update(status='bounded_stop', reason=str(error))
    finally:
        signal.alarm(0)
        if consumer is not None:
            consumer.db.close()
            consumer.pilot.close()
        summary['seconds_this_call'] = monotonic()-started
        if output_authenticated:
            bulk.atomic_json(output/'summary.json', summary)
        print({'status': summary['status'], 'completed_blocks': len(summary['blocks']),
               'seconds': summary['seconds_this_call']}, flush=True)


if __name__ == '__main__':
    main()
