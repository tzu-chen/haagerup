"""Restartable exact finite spans through grade four, with word provenance.

Run ONLY through hi_cft_safe_run.py.  This is a finite-span calculation,
never an all-weight properness or character certificate.  Checkpoints use
Q(sqrt(13),sqrt(-3)); no floating ranks or coefficient recognition occurs.

Each accepted echelon row records the original mode word, the earlier rows
subtracted, and the exact normalization.  Per-Cartan-block files are committed
together by an atomic CURRENT pointer.  A timed pilot may be resumed without
discarding completed exact work.  The replay phase checks every saved row's
local arithmetic identity against its already checked parents.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sys
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as e4


SOURCE = Path('hi_cft_20260923_c8_exact_fields.json')
REFERENCE3 = Path('hi_cft_20260923_c8_grade3_span.json')
REFERENCE4 = Path('hi_cft_20260923_proof_grade4_tol5.json')
FORMAT = 'exact-cartan-span-v1'


def coefficient(a):
    return [str(c) for c in x.A(a)]


def coefficient_bits(a):
    return max(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) for q in a)


def packed(v):
    return [[list(s[0]), list(s[1]), coefficient(c)] for s, c in sorted(v.items())]


def unpacked(rows):
    return {(tuple(a), tuple(o)): x.A(c) for a, o, c in rows}


def subtract(out, c, row):
    """out -= c*row without recopying/multiplying the unchanged coefficients."""
    for s, a in row.items():
        b = a if c == x.ONE else c * a
        value = out[s] - b if s in out else -b
        if value:
            out[s] = value
        elif s in out:
            del out[s]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def sources():
    return {str(p): sha(p) for p in (Path(__file__), Path(x.__file__),
            Path(e4.__file__), SOURCE, REFERENCE3, REFERENCE4)}


def install():
    # Smaller caches than the exploratory engines: one cached basis action
    # can itself contain many terms.  No dense ambient grade-four basis exists.
    x.creation = lru_cache(maxsize=512)(e4.creation.__wrapped__)
    x.vertex = lru_cache(maxsize=2048)(e4.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=4096)(e4.basis_mode.__wrapped__)


def clear_mode_caches():
    x.creation.cache_clear()
    x.vertex.cache_clear()
    x.basis_mode.cache_clear()


class BudgetStop(Exception):
    pass


class Database:
    def __init__(self, args):
        self.args = args
        self.directory = Path(args.checkpoint_dir)
        self.fields = {}
        self.rows = {}
        self.blocks = {i: {} for i in range(1, 5)}
        self.order = {i: [] for i in range(1, 5)}
        self.nnz = 0
        self.dirty = set()
        self.generation = 0
        self.old = None
        self.started = monotonic()
        self.last_save = self.started
        self.steps = 0
        self.stop = False
        self.meta = {'format': FORMAT, 'sources': sources(), 'phase': 'init',
                     'stage': 0, 'cursor': 0, 'closed_lower3': 0,
                     'closed_lower4': 0, 'history': [], 'audits': {},
                     'finite_span_only': True, 'completed_grade3': False,
                     'completed_grade4': False}
        if (self.directory / 'CURRENT').exists():
            self.load()
        elif self.directory.exists() and any(self.directory.iterdir()):
            raise RuntimeError('Refusing nonempty directory without CURRENT')

    def value(self, name):
        return self.fields[name]['vector'] if name in self.fields else self.rows[name]['vector']

    def evaluate(self, recipe):
        op = recipe['op']
        if op == 'ref':
            return self.value(recipe['id']).copy()
        if op == 'mode':
            return x.mode(self.value(recipe['left']), recipe['n'], self.value(recipe['right']))
        if op == 'sum':
            return x.vadd(*[(x.A(c), self.value(name)) for c, name in recipe['terms']])
        if op == 'vacuum':
            return x.VAC.copy()
        if op == 'current':
            return (x.LEFT + x.RIGHT)[recipe['index']].copy()
        if op == 'omega':
            return x.omega()
        if op == 'source_field':
            assert recipe['source_sha256'] == self.meta['sources'][str(SOURCE)]
            return x.read_field(json.loads(SOURCE.read_text())['fields'][recipe['index']])
        if op == 'u':
            a = (0, 0, 0, 0, 0, -1, 1, 1)
            b = (0, 0, 0, 1, 1, -1, 0, 0)
            c = (1, 1, 0, 0, 0, -1, 0, 0)
            return {(a, ()): x.ONE, (b, ()): x.A((0, Q(1, 20), Q(3, 20), 0)),
                    (c, ()): x.A((0, Q(1, 20), -Q(3, 20), 0))}
        raise ValueError(recipe)

    def field(self, recipe, name=None):
        if name is None:
            name = 'f%05d' % len(self.fields)
        assert name not in self.fields and name not in self.rows
        self.fields[name] = {'id': name, 'recipe': recipe, 'vector': self.evaluate(recipe)}
        return name

    def add(self, grade, vector, recipe):
        """Exact sparse row insertion; coefficients describe the whole reduction."""
        if not vector:
            return None
        weights = {x.weight(s) for s in vector}
        assert len(weights) == 1, weights
        assert all(x.grade(s) == grade for s in vector)
        w = next(iter(weights))
        block = self.blocks[grade].setdefault(w, {})
        out = vector.copy()
        elimination = []
        elimination_height = 0
        for pivot, name in sorted(block.items()):
            if pivot in out:
                c = out[pivot]
                elimination_height = max(elimination_height, coefficient_bits(c))
                elimination.append([coefficient(c), name])
                subtract(out, c, self.rows[name]['vector'])
        if not out:
            return None
        pivot = min(out)
        scale = out[pivot].inv()
        out = {s: c * scale for s, c in out.items()}
        if self.nnz + len(out) > self.args.max_nnz:
            raise BudgetStop('total saved sparse-term cap reached')
        if len(self.order[grade]) >= (7000 if grade == 4 else 1600):
            raise BudgetStop('finite-span rank cap reached')
        height = max(elimination_height, coefficient_bits(scale),
                     max(coefficient_bits(a) for a in out.values()))
        if height > self.args.max_coefficient_bits:
            raise BudgetStop('coefficient bit-length cap reached: %s' % height)
        name = 'r%d_%06d' % (grade, len(self.order[grade]))
        self.rows[name] = {'id': name, 'grade': grade, 'weight': list(w),
                           'recipe': recipe, 'elimination': elimination,
                           'scale': coefficient(scale), 'vector': out,
                           'coefficient_bits': height}
        block[pivot] = name
        self.order[grade].append(name)
        self.nnz += len(out)
        self.meta['largest_saved_coefficient_bits'] = max(
            self.meta.get('largest_saved_coefficient_bits', 0), height)
        self.dirty.add((grade, w))
        return name

    def reduce(self, grade, vector):
        if not vector:
            return {}
        weights = {x.weight(s) for s in vector}
        assert len(weights) == 1
        out = vector.copy()
        for pivot, name in sorted(self.blocks[grade].get(next(iter(weights)), {}).items()):
            if pivot in out:
                subtract(out, out[pivot], self.rows[name]['vector'])
        return out

    def perform(self, grade, recipe):
        self.boundary()
        result = self.add(grade, self.evaluate(recipe), recipe)
        self.steps += 1
        return result

    def boundary(self):
        if self.stop or monotonic() - self.started >= self.args.seconds:
            raise BudgetStop('requested time/stop boundary')
        if self.steps >= self.args.max_steps:
            raise BudgetStop('requested operation-count boundary')
        # The launcher watches the whole group.  This earlier soft stop lets
        # the producer save a checkpoint before its hard address cap is hit.
        status = Path('/proc/self/status').read_text()
        rss = int(next(line.split()[1] for line in status.splitlines() if line.startswith('VmRSS:')))
        if rss > self.args.soft_rss_mib * 1024:
            raise BudgetStop('producer soft RSS cap reached')
        if monotonic() - self.last_save >= self.args.checkpoint_seconds:
            self.save('periodic')

    def counts(self):
        return {str(g): len(self.order[g]) for g in self.order}

    def record(self, stage):
        row = {'stage': stage, 'dimensions': self.counts(), 'sparse_terms': self.nnz,
               'invocation_seconds': monotonic() - self.started,
               'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        self.meta['history'].append(row)
        print(json.dumps(row), flush=True)

    def save(self, reason):
        self.directory.mkdir(parents=True, exist_ok=True)
        # A hard kill can leave a .partial directory.  Do not overwrite it.
        while True:
            self.generation += 1
            new = self.directory / ('checkpoint_%06d' % self.generation)
            partial = new.with_name(new.name + '.partial')
            if not new.exists() and not partial.exists():
                break
        partial.mkdir()
        filenames = []
        for grade in sorted(self.blocks):
            for w, block in sorted(self.blocks[grade].items()):
                if not block:
                    continue
                filename = 'grade%d_weight_%d_%d.json.gz' % (grade, *w)
                filenames.append(filename)
                old_file = self.old / filename if self.old else None
                if (grade, w) not in self.dirty and old_file and old_file.exists():
                    os.link(old_file, partial / filename)
                else:
                    with gzip.open(partial / filename, 'wt', encoding='utf-8', compresslevel=1) as f:
                        f.write('{"grade":%d,"weight":%s,"rows":[' % (grade, json.dumps(w)))
                        for i, name in enumerate(sorted(block.values(), key=lambda z: int(z.split('_')[1]))):
                            row = dict(self.rows[name])
                            row['vector'] = packed(row['vector'])
                            if i:
                                f.write(',')
                            json.dump(row, f, separators=(',', ':'))
                        f.write(']}\n')
        fieldfile = 'fields.json.gz'
        if self.old and (self.old / fieldfile).exists():
            os.link(self.old / fieldfile, partial / fieldfile)
        else:
            with gzip.open(partial / fieldfile, 'wt', encoding='utf-8', compresslevel=1) as f:
                json.dump([{**r, 'vector': packed(r['vector'])} for r in self.fields.values()], f,
                          separators=(',', ':'))
        manifest = {**self.meta, 'generation': self.generation, 'reason': reason,
                    'order': {str(g): ids for g, ids in self.order.items()},
                    'dimensions': self.counts(), 'sparse_terms': self.nnz,
                    'block_files': filenames, 'field_file': fieldfile,
                    'files_sha256': {n: sha(partial / n) for n in filenames + [fieldfile]},
                    'invocation_seconds': monotonic() - self.started,
                    'invocation_steps': self.steps,
                    'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        (partial / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        partial.rename(new)
        pointer = self.directory / 'CURRENT.partial'
        pointer.write_text(new.name + '\n')
        pointer.replace(self.directory / 'CURRENT')
        self.old = new
        self.dirty.clear()
        self.last_save = monotonic()
        clear_mode_caches()
        print(json.dumps({'checkpoint': str(new), 'reason': reason,
                          'dimensions': self.counts(), 'sparse_terms': self.nnz}), flush=True)

    def load(self):
        name = (self.directory / 'CURRENT').read_text().strip()
        assert '/' not in name and name.startswith('checkpoint_')
        self.old = self.directory / name
        saved = json.loads((self.old / 'manifest.json').read_text())
        assert saved['format'] == FORMAT
        assert saved['sources'] == self.meta['sources'], 'source changed; refuse incompatible checkpoint'
        for filename, digest in saved['files_sha256'].items():
            assert sha(self.old / filename) == digest, ('checkpoint hash mismatch', filename)
        with gzip.open(self.old / saved['field_file'], 'rt') as f:
            for r in json.load(f):
                r['vector'] = unpacked(r['vector'])
                self.fields[r['id']] = r
        for filename in saved['block_files']:
            with gzip.open(self.old / filename, 'rt') as f:
                block = json.load(f)
            grade, w = block['grade'], tuple(block['weight'])
            self.blocks[grade][w] = {}
            for r in block['rows']:
                r['vector'] = unpacked(r['vector'])
                self.rows[r['id']] = r
                self.blocks[grade][w][min(r['vector'])] = r['id']
                self.nnz += len(r['vector'])
        self.order = {int(g): ids for g, ids in saved['order'].items()}
        self.meta = saved
        self.generation = saved['generation']
        assert self.nnz == saved['sparse_terms']


def mode(left, n, right):
    return {'op': 'mode', 'left': left, 'n': n, 'right': right}


def initialize(db):
    """Construct S2 using the same sparse, uneliminated product inputs as before."""
    db.field({'op': 'vacuum'}, 'vacuum')
    currents = [db.field({'op': 'current', 'index': i}, 'current%d' % i) for i in range(6)]
    db.field({'op': 'omega'}, 'omega')
    db.field({'op': 'u'}, 'u')
    source = json.loads(SOURCE.read_text())
    fields = [db.field({'op': 'source_field', 'index': i,
                        'source_sha256': db.meta['sources'][str(SOURCE)]}, 'source%d' % i)
              for i in range(len(source['fields']))]
    chosen = []

    def add2(name):
        if db.add(2, db.value(name), {'op': 'ref', 'id': name}):
            chosen.append(name)

    for cur in currents:
        db.add(1, db.value(cur), {'op': 'ref', 'id': cur})
        add2(db.field(mode(cur, -2, 'vacuum')))
        for other in currents:
            add2(db.field(mode(cur, -1, other)))
    stresses = []
    for offset, level in ((0, 1), (3, 39)):
        h, e, f = currents[offset:offset + 3]
        hh = db.field(mode(h, -1, h))
        ef = db.field(mode(e, -1, f))
        fe = db.field(mode(f, -1, e))
        stresses.append(db.field({'op': 'sum', 'terms': [
            [coefficient(Q(1, 4 * (level + 2))), hh],
            [coefficient(Q(1, 2 * (level + 2))), ef],
            [coefficient(Q(1, 2 * (level + 2))), fe]]}))
    complement = db.field({'op': 'sum', 'terms': [
        [coefficient(1), 'omega'], [coefficient(-1), stresses[0]],
        [coefficient(-1), stresses[1]], [coefficient(-1), fields[-1]]]})
    add2(fields[-1])
    add2(complement)
    for row, first in zip(source['fields'][:-1], fields[:-1]):
        left = first
        n, m = row['dimensions']
        for _ in range(n):
            right = left
            for _ in range(m):
                add2(right)
                right = db.field(mode('current5', 0, right))
            assert not db.value(right)
            left = db.field(mode('current2', 0, left))
        assert not db.value(left)
    assert len(chosen) == len(db.order[2]) == 120
    db.meta['s2_inputs'] = chosen
    db.meta['charged_fields'] = sorted(fields[:-1], key=lambda k: len(db.value(k)))
    db.meta['phase'] = 'grade3'
    db.meta['stage'] = 0
    db.meta['cursor'] = 0
    db.record('initialized exact S1 and S2')
    db.save('initialization complete')


def seeds(db, grade, label, recipes):
    for i in range(db.meta['cursor'], len(recipes)):
        db.perform(grade, recipes[i])
        db.meta['cursor'] = i + 1
    db.record(label)
    db.meta['stage'] += 1
    db.meta['cursor'] = 0
    db.save('stage complete')


def closure(db, grade, full=False):
    operators = [('current2', 0), ('current5', 0)]
    if full:
        operators.append(('u', 1))
    key = 'closed_lower%d' % grade
    if not full and db.meta['cursor'] == 0:
        db.meta['cursor'] = db.meta[key] * len(operators)
    # The list grows during traversal. Every accepted row receives each mode.
    while db.meta['cursor'] < len(db.order[grade]) * len(operators):
        i, j = divmod(db.meta['cursor'], len(operators))
        left, n = operators[j]
        db.perform(grade, mode(left, n, db.order[grade][i]))
        db.meta['cursor'] += 1
    if not full:
        db.meta[key] = len(db.order[grade])
    db.record('grade%d %s closure' % (grade, 'lowering and u_1' if full else 'current lowering'))
    db.meta['stage'] += 1
    db.meta['cursor'] = 0
    db.save('stage complete')


def grade3(db):
    s2 = db.meta['s2_inputs']
    fields = db.meta['charged_fields']
    while db.meta['phase'] == 'grade3':
        stage = db.meta['stage']
        if stage == 0:
            seeds(db, 3, 'grade3 affine descendants',
                  [mode('current%d' % i, -1, v) for i in range(6) for v in s2])
        elif stage == 1:
            seeds(db, 3, 'grade3 translation descendants', [mode('omega', 0, v) for v in s2])
        elif stage == 2:
            closure(db, 3)
        elif stage < 3 + 2 * len(fields):
            j, parity = divmod(stage - 3, 2)
            if parity:
                closure(db, 3)
            else:
                seeds(db, 3, 'grade3 field %s zero products' % fields[j],
                      [mode(fields[j], 0, v) for v in s2])
        else:
            weights = {','.join(map(str, w)): len(b) for w, b in db.blocks[3].items() if b}
            reference = json.loads(REFERENCE3.read_text())['weight_multiplicities']
            assert weights == reference, 'exact grade3 weight multiplicities disagree with previous certificate'
            db.meta['grade3_weight_multiplicities'] = weights
            db.meta['completed_grade3'] = True
            db.meta['phase'] = 'grade4'
            db.meta['stage'] = db.meta['cursor'] = 0
            db.record('exact grade3 complete')
            db.save('grade3 complete')


def grade4(db):
    assert db.meta['completed_grade3']
    s2, s3 = db.meta['s2_inputs'], db.order[3]
    while db.meta['phase'] == 'grade4':
        stage = db.meta['stage']
        if stage == 0:
            seeds(db, 4, 'grade4 affine descendants',
                  [mode('current%d' % i, -1, v) for i in range(6) for v in s3])
        elif stage == 1:
            seeds(db, 4, 'grade4 translation descendants', [mode('omega', 0, v) for v in s3])
        elif stage in (2, 4, 6):
            closure(db, 4)
        elif stage == 3:
            seeds(db, 4, 'grade4 normal ordered u S2', [mode('u', -1, v) for v in s2])
        elif stage == 5:
            seeds(db, 4, 'grade4 u zero S3', [mode('u', 0, v) for v in s3])
        elif stage == 7:
            closure(db, 4, full=True)
        else:
            weights = {','.join(map(str, w)): len(b) for w, b in db.blocks[4].items() if b}
            old = json.loads(REFERENCE4.read_text())['weight_multiplicities']
            db.meta['grade4_weight_multiplicities'] = weights
            db.meta['matches_previous_numerical_blocks'] = weights == old
            db.meta['completed_grade4'] = True
            db.meta['phase'] = 'audit'
            db.meta['stage'] = db.meta['cursor'] = 0
            db.record('exact grade4 finite span complete')
            db.save('grade4 complete; low-mode audits still pending')


def audits(db):
    """Check generator modes landing at the same or a lower positive grade.

    The chosen S1/S2/S3/S4 are not enlarged here: a nonzero residual is an
    explicit counterexample to this finite truncation, retained separately.
    Every grade includes the vacuum-target modes. This is still finite.
    """
    assert db.meta['completed_grade4']
    specs = []
    for source_grade in (1, 2, 3, 4):
        for i in range(6):
            for target_grade in range(source_grade + 1):
                specs.append((source_grade, target_grade, 'current%d' % i, source_grade - target_grade))
        for left in ('omega', 'u'):
            for target_grade in range(source_grade + 1):
                specs.append((source_grade, target_grade, left, source_grade - target_grade + 1))
    while db.meta['stage'] < len(specs):
        sg, tg, left, n = specs[db.meta['stage']]
        label = '%s_%d:S%d->S%d' % (left, n, sg, tg)
        for i in range(db.meta['cursor'], len(db.order[sg])):
            db.boundary()
            recipe = mode(left, n, db.order[sg][i])
            v = db.evaluate(recipe)
            if tg == 0:
                residual = {s: c for s, c in v.items() if s != (x.ZERO, ())}
            else:
                residual = db.reduce(tg, v)
            db.steps += 1
            if residual:
                witness = {'label': label, 'recipe': recipe, 'source': db.order[sg][i],
                           'residual': packed(residual), 'image': packed(v),
                           'scope': 'A nonzero exact residual disproves preservation of these finite spans.'}
                (db.directory / 'low_mode_failure.json').write_text(json.dumps(witness, indent=2) + '\n')
                db.meta['low_mode_failure'] = {'label': label, 'source': db.order[sg][i]}
                db.save('exact low-mode failure')
                raise RuntimeError('exact low-mode failure: %s on %s' % (label, db.order[sg][i]))
            key = '%d:%s:%d' % (sg, ','.join(map(str, db.rows[db.order[sg][i]]['weight'])), db.meta['stage'])
            db.meta['audits'][key] = db.meta['audits'].get(key, 0) + 1
            db.meta['cursor'] = i + 1
        db.record('passed ' + label)
        db.meta['stage'] += 1
        db.meta['cursor'] = 0
        db.save('audit family complete')
    db.meta['phase'] = 'complete'
    db.meta['all_listed_generator_low_modes_passed'] = True
    db.save('all finite low-mode audits complete')


def replay(db):
    """An exact audit of row identities, separate from generation completion."""
    progress = db.meta.setdefault('replay', {'fields': 0, 'rows': 0})
    fields = list(db.fields.values())
    for i in range(progress['fields'], len(fields)):
        db.boundary()
        r = fields[i]
        assert db.evaluate(r['recipe']) == r['vector'], ('field replay', r['id'])
        progress['fields'] = i + 1
        db.steps += 1
    names = [name for g in sorted(db.order) for name in db.order[g]]
    for i in range(progress['rows'], len(names)):
        db.boundary()
        r = db.rows[names[i]]
        v = db.evaluate(r['recipe'])
        for c, name in r['elimination']:
            v = x.vadd((1, v), (-x.A(c), db.value(name)))
        v = x.vadd((x.A(r['scale']), v))
        assert v == r['vector'], ('row replay', r['id'])
        assert v[min(v)] == x.ONE
        progress['rows'] = i + 1
        db.steps += 1
    progress['completed_for_dimensions'] = db.counts()
    db.save('all saved provenance identities replayed')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checkpoint-dir', required=True)
    ap.add_argument('--phase', choices=('grade3', 'grade4', 'audit', 'replay'), required=True)
    ap.add_argument('--seconds', type=int, default=300)
    ap.add_argument('--max-steps', type=int, default=100000000)
    ap.add_argument('--checkpoint-seconds', type=int, default=45)
    ap.add_argument('--max-nnz', type=int, default=1000000)
    ap.add_argument('--max-coefficient-bits', type=int, default=2048)
    ap.add_argument('--soft-rss-mib', type=int, default=1800)
    args = ap.parse_args()
    cap = resource.getrlimit(resource.RLIMIT_AS)[0]
    assert 0 < cap <= 6 * 1024 ** 3, 'Must use the permanent safe launcher'
    assert len(os.sched_getaffinity(0)) <= 2, 'Need at most two allowed CPUs'
    assert 1 <= args.seconds <= 1800
    assert 10 <= args.checkpoint_seconds <= 120
    assert 64 <= args.soft_rss_mib < cap / 1024 ** 2
    assert 1 <= args.max_nnz <= 3000000
    install()
    db = Database(args)

    def request_stop(*_):
        db.stop = True

    signal.signal(signal.SIGTERM, request_stop)
    signal.signal(signal.SIGINT, request_stop)
    try:
        if db.meta['phase'] == 'init':
            assert args.phase == 'grade3', 'First construct and checkpoint grade3'
            initialize(db)
        if args.phase == 'grade3':
            if not db.meta['completed_grade3']:
                grade3(db)
        elif args.phase == 'grade4':
            assert db.meta['completed_grade3'], 'Finish grade3 first'
            if not db.meta['completed_grade4']:
                grade4(db)
        elif args.phase == 'audit':
            assert db.meta['completed_grade4'], 'Finish grade4 first'
            if db.meta['phase'] != 'complete':
                audits(db)
        else:
            replay(db)
    except BudgetStop as exc:
        db.record('bounded stop: ' + str(exc))
        db.save('bounded stop: ' + str(exc))
        return 75
    print(json.dumps({'status': 'requested phase complete', 'phase': args.phase,
                      'dimensions': db.counts(), 'seconds': monotonic() - db.started,
                      'finite_span_only': True}), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
