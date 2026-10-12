"""Export, or independently check, the 120-vector short-generation witness.

Root alone runs either mode through hi_cft_safe_run.py, serially:
  python hi_cft_safe_run.py --limit-mib 2048 -- python \
    c8_reviewability_20260927/export_minimal_generation.py \
    --output c8_reviewability_20260927/minimal_generation_witness.json
  python hi_cft_safe_run.py --limit-mib 1024 -- python \
    c8_reviewability_20260927/export_minimal_generation.py \
    --verify c8_reviewability_20260927/minimal_generation_witness.json \
    --output c8_reviewability_20260927/minimal_generation_checked.json

The export follows the original minimal-generators queue and pivot order.
It records each independent raw vector, its recipe on prior normalized
rows, every elimination factor, the pivot normalization, and expansions
of all eight saved highest vectors, e, and omega. The saved fields are
targets only: generation starts with six currents, omega and explicit u.

Verification imports only standard-library code and check_readable_inputs
(which has no import-time computation beyond small constants). It checks
the coordinate identities, triangular independence, target identities,
recipe DAG shape and source hashes. It does NOT recompute mode products.
Thus independent coordinate verification does not prove the recipe's
raw vector equals its named VOA mode product.

Allocation review: original generation used 0.033 GiB RSS and 1.61 s.
The same <=120-row calculation adds <=120 coefficients per tracked row,
raw/normalized copies and bounded JSON serialization. Expected total
<0.25 GiB, internal RSS boundary 512 MiB, launcher AS <=2 GiB. Maximum
persistent sparse entries 100000, each vector <=2000 entries and each
rational <=2048 bits; source/witness JSON <=30 MiB. Vertex, basis-mode,
dot and cocycle caches <=12000; creation cache <=2048. No dense ambient
basis, numerical library, worker, or higher-grade mode is used. The
export and independent verification each have an internal 180 s cap.
"""

import argparse
from collections import deque
import csv
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
from time import monotonic


ROOT = Path(__file__).resolve().parents[1]
MIB = 1024**2
MAX_VECTOR_TERMS = 2000
MAX_PERSISTENT_TERMS = 100000
MAX_BITS = 2048
MAX_JSON_BYTES = 30 * MIB
SOURCE_NAMES = (
    'hi_cft_20260923_c8_exact.py',
    'hi_cft_20260923_c8_minimal_generators.py',
    'hi_cft_20260923_c8_minimal_generators.json',
    'hi_cft_20260923_c8_exact_fields.json',
    'c8_reviewability_20260927/check_readable_inputs.py',
    'c8_reviewability_20260927/export_minimal_generation.py',
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def boundary():
    need(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 512 * 1024,
         '512 MiB internal RSS review boundary')


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(MIB), b''):
            digest.update(block)
            boundary()
    return digest.hexdigest()


def read_json(path):
    path = Path(path)
    need(path.stat().st_size <= MAX_JSON_BYTES, '30 MiB JSON input cap')
    result = json.loads(path.read_text())
    boundary()
    return result


def bounded(vector):
    need(len(vector) <= MAX_VECTOR_TERMS, 'individual support cap')
    for coefficient in vector.values():
        need(len(coefficient) == 4, 'four coefficient components')
        need(all(max(abs(q.numerator).bit_length(),
                     q.denominator.bit_length()) <= MAX_BITS
                 for q in coefficient), 'coefficient bit cap')
    boundary()
    return vector


def pack(vector):
    bounded(vector)
    return [{'momentum': list(a), 'oscillators': list(o),
             'coefficient': list(map(str, c))}
            for (a, o), c in sorted(vector.items())]


def pack_expression(expression):
    need(len(expression) <= 120, 'expression length cap')
    bounded(expression)
    return [{'index': i, 'coefficient': list(map(str, c))}
            for i, c in sorted(expression.items())]


def write_new(path, value):
    path = Path(path)
    need(not path.exists(), 'refusing to overwrite ' + str(path))
    need(path.parent.is_dir(), 'output parent must already exist')
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
    need(path.stat().st_size <= MAX_JSON_BYTES, '30 MiB JSON output cap')
    boundary()


def export(args, started):
    # The engine is deliberately imported only in export mode.
    sys.path.insert(0, str(ROOT))
    import hi_cft_20260923_c8_exact as x

    # Preserve each function body while lowering the two older cache caps.
    x.dot = lru_cache(maxsize=12000)(x.dot.__wrapped__)
    x.cocycle = lru_cache(maxsize=12000)(x.cocycle.__wrapped__)
    for function in (x.dot, x.cocycle, x.vertex, x.basis_mode):
        need(function.cache_info().maxsize <= 12000, 'mode cache cap')
    need(x.creation.cache_info().maxsize <= 2048, 'creation cache cap')

    source_hashes = {name: sha(ROOT / name) for name in SOURCE_NAMES}
    baseline = read_json(ROOT / SOURCE_NAMES[2])
    data = read_json(ROOT / SOURCE_NAMES[3])
    need(len(data['fields']) == 9, 'eight highest vectors and e expected')
    currents = x.LEFT + x.RIGHT
    omega = bounded(x.omega())
    u = {
        ((0, 0, 0, 0, 0, -1, 1, 1), ()): x.ONE,
        ((0, 0, 0, 1, 1, -1, 0, 0), ()):
            x.A((0, Q(1, 20), Q(3, 20), 0)),
        ((1, 1, 0, 0, 0, -1, 0, 0), ()):
            x.A((0, Q(1, 20), Q(-3, 20), 0)),
    }
    rows, blocks, queue = [], {}, deque()
    persistent = 0
    attempts = 0
    history = []

    def mode(a, n, b):
        need(a and b, 'nonzero mode operands required')
        need({x.grade(s) for s in a} == {x.grade(next(iter(a)))},
             'homogeneous left operand')
        need({x.grade(s) for s in b} == {x.grade(next(iter(b)))},
             'homogeneous right operand')
        target = x.grade(next(iter(a))) + x.grade(next(iter(b))) - n - 1
        need(target == 2, 'only target-grade-two products are authorized')
        return bounded(x.mode(a, n, b))

    def combine(left, factor, right):
        result = left.copy()
        for i, c in right.items():
            value = result.get(i, x.ZERO_A) + factor * c
            if value:
                result[i] = value
            else:
                result.pop(i, None)
        # A rejected candidate may temporarily have its own formal source
        # index in addition to all 120 retained generators.
        need(len(result) <= 121, 'tracked scratch expansion cap')
        return bounded(result)

    def add(raw, recipe):
        nonlocal persistent, attempts
        attempts += 1
        bounded(raw)
        if not raw:
            return
        need({x.grade(s) for s in raw} == {2}, 'weight-two source required')
        weights = {x.weight(s) for s in raw}
        need(len(weights) == 1, 'one Cartan weight per source')
        weight = next(iter(weights))
        block = blocks.setdefault(weight, {})
        index = len(rows)
        remainder, expression = raw.copy(), {index: x.ONE}
        elimination = []
        for pivot, j in sorted(block.items()):
            if pivot not in remainder:
                continue
            coefficient = remainder[pivot]
            remainder = bounded(x.vadd((1, remainder),
                                      (-coefficient, rows[j]['normalized'])))
            expression = combine(expression, -coefficient, rows[j]['in_raw'])
            elimination.append((j, coefficient))
        if not remainder:
            return
        need(index < 120, 'exceeded the proposed 120-dimensional space')
        pivot = min(remainder)
        pivot_coefficient = remainder[pivot]
        scale = pivot_coefficient.inv()
        normalized = bounded({s: scale * c for s, c in remainder.items()})
        expression = bounded({i: scale * c for i, c in expression.items()})
        need(len(expression) <= 120, 'retained expansion cap')
        need(normalized[pivot] == x.ONE, 'unit pivot')
        need(all(p not in normalized for p in block), 'triangular new row')
        row = {'raw': raw, 'normalized': normalized, 'in_raw': expression,
               'recipe': recipe, 'weight': weight, 'pivot': pivot,
               'pivot_coefficient': pivot_coefficient, 'scale': scale,
               'elimination': elimination}
        rows.append(row)
        block[pivot] = index
        queue.append(index)
        persistent += len(raw) + len(normalized) + len(expression) + len(elimination)
        need(persistent <= MAX_PERSISTENT_TERMS, 'persistent support cap')

    for i, current in enumerate(currents):
        add(mode(current, -2, x.VAC),
            {'kind': 'current_mode_vacuum', 'current': i, 'mode': -2})
        for j, other in enumerate(currents):
            add(mode(current, -1, other),
                {'kind': 'current_mode_current', 'left_current': i,
                 'mode': -1, 'right_current': j})
    add(omega, {'kind': 'ambient_conformal_vector'})
    add(u, {'kind': 'explicit_three_vertex_u'})
    initial, iterations = len(rows), 0
    while queue:
        parent = queue.popleft()
        vector, before = rows[parent]['normalized'], len(rows)
        for i in (1, 2, 4, 5):
            add(mode(currents[i], 0, vector),
                {'kind': 'current_zero_action', 'current': i, 'mode': 0,
                 'parent_normalized_basis': parent})
        add(mode(u, 1, vector),
            {'kind': 'u_one_action', 'mode': 1,
             'parent_normalized_basis': parent})
        iterations += 1
        if len(rows) != before:
            history.append([iterations, len(rows)])
    need(len(rows) == iterations == 120, 'complete 120-vector queue')
    need(initial == baseline['initial_span_dimension'], 'original initial rank')
    need(history == baseline['dimension_history'], 'original queue history')
    need(u == x.read_field(data['fields'][-2]), 'explicit u target identity')

    def target_expression(target):
        weights = {x.weight(s) for s in target}
        need(len(weights) == 1, 'one weight per target')
        remainder, normalized_expression, raw_expression = target.copy(), {}, {}
        for pivot, j in sorted(blocks[next(iter(weights))].items()):
            if pivot not in remainder:
                continue
            coefficient = remainder[pivot]
            remainder = bounded(x.vadd((1, remainder),
                                      (-coefficient, rows[j]['normalized'])))
            normalized_expression[j] = coefficient
            raw_expression = combine(raw_expression, coefficient, rows[j]['in_raw'])
        need(not remainder, 'target outside generated span')
        for name, expression in (('raw', raw_expression),
                                 ('normalized', normalized_expression)):
            reconstructed = {}
            for i, coefficient in expression.items():
                reconstructed = bounded(x.vadd((1, reconstructed),
                                                (coefficient, rows[i][name])))
            need(reconstructed == target, 'direct target-coordinate identity')
        return {'vector': pack(target),
                'in_normalized_basis': pack_expression(normalized_expression),
                'in_raw_generators': pack_expression(raw_expression)}

    targets = []
    for i, field in enumerate(data['fields']):
        target = target_expression(bounded(x.read_field(field)))
        target.update({'name': 'e' if i == 8 else 'highest_' + str(i),
                       'saved_field_index': i, 'dimensions': field['dimensions'],
                       'e_weight': field['e_weight']})
        targets.append(target)
    target = target_expression(omega)
    target['name'] = 'omega'
    targets.append(target)
    need(all(sha(ROOT / name) == value for name, value in source_hashes.items()),
         'source changed during export')

    basis = []
    for i, row in enumerate(rows):
        basis.append({
            'index': i, 'recipe': row['recipe'], 'cartan_weight': list(row['weight']),
            'raw_vector': pack(row['raw']), 'normalized_vector': pack(row['normalized']),
            'pivot': {'momentum': list(row['pivot'][0]),
                      'oscillators': list(row['pivot'][1])},
            'pivot_coefficient_before_normalization': list(map(str, row['pivot_coefficient'])),
            'normalization_scalar': list(map(str, row['scale'])),
            'elimination': [{'index': j, 'coefficient': list(map(str, c))}
                            for j, c in row['elimination']],
            'normalized_in_raw_generators': pack_expression(row['in_raw']),
        })
        boundary()
    output = {
        'format': 'short-generation-witness-v1',
        'arithmetic': 'Q(s,t), s^2=13, t^2=-3; coordinates [1,s,t,st]',
        'source_sha256': source_hashes,
        'current_order': ['H_left', 'E_left', 'F_left', 'H_right', 'E_right', 'F_right'],
        'inputs': {'vacuum': pack(x.VAC), 'currents': [pack(c) for c in currents],
                   'omega': pack(omega), 'u': pack(u)},
        'identity_convention':
            'normalized[i] = scale[i] * (raw[i] - sum elimination[i,j]*normalized[j]); '
            'raw[i] has its stated recipe on inputs or earlier normalized rows',
        'basis': basis, 'targets': targets,
        'initial_span_dimension': initial, 'resulting_weight_two_dimension': len(rows),
        'processed_basis_vectors': iterations, 'attempted_vectors': attempts,
        'dimension_history': history, 'persistent_sparse_entries': persistent,
        'seconds': monotonic() - started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': 'Exact short-generation recipes and coordinate witnesses. '
                 'Independent --verify checks coordinate identities and DAG shape; '
                 'it does not recompute the raw mode products or formalize the lattice VOA.',
    }
    write_new(args.output, output)
    recipes_path = args.output.with_suffix('.recipes.tsv')
    coefficients_path = args.output.with_suffix('.target_coefficients.tsv')
    for path in (recipes_path, coefficients_path):
        need(not path.exists(), 'refusing to overwrite ' + str(path))
    with recipes_path.open('x', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['basis_index', 'cartan_weight', 'recipe', 'pivot',
                         'normalization_scalar', 'elimination'])
        for row in basis:
            writer.writerow([row['index'], json.dumps(row['cartan_weight']),
                             json.dumps(row['recipe'], sort_keys=True), json.dumps(row['pivot']),
                             json.dumps(row['normalization_scalar']), json.dumps(row['elimination'])])
    with coefficients_path.open('x', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['target', 'raw_generator_index', 'q0', 'qs', 'qt', 'qst'])
        for target in targets:
            for term in target['in_raw_generators']:
                writer.writerow([target['name'], term['index'], *term['coefficient']])
    print(json.dumps({key: output[key] for key in (
        'resulting_weight_two_dimension', 'processed_basis_vectors',
        'attempted_vectors', 'persistent_sparse_entries', 'seconds', 'peak_rss_KiB')}), flush=True)


def verify(args, started):
    # This reader imports no hi_cft_* research engine.
    from check_readable_inputs import (
        K, linear, dot, LEFT, RIGHT, G, SIMPLE, h, exponential,
        inverse, MOMENTA, U_COEFF,
    )

    witness = read_json(args.verify)
    need(witness['format'] == 'short-generation-witness-v1', 'witness format')
    need(set(witness['source_sha256']) == set(SOURCE_NAMES), 'exact source manifest')
    for name, digest in witness['source_sha256'].items():
        need(sha(ROOT / name) == digest, 'source hash mismatch: ' + name)

    def field(value):
        need(isinstance(value, list) and len(value) == 4,
             'four rational strings required')
        need(all(isinstance(q, str) and len(q) <= 1300 for q in value),
             'rational string size cap')
        result = K(value)
        bounded({0: result})
        return result

    def state(item):
        a, o = item['momentum'], item['oscillators']
        need(len(a) == 8 and all(type(i) is int and abs(i) <= 32 for i in a),
             'bounded eight-dimensional momentum')
        need(len(o) <= 2 and all(type(i) is int and 0 <= i < 16 for i in o)
             and o == sorted(o), 'grade<=2 oscillator encoding')
        return tuple(a), tuple(o)

    def decode(items, grade=2):
        need(len(items) <= MAX_VECTOR_TERMS, 'encoded support cap')
        result = {}
        for item in items:
            s, c = state(item), field(item['coefficient'])
            need(s not in result and c, 'duplicate or zero coordinate')
            a, o = s
            need(dot(a, a) + 2 * sum(i // 8 + 1 for i in o) == 2 * grade,
                 'homogeneous encoded grade')
            result[s] = c
        return bounded(result)

    def expression(items, bound):
        need(len(items) <= 120, 'encoded expression cap')
        result = {}
        for item in items:
            i, c = item['index'], field(item['coefficient'])
            need(type(i) is int and 0 <= i < bound and i not in result and c,
                 'expression has distinct, earlier nonzero coefficients')
            result[i] = c
        return bounded(result)

    def sum_rows(coefficients, vectors):
        result = {}
        for i, c in coefficients.items():
            result = bounded(linear((1, result), (c, vectors[i])))
        return result

    inputs = witness['inputs']
    need(len(inputs['currents']) == 6, 'six input currents')
    vacuum = decode(inputs['vacuum'], 0)
    currents = [decode(v, 1) for v in inputs['currents']]
    omega, u = decode(inputs['omega']), decode(inputs['u'])
    need(vacuum == {((0,) * 8, ()): K(1)}, 'vacuum coordinates')
    expected_currents = [
        h(LEFT), exponential(LEFT), exponential(tuple(-v for v in LEFT), -1),
        h(RIGHT),
        linear(*[(1, exponential(SIMPLE[i])) for i, c in enumerate(RIGHT) if c]),
        linear(*[(-c, exponential(tuple(-v for v in SIMPLE[i])))
                 for i, c in enumerate(RIGHT) if c]),
    ]
    need(currents == expected_currents, 'six explicit current-coordinate formulas')
    gi = inverse(G)
    expected_omega = {((0,) * 8, (i, j)): K(gi[i][j] / (2 if i == j else 1))
                      for i in range(8) for j in range(i, 8) if gi[i][j]}
    need(omega == expected_omega, 'ambient inverse-Gram stress formula')
    need(u == {(a, ()): c for a, c in zip(MOMENTA, U_COEFF)},
         'displayed three-vertex u formula')
    rows = witness['basis']
    need(len(rows) == 120, '120 independent rows required')
    raws, normalized, pivots = [], [], []
    persistent = sum(map(len, currents)) + len(omega) + len(u)
    for i, row in enumerate(rows):
        need(row['index'] == i, 'consecutive basis numbering')
        raw, norm = decode(row['raw_vector']), decode(row['normalized_vector'])
        need(raw and norm, 'nonzero basis vector')
        weight = tuple(row['cartan_weight'])
        need({(dot(LEFT, s[0]), dot(RIGHT, s[0])) for s in raw} == {weight}
             and {(dot(LEFT, s[0]), dot(RIGHT, s[0])) for s in norm} == {weight},
             'Cartan weight of raw and normalized row')
        recipe = row['recipe']
        kind = recipe['kind']
        if kind == 'current_mode_vacuum':
            need(recipe['mode'] == -2 and recipe['current'] in range(6), 'derivative recipe')
        elif kind == 'current_mode_current':
            need(recipe['mode'] == -1 and recipe['left_current'] in range(6)
                 and recipe['right_current'] in range(6), 'current product recipe')
        elif kind == 'ambient_conformal_vector':
            need(raw == omega, 'ambient stress seed coordinates')
        elif kind == 'explicit_three_vertex_u':
            need(raw == u, 'u seed coordinates')
        elif kind in ('current_zero_action', 'u_one_action'):
            parent = recipe['parent_normalized_basis']
            need(type(parent) is int and 0 <= parent < i, 'acyclic mode-parent reference')
            need((kind == 'current_zero_action' and recipe['mode'] == 0
                  and recipe['current'] in (1, 2, 4, 5))
                 or (kind == 'u_one_action' and recipe['mode'] == 1), 'authorized operator')
        else:
            raise ValueError('unknown recipe kind: ' + kind)
        elimination = expression(row['elimination'], i)
        remainder = raw.copy()
        for j, c in elimination.items():
            need(remainder.get(pivots[j], K(0)) == c,
                 'elimination coefficient is the current pivot entry')
            remainder = bounded(linear((1, remainder), (-c, normalized[j])))
        pivot = state(row['pivot'])
        scale = field(row['normalization_scalar'])
        pivot_coefficient = field(row['pivot_coefficient_before_normalization'])
        need(remainder and pivot == min(remainder), 'least-state pivot rule')
        need(remainder[pivot] == pivot_coefficient and scale * pivot_coefficient == K(1),
             'pivot normalization inverse')
        need(bounded(linear((scale, remainder))) == norm, 'raw-elimination normalization identity')
        need(norm.get(pivot) == K(1) and all(p not in norm for p in pivots),
             'unit triangular pivots establish independence')
        need(pivot not in pivots, 'distinct pivot states')
        raws.append(raw)
        normalized.append(norm)
        pivots.append(pivot)
        in_raw = expression(row['normalized_in_raw_generators'], i + 1)
        need(sum_rows(in_raw, raws) == norm, 'normalized expansion in raw generators')
        persistent += len(raw) + len(norm) + len(in_raw) + len(elimination)
        need(persistent <= MAX_PERSISTENT_TERMS, 'persistent support cap')

    data = read_json(ROOT / 'hi_cft_20260923_c8_exact_fields.json')
    need(len(data['fields']) == 9, 'nine saved target fields')
    expected = {}
    for i, row in enumerate(data['fields']):
        items = [{'momentum': item['momentum'], 'oscillators': item['oscillators'],
                  'coefficient': item['Qsqrt13_sqrtminus3'][0]
                                 + item['Qsqrt13_sqrtminus3'][1]}
                 for item in row['coefficients']]
        expected['e' if i == 8 else 'highest_' + str(i)] = decode(items)
    expected['omega'] = omega
    need(u == expected['highest_7'], 'explicit u equals the eighth highest vector')
    need(len(witness['targets']) == 10, 'ten target records')
    seen = set()
    for target in witness['targets']:
        name = target['name']
        need(name in expected and name not in seen, 'distinct target name')
        seen.add(name)
        vector = decode(target['vector'])
        need(vector == expected[name], 'target equals authenticated saved coordinates')
        for key, vectors in (('in_raw_generators', raws),
                             ('in_normalized_basis', normalized)):
            need(sum_rows(expression(target[key], 120), vectors) == vector,
                 'target expansion identity')
    need(seen == set(expected), 'all eight highest fields, e and omega checked')
    report = {
        'format': 'short-generation-coordinate-check-v1',
        'witness': str(args.verify), 'witness_sha256': sha(args.verify),
        'verifier_sha256': sha(Path(__file__)),
        'arithmetic_helper_sha256': sha(ROOT / 'c8_reviewability_20260927/check_readable_inputs.py'),
        'basis_rows': 120, 'unit_triangular_independence': True,
        'raw_elimination_normalization_identities': 120,
        'normalized_in_raw_identities': 120, 'target_names': sorted(seen),
        'target_expansions_checked_in_two_bases': 20,
        'mode_recipe_DAG_shape_checked': True, 'mode_products_recomputed': False,
        'vacuum_currents_omega_u_coordinate_formulas_checked': True,
        'source_hashes_match': True, 'persistent_sparse_entries': persistent,
        'seconds': monotonic() - started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': 'Independent exact coordinate, rank and target-expansion verification. '
                 'Mode-product recipes and the VOA interpretation remain separate inputs.',
    }
    write_new(args.output, report)
    print(json.dumps(report), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--verify', type=Path)
    parser.add_argument('--seconds', type=int, default=180)
    args = parser.parse_args()
    need(0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2 * 1024**3,
         'run through the guarded launcher with AS at most 2 GiB')
    need(1 <= args.seconds <= 180, 'time cap at most 180 seconds')
    need(not args.output.exists(), 'refusing to overwrite output')
    if args.verify is None:
        for suffix in ('.recipes.tsv', '.target_coefficients.tsv'):
            need(not args.output.with_suffix(suffix).exists(), 'refusing to overwrite TSV')
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('180-second review cap')))
    signal.alarm(args.seconds)
    started = monotonic()
    if args.verify is None:
        export(args, started)
    else:
        verify(args, started)


if __name__ == '__main__':
    main()
