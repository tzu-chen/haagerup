"""Independent streaming rank/word-graph audit of the frozen X3v2 output.

No vertex modes are recomputed. Root alone launches via safe_run, AS<=3GiB,
RSS review1GiB, hard alarm600s. Retain only independently rebuilt echelon
rows and scalar word metadata; never all raw vectors or a full JSONL parse.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x


PRIME = 1000003
MAX_LINE = 2*1024**2
MAX_FILE = 384*1024**2
MAX_SUMMARY = 16*1024**2


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def file_hash(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024**2), b''):
            result.update(chunk)
    return result.hexdigest()


def read_json(path):
    path = Path(path)
    assert path.stat().st_size < MAX_SUMMARY
    return json.loads(path.read_text())


def prefix_hash(path, count):
    assert 0 <= count <= MAX_FILE
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        remaining = count
        while remaining:
            chunk = stream.read(min(remaining, 1024**2))
            assert chunk
            result.update(chunk)
            remaining -= len(chunk)
    return result.hexdigest()


def unique_weight(vector):
    weights = {x.weight(state) for state in vector}
    assert len(weights) == 1
    return weights.pop()


def add_weight(a, b):
    return tuple(s+t for s, t in zip(a, b))


def x2_metadata():
    certificate = read_json('hi_cft_20260923_next_x2_conditional_rank.json')
    checked = read_json('hi_cft_20260923_next_x2_replay.json')
    assert certificate['prime'] == PRIME
    assert certificate['rank_lower_bound'] == 1250
    assert checked['rank_independently_verified'] == 1250
    assert checked['exact_X1_orthogonality_verified']
    for data in (certificate, checked):
        for path, expected in data['source_sha256'].items():
            assert file_hash(path) == expected, path
    weights, terms = [], 0
    raw_hash = hashlib.sha256()
    with Path(certificate['independent_vectors_file']).open('rb') as stream:
        while True:
            line = stream.readline(MAX_LINE+1)
            if not line:
                break
            assert len(line) <= MAX_LINE and line.endswith(b'\n')
            raw_hash.update(line)
            row = json.loads(line)
            assert row['id'] == len(weights)
            weights.append(tuple(row['Cartan_weight']))
            terms += len(row['vector'])
    assert len(weights) == 1250
    assert raw_hash.hexdigest() == certificate['independent_vectors_sha256']
    return weights, terms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', default='hi_cft_20260923_next_x3_conditional_rank_v2.json')
    parser.add_argument('--output', default='hi_cft_20260923_next_x3_replay.json')
    args = parser.parse_args()
    output = Path(args.output)
    assert not output.exists(), 'Refusing overwrite'
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('600-second replay cap')))
    signal.alarm(600)
    started = monotonic()
    certificate = read_json(args.certificate)
    assert certificate['format'] == 'x3-word-span-v2'
    assert certificate['prime'] == PRIME
    assert certificate['square_roots_mod_prime'] == [231543, 1000]
    assert 231543**2 % PRIME == 13 and 1000**2 % PRIME == PRIME-3
    assert certificate['status'] in ('complete', 'saturated', 'bounded_stop')
    assert certificate['combined_terms'] <= 4000000
    for path, expected in certificate['source_sha256'].items():
        assert file_hash(path) == expected, path

    ancestry = certificate['v1_ancestry']
    assert file_hash(ancestry['certificate_file']) == ancestry['certificate_sha256']
    old = read_json(ancestry['certificate_file'])
    assert old['format'] == 'x3-word-span-v1'
    assert old['rank_lower_bound'] == ancestry['imported_rank']
    assert old['records_bytes'] == ancestry['records_bytes']
    assert old['records_sha256'] == ancestry['records_prefix_sha256']
    assert old['combined_terms'] == ancestry['imported_combined_terms']
    assert old['combined_terms'] <= 2000000
    for path, expected in old['source_sha256'].items():
        assert certificate['source_sha256'][path] == expected
    assert file_hash(ancestry['producer_file']) == ancestry['producer_sha256']
    assert prefix_hash(ancestry['records_file'], ancestry['records_bytes']) == ancestry['records_prefix_sha256']
    assert prefix_hash(certificate['records_file'], ancestry['records_bytes']) == ancestry['records_prefix_sha256']

    dimensions = read_json('hi_cft_20260923_c8_grade3_exact_v2.json')
    assert dimensions['grade_three_span_dimension'] == 956
    assert dimensions['characteristic_zero_span_dimension_certified']
    for path, expected in dimensions['source_sha256'].items():
        assert file_hash(path) == expected, path
    x2_weights, input_terms = x2_metadata()
    assert input_terms == certificate['input_X2_terms']
    field_data = read_json('hi_cft_20260923_c8_exact_fields.json')
    ordered_fields = sorted(enumerate(field_data['fields'][:-1]),
                            key=lambda item: (len(item[1]['coefficients']), item[0]))
    charged_weights = [unique_weight(x.read_field(row)) for _, row in ordered_fields]
    expected_operators = [{'kind': 'certified_S2_highest', 'field_index': i,
                           'dimensions': row['dimensions']} for i, row in ordered_fields]
    assert certificate['charged_S2_operators'] == expected_operators
    current_weights = [unique_weight(c) for c in x.LEFT+x.RIGHT]
    # The actual u consists of the three frozen momenta below; its scalar
    # coefficients are source-bound but no mode coefficient is replayed.
    u_weights = {x.weight((a, ())) for a in
                 ((0,0,0,0,0,-1,1,1), (0,0,0,1,1,-1,0,0),
                  (1,1,0,0,0,-1,0,0))}
    assert len(u_weights) == 1
    u_weight = u_weights.pop()

    states = [(tuple(a), tuple(o)) for a, o in certificate['states']]
    assert len(states) == len(set(states)) == certificate['known_state_count'] <= 11586
    assert all(x.grade(state) == 3 for state in states)
    state_weights = [x.weight(state) for state in states]
    rows, accepted_weights = {}, []
    raw_terms = row_terms = 0
    record_hash = hashlib.sha256()
    largest_raw = largest_row = 0
    committed = certificate['records_bytes']
    assert committed <= MAX_FILE
    assert Path(certificate['records_file']).stat().st_size >= committed
    with Path(certificate['records_file']).open('rb') as stream:
        while stream.tell() < committed:
            line = stream.readline(MAX_LINE+1)
            assert len(line) <= MAX_LINE and line.endswith(b'\n')
            assert stream.tell() <= committed
            record_hash.update(line)
            record = json.loads(line)
            idx = len(accepted_weights)
            assert record['id'] == idx
            raw, saved_row = dict(record['vector']), dict(record['echelon_row'])
            assert len(raw) == len(record['vector']) and len(saved_row) == len(record['echelon_row'])
            assert record['vector'] == sorted(record['vector'])
            assert record['echelon_row'] == sorted(record['echelon_row'])
            assert digest(record['vector']) == record['vector_sha256']
            assert digest(record['echelon_row']) == record['echelon_row_sha256']
            weight = tuple(record['Cartan_weight'])
            for vector in (raw, saved_row):
                assert vector
                assert all(0 <= i < len(states) and 0 < c < PRIME for i, c in vector.items())
                assert all(state_weights[i] == weight for i in vector)

            word = record['word']
            op, mode = word['operator'], word['mode']
            if word['kind'] == 'X2_mode':
                source = word['X2']
                assert 0 <= source < len(x2_weights)
                source_weight = x2_weights[source]
                if op[0] == 'current':
                    assert len(op) == 2 and 0 <= op[1] < 6 and mode == -1
                    operator_weight, operator_grade = current_weights[op[1]], 1
                elif op == ['omega']:
                    assert mode == 0
                    operator_weight, operator_grade = (0,0), 2
                else:
                    assert len(op) == 2 and op[0] == 'charged_S2'
                    assert 0 <= op[1] < len(charged_weights) and mode == 0
                    operator_weight, operator_grade = charged_weights[op[1]], 2
                assert operator_grade+2-mode-1 == 3
            else:
                assert word['kind'] == 'accepted_X3_mode'
                source = word['source']
                assert 0 <= source < idx
                source_weight = accepted_weights[source]
                if op[0] == 'current':
                    assert len(op) == 2 and op[1] in (1,2,4,5) and mode == 0
                    operator_weight, operator_grade = current_weights[op[1]], 1
                else:
                    assert op == ['u'] and mode == 1
                    operator_weight, operator_grade = u_weight, 2
                assert operator_grade+3-mode-1 == 3
            assert add_weight(source_weight, operator_weight) == weight

            # Independent elimination uses only earlier independently rebuilt
            # rows, never the producer's saved row as an elimination input.
            reduced = dict(raw)
            block = rows.setdefault(weight, {})
            for pivot in sorted(block, key=lambda i: states[i]):
                coefficient = reduced.get(pivot, 0)
                if coefficient:
                    for i, value in block[pivot].items():
                        new = (reduced.get(i, 0)-coefficient*value) % PRIME
                        if new:
                            reduced[i] = new
                        else:
                            reduced.pop(i, None)
            assert reduced, 'Saved independent vector is dependent'
            pivot = min(reduced, key=lambda i: states[i])
            inverse = pow(reduced[pivot], -1, PRIME)
            reduced = {i: c*inverse % PRIME for i, c in reduced.items()}
            assert pivot == record['pivot_state_id'] and pivot not in block
            assert reduced == saved_row, 'Independent normalized row differs'
            block[pivot] = reduced
            accepted_weights.append(weight)
            raw_terms += len(raw)
            row_terms += len(reduced)
            largest_raw = max(largest_raw, len(raw))
            largest_row = max(largest_row, len(reduced))
            assert input_terms+raw_terms+row_terms <= 4000000
            if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 1024**2:
                raise MemoryError('1 GiB replay RSS review threshold')
        assert stream.tell() == committed
    assert record_hash.hexdigest() == certificate['records_sha256']
    rank = len(accepted_weights)
    assert rank == certificate['rank_lower_bound']
    assert raw_terms == certificate['raw_X3_terms']
    assert row_terms == certificate['echelon_X3_terms']
    assert input_terms+raw_terms+row_terms == certificate['combined_terms']
    block_ranks = {str(w): len(block) for w, block in sorted(rows.items())}
    assert block_ranks == certificate['Cartan_block_ranks']
    result = {'status': 'PASS', 'prime': PRIME,
              'rank_independently_verified': rank,
              'raw_vector_rank_and_saved_echelon_rows_verified': True,
              'source_hashes_verified': True, 'v1_import_prefix_verified': True,
              'word_graph_grades_and_Cartan_weights_verified': True,
              'vertex_mode_coefficients_recomputed': False,
              'scope': 'Independent finite-field row-rank and normalized-echelon replay, plus source/import hashes and acyclic mode-word graph. Mathematical mode coefficients remain certified by the frozen deterministic producers, not independently recomputed here. Unrecorded dependent candidates and exhaustion are not independently replayed.',
              'conditional_consequence': ('If U is proper, U3=S3 has dimension956.' if rank == 10630
                                         else 'Rank above10630 contradicts properness.' if rank > 10630
                                         else 'Conditional lower bound on dimX3 only.'),
              'Cartan_block_ranks': block_ranks,
              'largest_raw_vector_terms': largest_raw,
              'largest_echelon_row_terms': largest_row,
              'echelon_terms_retained': row_terms,
              'input_raw_echelon_terms_verified': input_terms+raw_terms+row_terms,
              'certificate_file': args.certificate,
              'certificate_sha256': file_hash(args.certificate),
              'records_file': certificate['records_file'],
              'records_bytes_verified': committed,
              'records_prefix_sha256': record_hash.hexdigest(),
              'v1_ancestry': ancestry,
              'source_sha256': {str(Path(__file__)): file_hash(__file__),
                                **certificate['source_sha256']},
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    temporary = output.with_suffix(output.suffix+'.tmp')
    with temporary.open('w') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(output)
    signal.alarm(0)
    print({'output': str(output), 'rank': rank, 'seconds': result['seconds'],
           'peak_rss_KiB': result['peak_rss_KiB']}, flush=True)


if __name__ == '__main__':
    main()
