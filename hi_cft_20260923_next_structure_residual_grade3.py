"""Exact residual kernel in the certified 956-dimensional S3.

ROOT ONLY: safe_run, AS<=2 GiB, internal alarm<=300 seconds. No job is
launched by writing/importing this producer. Estimate <0.6 GiB RSS: only
the 58-dimensional Cartan-zero checkpoint block is loaded; decompressed
JSON is capped at32 MiB, input sparse terms at100000, and mode caches at
512/2048/4096 entries. No full ambient grade-three space is enumerated.
The output is unconditional about S3 and conditional about the full U3.
"""

from fractions import Fraction as Q
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3
from hi_cft_20260923_next_structure_core_extension import read, serialize, kernel


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''):
            value.update(chunk)
    return value.hexdigest()


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(300)
    started = monotonic()
    output = Path('hi_cft_20260923_next_structure_residual_grade3.json')
    assert not output.exists(), 'Refusing to overwrite a certificate'
    directory = Path('hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    manifest_path = directory/'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    assert manifest['format'] == 'exact-cartan-span-v1'
    assert manifest['completed_grade3'] and manifest['dimensions']['3'] == 956
    for path, expected in manifest['sources'].items():
        assert digest(path) == expected, ('Frozen source changed', path)
    filename = 'grade3_weight_0_0.json.gz'
    compressed = directory/filename
    assert compressed.stat().st_size < 2*1024**2
    assert digest(compressed) == manifest['files_sha256'][filename]
    with gzip.open(compressed, 'rb') as stream:
        raw = stream.read(32*1024**2+1)
    assert len(raw) <= 32*1024**2, 'Decompressed input cap'
    block = json.loads(raw)
    del raw
    assert block['grade'] == 3 and block['weight'] == [0, 0]
    assert len(block['rows']) == 58
    basis = [{(tuple(a), tuple(o)): x.A(c) for a, o, c in row['vector']}
             for row in block['rows']]
    del block
    assert sum(map(len, basis)) <= 100000
    input_span = x.Span()
    for vector in basis:
        assert all(x.grade(state) == 3 and x.weight(state) == (0, 0)
                   for state in vector)
        input_span.reduce(vector, True)
    assert input_span.dimension == 58

    x.creation = lru_cache(maxsize=512)(g3.creation.__wrapped__)
    x.vertex = lru_cache(maxsize=2048)(g3.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=4096)(g3.basis_mode.__wrapped__)
    sources = [Path('hi_cft_20260923_proof_potts_exact.json'),
               Path('hi_cft_20260923_proof_pf13_exact.json'),
               Path('hi_cft_20260923_proof_remaining_axes.json')]
    potts, pf, axes = [json.loads(path.read_text()) for path in sources]
    p, z = read(potts['potts_stress']), read(pf['stress'])
    q, r = read(axes['first_stress']), read(axes['second_stress'])
    omega = x.omega()
    omega_a = x.vadd((1, omega), (-1, q), (-1, r))
    expected_a = x.vadd((Q(1, 4), x.mode(x.LEFT[0], -1, x.LEFT[0])),
                       (Q(1, 156), x.mode(x.RIGHT[0], -1, x.RIGHT[0])),
                       (1, p), (1, z))
    assert omega_a == expected_a
    print({'Cartan_zero_S3': len(basis), 'input_terms': sum(map(len, basis)),
           'seconds': monotonic()-started}, flush=True)
    vectors = kernel(basis, lambda v: x.mode(omega_a, 1, v))
    residual_span = x.Span()
    for vector in vectors:
        assert not input_span.reduce(vector)
        assert not x.mode(omega_a, 1, vector)
        # Positive energy of the regular unitary core identifies this
        # stress kernel with its commutant. Redundant annihilation tests
        # below never create grade four; stress mode zero is unnecessary.
        for current in x.LEFT+(x.RIGHT[0],):
            for n in range(4):
                assert not x.mode(current, n, vector)
        for stress in (p, z):
            for n in range(1, 5):
                assert not x.mode(stress, n, vector)
        residual_span.reduce(vector, True)
    assert residual_span.dimension == len(vectors)

    descendants = [x.mode(omega, 0, v) for v in (q, r)]
    descendant_span = x.Span()
    for vector in descendants:
        assert not input_span.reduce(vector)
        assert not residual_span.reduce(vector)
        descendant_span.reduce(vector, True)
    assert descendant_span.dimension == 2
    primary = kernel(vectors, lambda v: x.mode(omega, 2, v))
    for vector in primary:
        for n in (2, 3, 4):
            assert not x.mode(omega, n, vector)
    assert len(primary)+2 == len(vectors)
    result = {
        'arithmetic': 'Q(sqrt(13),sqrt(-3))',
        'certified_S3_dimension': 956,
        'Cartan_zero_S3_dimension': 58,
        'residual_S3_dimension': len(vectors),
        'translation_descendant_dimension': 2,
        'Virasoro_primary_grade3_dimension': len(primary),
        'basis': list(map(serialize, vectors)),
        'primary_basis': list(map(serialize, primary)),
        'translation_basis': list(map(serialize, descendants)),
        'core_zero_modes_and_positive_modes_checked': True,
        'scope': 'Exact kernel of omega_AL,1 on the frozen S3. Under the '
                 'separate proper-case certificate U3=S3, this is the full '
                 'weight-three space of Com(AL,U). No properness claim.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(path): digest(path) for path in
            [Path(__file__), Path(x.__file__), Path(g3.__file__),
             Path('hi_cft_20260923_next_structure_core_extension.py'),
             manifest_path, compressed, *sources]}}
    output.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print({key: value for key, value in result.items() if key not in
           ('basis', 'primary_basis', 'translation_basis', 'source_sha256')}, flush=True)


if __name__ == '__main__':
    main()
