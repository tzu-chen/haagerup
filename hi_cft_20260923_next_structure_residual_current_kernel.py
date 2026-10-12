"""Exact residual weight-two fields preserving the six known currents.

Root-only job under hi_cft_safe_run.py; <=2 GiB AS and300 seconds.
Estimated peak below0.25 GiB: five frozen sparse residual fields,
ten grade-one images, exact elimination with five columns, and the
existing bounded mode caches. No dense ambient basis, SymPy, workers,
higher grades, or floating arithmetic. The input certificate already
proves this is the full five-dimensional residual weight-two space.
"""

import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
from hi_cft_20260923_next_structure_core_extension import read, serialize, kernel
from hi_cft_20260923_next_structure_residual_tensor import coordinate_map


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(300)
    started = monotonic()
    source = Path('hi_cft_20260923_next_structure_residual_tensor.json')
    assert source.stat().st_size <= 8*1024**2
    data = json.loads(source.read_text())
    assert data['exact_dimension'] == 5 and data['exact_closure_verified']
    basis = list(map(read, data['basis']))
    coordinates = coordinate_map(basis)
    current_span = x.Span()
    for current in x.LEFT+x.RIGHT:
        current_span.reduce(current, True)
    assert current_span.dimension == 6

    def images(field):
        return [current_span.reduce(x.mode(field, 1, current))
                for current in x.RIGHT[1:]]

    def image(field):
        return {(j, state): coefficient
                for j, vector in enumerate(images(field))
                for state, coefficient in vector.items()}

    # The saved first two tensor basis vectors are the actual q and r.
    assert data['basis_description'] == 'q,r, then three vectors orthogonal to q and r'
    assert not image(basis[0]) and not image(basis[1])
    found = kernel(basis, image)
    for field in found:
        assert not image(field)
        # Check all six currents, not just the two defining images.
        for current in x.LEFT+x.RIGHT:
            assert not current_span.reduce(x.mode(field, 1, current))

    known = x.Span()
    known.reduce(basis[0], True)
    known.reduce(basis[1], True)
    kernel_is_qr = len(found) == 2 and all(not known.reduce(v) for v in found)
    result = {
        'full_residual_grade2_dimension': 5,
        'known_current_dimension': 6,
        'map': 'v -> (v_1 E+ mod K1, v_1 E- mod K1)',
        'map_rank': 5-len(found),
        'kernel_dimension': len(found),
        'kernel_exactly_span_q_r': kernel_is_qr,
        'kernel_basis': list(map(serialize, found)),
        'kernel_coordinates': [[list(map(str, c)) for c in coordinates(v)]
                               for v in found],
        'basis_image_pairs': [[serialize(v) for v in images(field)] for field in basis],
        'all_six_current_preservation_checked_on_kernel': True,
        'conditional_consequence': (
            'If U is proper then U1=K1, so Com(AL,U)2 is exactly span(q,r).'
            if kernel_is_qr else 'No dimension-two coset conclusion.'),
        'scope': 'A conditional obstruction; does not prove U proper.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), Path(x.__file__), source,
                                    Path('hi_cft_20260923_next_structure_core_extension.py'),
                                    Path('hi_cft_20260923_next_structure_residual_tensor.py'))}}
    output = Path('hi_cft_20260923_next_structure_residual_current_kernel.json')
    assert not output.exists(), 'Refusing to overwrite a certificate'
    output.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print({k: v for k, v in result.items() if k not in
           ('kernel_basis', 'kernel_coordinates', 'basis_image_pairs', 'source_sha256')}, flush=True)


if __name__ == '__main__':
    main()
