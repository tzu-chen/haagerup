"""Root-only deterministic exact controls for optional FLINT K-system solve."""
import hashlib
import json
from pathlib import Path
import random
import resource
import signal
from time import monotonic

from gmpy2 import mpq

from hi_cft_20260923_next_fast_field import FastField as F
from hi_cft_20260923_next_flint_field_solve import Flint, regular_block


def mm(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(120)
    started = monotonic()
    random_source = random.Random(202609230831)

    def value():
        return F(tuple(mpq(random_source.randrange(-5, 6), random_source.randrange(1, 8))
                       for _ in range(4)))

    checked = 0
    for _ in range(100):
        a, b = value(), value()
        block = regular_block(a)
        assert F(tuple(sum(block[i][j]*b[j] for j in range(4)) for i in range(4))) == a*b
        checked += 1
    flint = Flint()
    controls = []
    for n in (1, 3, 8, 16):
        # Unit triangular factors guarantee invertibility without relying on
        # a random nonsingularity assumption or the native solver itself.
        lower = [[value() if i > j else F(int(i == j)) for j in range(n)] for i in range(n)]
        upper = [[value() if i < j else F(int(i == j)) for j in range(n)] for i in range(n)]
        a = mm(lower, upper)
        expected = [[value() for _ in range(3)] for _ in range(n)]
        b = mm(a, expected)
        for method in ('dixon', 'multi_mod'):
            tick = monotonic()
            actual = flint.solve(a, b, method)
            assert actual == expected
            assert mm(a, actual) == b
            controls.append({'n': n, 'rhs': 3, 'method': method, 'seconds': monotonic()-tick})
    try:
        flint.solve([[F(0)]], [[F(1)]])
    except ValueError:
        singular_rejected = True
    else:
        raise AssertionError('Singular matrix was accepted')
    paths = [Path(__file__), Path('hi_cft_20260923_next_flint_field_solve.py'),
             Path('hi_cft_20260923_next_fast_field.py')]
    result = {'status': 'exact_flint_regular_representation_controls_passed',
              'FLINT_version': flint.version, 'native_threads': 1,
              'multiplication_controls': checked, 'systems': controls,
              'singular_rejected': singular_rejected,
              'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    path = Path('hi_cft_20260923_next_flint_field_check.json')
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print(result, flush=True)


if __name__ == '__main__':
    main()
