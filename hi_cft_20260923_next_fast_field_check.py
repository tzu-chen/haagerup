"""Root-only exact arithmetic and lattice-mode equivalence control.

Run through hi_cft_safe_run.py --limit-mib 2048. Peak estimate <0.2GiB,
alarm120s. No large basis or eigensolver. Original sources are read-only.
"""
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as e4
import hi_cft_20260923_next_fast_field as fast


def canonical(value):
    return tuple(Fraction(int(q.numerator), int(q.denominator)) for q in value)


def vector_canonical(vector):
    return {state: canonical(c) for state, c in vector.items()}


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(120)
    output = Path('hi_cft_20260923_next_fast_field_check.json')
    assert not output.exists()
    started = monotonic()
    rng = random.Random(20260923)
    cases = []
    # Include every basis direction and sparse coefficient support, followed
    # by dense random rational cases. Exact old arithmetic is the oracle.
    for support in range(16):
        cases.append(tuple(Fraction(rng.randint(1, 19), rng.randint(1, 19))
                           if support >> i & 1 else Fraction(0) for i in range(4)))
    for _ in range(128):
        cases.append(tuple(Fraction(rng.randint(-1000, 1000), rng.randint(1, 1000))
                           for _ in range(4)))
    field_checks = 0
    for i, value in enumerate(cases):
        old, new = x.A(value), fast.FastField(value)
        other = cases[(i*17+3) % len(cases)]
        old_other, new_other = x.A(other), fast.FastField(other)
        for left, right in ((old+old_other, new+new_other),
                            (old-old_other, new-new_other),
                            (old*old_other, new*new_other)):
            assert canonical(left) == canonical(right)
            field_checks += 1
        for mask in range(4):
            assert canonical(old.conj(mask)) == canonical(new.conj(mask))
            field_checks += 1
        if old:
            assert canonical(old.inv()) == canonical(new.inv())
            assert new*new.inv() == fast.ONE
            field_checks += 2
    source = Path('hi_cft_20260923_c8_exact_fields.json')
    fields = json.loads(source.read_text())['fields']
    e4.install()
    x.creation = lru_cache(maxsize=128)(e4.creation.__wrapped__)
    x.vertex = lru_cache(maxsize=512)(e4.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=1024)(e4.basis_mode.__wrapped__)
    old_fields = [x.read_field(row) for row in fields]
    jobs = []
    for i in (0, 1, len(old_fields)-1):
        for j in (0, len(old_fields)-1):
            for mode in (-1, 0, 1, 2, 3):
                # The weight2 normal product has weight4. These cases cover
                # both it and every potentially nonzero singular output.
                jobs.append((old_fields[i], mode, old_fields[j]))
    v3 = x.mode(old_fields[0], 0, old_fields[-1])
    jobs.extend((current, -1, v3) for current in (x.LEFT[1], x.RIGHT[2]))
    baseline = [vector_canonical(x.mode(a, n, b)) for a, n, b in jobs]
    frozen_jobs = [({s: canonical(c) for s, c in a.items()}, n,
                    {s: canonical(c) for s, c in b.items()}) for a, n, b in jobs]
    fast.install(x)
    for expected, (a, n, b) in zip(baseline, frozen_jobs):
        a = {s: fast.FastField(c) for s, c in a.items()}
        b = {s: fast.FastField(c) for s, c in b.items()}
        assert vector_canonical(x.mode(a, n, b)) == expected
    sources = [Path(__file__), Path(fast.__file__), Path(x.__file__),
               Path(e4.__file__), source]
    result = {'status': 'exact_field_and_mode_equivalence_passed',
              'field_checks': field_checks, 'mode_checks': len(jobs),
              'mode_output_grades': [0, 1, 2, 3, 4],
              'scope': 'Exact arithmetic control on deterministic inputs; not an all-input formal verification of the lattice engine or a properness certificate.',
              'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    output.write_text(json.dumps(result, indent=2)+'\n')
    signal.alarm(0)
    print(result)


if __name__ == '__main__':
    main()
