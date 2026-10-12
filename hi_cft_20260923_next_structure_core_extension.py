"""Exact grade-two test for an order-13 extension of T tensor PF13.

Run only through hi_cft_safe_run.py, with <=2 GiB address space and a
300-second time cap. No NumPy/SciPy/SymPy or numerical coefficient
recognition is used. Estimated peak <0.5 GiB: 120 sparse input vectors,
at most twelve vectors per Cartan block, bounded 12000-entry mode
caches, and small exact elimination rows. No dense ambient matrices,
worker processes, or detached jobs are created.

This producer only establishes exact membership in the certified S2.
It does not assert that S2 is all of U2. Finding the order-13 simple
current tops, however, gives actual fields in U and an all-weight
simple-current extension by the existing rational fusion rules.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x


def read(rows):
    return {(tuple(r['momentum']), tuple(r['oscillators'])):
            x.A(r['coefficient']) for r in rows}


def serialize(v):
    return [{'momentum': list(a), 'oscillators': list(o),
             'coefficient': list(map(str, c))}
            for (a, o), c in sorted(v.items())]


def kernel(vectors, image):
    """Exact kernel of an ambient sparse map, tracking original vectors."""
    pivots = {}
    answers = []
    for vector in vectors:
        pre = vector.copy()
        out = image(vector)
        while out:
            pivot = min(out)
            if pivot not in pivots:
                scale = out[pivot].inv()
                pivots[pivot] = (
                    {s: c*scale for s, c in out.items()},
                    {s: c*scale for s, c in pre.items()})
                break
            row, lift = pivots[pivot]
            factor = out[pivot]
            out = x.vadd((1, out), (-factor, row))
            pre = x.vadd((1, pre), (-factor, lift))
        else:
            assert pre, 'Input vectors must be linearly independent'
            answers.append(pre)
    return answers


def reconstruct_s2(data):
    """The already certified 120-dimensional S2 reconstruction."""
    span = x.Span()
    for c in x.LEFT+x.RIGHT:
        span.reduce(x.mode(c, -2, x.VAC), True)
        for d in x.LEFT+x.RIGHT:
            span.reduce(x.mode(c, -1, d), True)
    span.reduce(x.omega(), True)
    span.reduce(x.read_field(data['fields'][-1]), True)
    for row in data['fields'][:-1]:
        for v in x.descendants(x.read_field(row), *row['dimensions']):
            span.reduce(v, True)
    assert span.dimension == 120
    assert max(map(len, span.blocks.values())) == 12
    return span


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--output', default=
                        'hi_cft_20260923_next_structure_core_extension.json')
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    assert 0 < args.seconds <= 300
    output = Path(args.output)
    assert not output.exists(), 'Refusing to overwrite a certificate'
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(args.seconds)
    started = monotonic()

    sources = [Path('hi_cft_20260923_c8_exact_fields.json'),
               Path('hi_cft_20260923_proof_potts_exact.json'),
               Path('hi_cft_20260923_proof_pf13_exact.json'),
               Path('hi_cft_20260923_proof_remaining_axes.json')]
    assert all(p.stat().st_size <= 8*1024**2 for p in sources)
    data, potts, pf13, axes = [json.loads(p.read_text()) for p in sources]
    p = read(potts['potts_stress'])
    z = read(pf13['stress'])
    omega_t = x.vadd(
        (Q(1, 4), x.mode(x.LEFT[0], -1, x.LEFT[0])),
        (Q(1, 156), x.mode(x.RIGHT[0], -1, x.RIGHT[0])), (1, p))
    s = x.vadd((1, x.omega()), (-1, omega_t), (-1, z))
    assert not x.vadd((1, s), (-1, read(axes['first_stress'])),
                     (-1, read(axes['second_stress'])))
    assert x.mode(s, 3, s) == {(x.ZERO, ()): x.A(Q(9, 5))}
    assert not x.vadd((1, x.mode(s, 1, s)), (-2, s))
    for stress in (omega_t, z):
        for n in (1, 2, 3):
            assert not x.mode(s, n, stress)

    span = reconstruct_s2(data)
    assert not span.reduce(s)
    print(json.dumps({'stage': 'S2 reconstructed', 'dimension': 120,
                      'seconds': monotonic()-started}), flush=True)

    # Build the entire known (T tensor PF13)_2. V_L has nine states at
    # weight two; add Potts stress, four charged T states, and PF stress.
    known = x.Span()
    core_currents = x.LEFT+(x.RIGHT[0],)
    for c in core_currents:
        known.reduce(x.mode(c, -2, x.VAC), True)
        for d in core_currents:
            known.reduce(x.mode(c, -1, d), True)
    assert known.dimension == 9
    known.reduce(p, True)
    assert known.dimension == 10
    for left in (-1, 1):
        for right in (-13, 13):
            block = span.blocks[(left, right)]
            assert len(block) == 1
            v = next(iter(block.values()))
            assert all(not osc for _, osc in v), 'Charged core top is pure lattice'
            assert not x.vadd((1, x.mode(omega_t, 1, v)), (-2, v))
            assert not x.mode(z, 1, v)
            known.reduce(v, True)
    assert known.dimension == 14
    known.reduce(z, True)
    assert known.dimension == 15
    for block in known.blocks.values():
        for v in block.values():
            assert not span.reduce(v)
            assert not x.mode(s, 1, v)

    records = []
    total_zero = 0
    total_classified = 0
    joint_targets = {Q(0): 'T vacuum grade two',
                     Q(2): 'PF13 stress',
                     Q(12, 13): 'order-13 simple-current candidate',
                     Q(22, 13): 'simple-current or i=10 PF13 candidate'}
    for weight, block in sorted(span.blocks.items()):
        vectors = [v for _, v in sorted(block.items())]
        zero = kernel(vectors, lambda v: x.mode(s, 1, v))
        total_zero += len(zero)
        for v in zero:
            assert not span.reduce(v)
            assert not x.mode(s, 1, v)
        z_images = {id(v): x.mode(z, 1, v) for v in zero}
        eigenspaces = []
        classified = 0
        for eigenvalue, label in joint_targets.items():
            eig = kernel(zero, lambda v: x.vadd(
                (1, z_images[id(v)]), (-eigenvalue, v)))
            classified += len(eig)
            if not eig:
                continue
            entries = []
            for v in eig:
                assert not x.vadd((1, x.mode(z, 1, v)), (-eigenvalue, v))
                assert not x.vadd((1, x.mode(omega_t, 1, v)),
                                 (eigenvalue-2, v))
                entry = {'vector': serialize(v),
                         'outside_known_A2': bool(known.reduce(v))}
                if eigenvalue in (Q(12, 13), Q(22, 13)):
                    expected_p = Q(2, 3) if eigenvalue == Q(12, 13) else Q(0)
                    entry['candidate_Potts_weight'] = str(expected_p)
                    entry['candidate_Potts_weight_verified'] = not x.vadd(
                        (1, x.mode(p, 1, v)), (-expected_p, v))
                entries.append(entry)
            eigenspaces.append({'PF13_weight': str(eigenvalue),
                                'T_weight': str(2-eigenvalue),
                                'dimension': len(eig), 'interpretation': label,
                                'vectors': entries})
        assert classified <= len(zero)
        total_classified += classified
        if zero:
            records.append({'Cartan_weight': list(weight),
                            'S2_block_dimension': len(vectors),
                            'zero_s_energy_dimension': len(zero),
                            'known_A2_dimension': len(known.blocks.get(weight, {})),
                            'classified_dimension': classified,
                            'joint_eigenspaces': eigenspaces,
                            'full_zero_basis': [serialize(v) for v in zero]})
        print(json.dumps({'Cartan_weight': list(weight),
                          'zero_s_energy_dimension': len(zero),
                          'seconds': monotonic()-started}), flush=True)

    # Analytic PF13 top classification: this energy is unique to the
    # i=13 simple-current representatives in the ALY parametrization.
    pf_labels_12 = [(i, j) for i in range(1, 14) for j in range(i)
                   if Q(i*(13-i), 2*13*15)+Q(j*(i-j), 13) == Q(12, 13)]
    assert pf_labels_12 == [(13, 1), (13, 12)]
    target_weights = {(a, b) for a in (-1, 1) for b in (-5, 5)}
    target_weights |= {(0, -8), (0, 8)}
    witnessed = {}
    for row in records:
        weight = tuple(row['Cartan_weight'])
        if weight in target_weights:
            es = [e for e in row['joint_eigenspaces']
                  if e['PF13_weight'] == '12/13']
            if es:
                witnessed[str(weight)] = sum(e['dimension'] for e in es)
                assert all(v['outside_known_A2'] and
                           v['candidate_Potts_weight_verified']
                           for e in es for v in e['vectors'])

    result = {
        'arithmetic': 'Q(sqrt(13),sqrt(-3)); exact sparse elimination',
        'S2_dimension': span.dimension, 'known_T_tensor_PF13_grade2_dimension': 15,
        'zero_s_energy_dimension': total_zero,
        'extra_zero_s_energy_dimension': total_zero-15,
        'classified_dimension': total_classified,
        'order13_target_weight_count': len(witnessed),
        'order13_target_multiplicities': witnessed,
        'all_six_order13_target_weights_present': len(witnessed) == 6,
        'PF13_actual_top_labels_at_12over13': pf_labels_12,
        'blocks': records, 'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': 'Exact kernels in certified S2 only. s=q+r is the remaining '
                 'c=18/5 stress. hPF=12/13 uniquely identifies a PF13 simple '
                 'current; hPF=22/13 alone does not. Existence of the six '
                 'j=+/-5 target states supplies an actual order-13 extension '
                 'candidate; the T/PF charge-sign matching is not inferred '
                 'from conformal weights alone.',
        'source_sha256': {str(f): hashlib.sha256(f.read_bytes()).hexdigest()
                          for f in [Path(__file__), Path(x.__file__), *sources]}}
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('blocks', 'source_sha256')}), flush=True)


if __name__ == '__main__':
    main()
