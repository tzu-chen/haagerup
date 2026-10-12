#!/usr/bin/env python3
"""Partial results of the direct triplet controls, chunk by chunk, for Lean kernel replay
(Benchmark.md section 5; record hi_cft_20260923_next_structure_p4_controls.json).

Written 4 October 2026 by the S2-replay agent; NOT run by its author (job admission is the root's).

Why chunks.  The Lean kernel spends about 0.2 GiB per second of evaluation, so a control such as
F_R(0) q+ = q0 on the 2,313-state vector q+ cannot be one kernel check.  It is replayed as
    F_R(0) chunk_i = R_i      (one small kernel check per chunk of q+),
    sum_i R_i = q0            (one merge check),
and this script supplies the R_i.

Controls (by the sl2 relations, which Lean derives with the commutator formula, the 12 non-Cartan
current identities of the record reduce to these six; L(2)P4 in S2 reduces to L(2)q+):
    eL_qp : E_L(0) q+        expected 0
    fL_qp : F_L(0) q+        expected 0
    eR_qp : E_R(0) q+        expected 0
    fR_qp : F_R(0) q+        expected q0
    fR_q0 : F_R(0) q0        expected q-
    fR_qm : F_R(0) q-        expected 0
    L2_qp : omega_(3) q+     (grade two; the total is recorded for the S2 membership step)

Input: lean/tools/lattice_export/p4.json (export_p4.py; the vectors of the record).  The input
field is cut by the shared spec p4_chunks.control_subchunks: inside each data chunk of gen_p4.py
(momentum-aligned, P4Data<F><c>.lean), consecutive sub-chunks of at most SUB_STATES[control]
states (--states-per-chunk overrides it), so that the partial results match the Lean replay.

Engine: hi_cft_20260923_c8_exact.py with hi_cft_20260923_proof_general_modes_v2.install(4)
(MAX_GRADE 4), the same as export_fields.py; modes x.mode(u, n, v) on sparse dict vectors.  No
ambient bases are built: each chunk is a dict of at most --states-per-chunk states, its image is
computed, appended to the output file and released; only the running total (one vector of the
size of the expected result, at most about 2,400 states) is kept, to assert the expected identity
at the end.

Output: one JSON-lines file per control, lean/tools/lattice_export/p4_controls/<control>.jsonl:
    line 1: {"control", "current", "mode", "input", "expected", "states_per_chunk", "chunks"}
    then one line per sub-chunk: {"index", "data_chunk", "sub", "first", "last", "n_states",
    "image"} with "image" packed
    like s2.json ([momentum, codes, 4 coefficients "p/q"] sorted by state);
    last line: {"total_terms", "matches_expected": true, "total": packed (L2_qp only)}.
Each control is asserted against its expected value (L2_qp: grade two) before the final line is
written.

Memory estimate.  Engine caches: general_modes_v2.vertex lru 256 and basis_mode lru 128
(entries are tuples of at most a few hundred (state, coefficient) pairs at grade <= 4, i.e. at
most about 30 MB together), proof_exact4.creation lru 2048 (at most about 80 MB), and the small
integer caches of c8_exact (dot, cocycle: 16,384 entries each, a few MB) and
oscillator_inner (20,000 ints).  Data: p4.json parsed (1.6 MB of JSON, about 25 MB of Python
objects), one chunk and its image (a few MB), the running total (at most about 2,400 states,
about 2 MB).  The record's own run (projections and all 18 controls on the same vectors with
smaller caches) peaked at 264 MiB.  Estimated peak 0.25-0.4 GiB; run time a few minutes.

Run from the repository root through the resource guard:
    ~/.local/bin/research-safe-run --memory-mib 1024 --limit-mib 2048 --threads 1 -- \\
        python3 lean/tools/lattice_export/export_p4_controls.py
(--states-per-chunk overrides p4_chunks.SUB_STATES and must then be passed to the Lean generator
too; --only <control> restricts to one control.)
"""
import argparse
import hashlib
import json
import resource
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
import hi_cft_20260923_c8_exact as x  # noqa: E402
import hi_cft_20260923_proof_general_modes_v2 as g  # noqa: E402
sys.path.insert(0, str(HERE))
import p4_chunks  # noqa: E402  (the chunking spec)

g.install(4)

# index into x.LEFT + x.RIGHT = (hL, eL, fL, hR, eR, fR)
CONTROLS = [
    ('eL_qp', 1, 0, 'P4_plus', None),
    ('fL_qp', 2, 0, 'P4_plus', None),
    ('eR_qp', 4, 0, 'P4_plus', None),
    ('fR_qp', 5, 0, 'P4_plus', 'P4_zero'),
    ('fR_q0', 5, 0, 'P4_zero', 'P4_minus'),
    ('fR_qm', 5, 0, 'P4_minus', None),
    ('L2_qp', 'omega', 3, 'P4_plus', 'grade2'),
]


def q(c):
    c = Q(c)
    return f"{c.numerator}/{c.denominator}"


def packed(v):
    return [[list(a), list(o), [q(t) for t in c]] for (a, o), c in sorted(v.items())]


def read(vector):
    out = {}
    for a, o, c in vector:
        val = x.A(tuple(Q(t) for t in c))
        if val:
            out[(tuple(a), tuple(o))] = val
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--states-per-chunk', type=int, default=None)
    ap.add_argument('--only', default=None)
    args = ap.parse_args()
    n = args.states_per_chunk
    assert n is None or 1 <= n <= 2400
    p4_path = HERE / 'p4.json'
    data = json.loads(p4_path.read_text())
    fields = {f['id']: f['vector'] for f in data['fields']}
    currents = x.LEFT + x.RIGHT
    outdir = HERE / 'p4_controls'
    outdir.mkdir(exist_ok=True)
    started = time.monotonic()
    for name, cur, mode, src, expected in CONTROLS:
        if args.only and name != args.only:
            continue
        u = x.omega() if cur == 'omega' else currents[cur]
        chunks = p4_chunks.control_subchunks(fields[src], name, n)
        path = outdir / f'{name}.jsonl'
        tmp = path.with_suffix('.jsonl.tmp')
        total = {}
        with tmp.open('w') as out:
            out.write(json.dumps({'control': name, 'current': cur, 'mode': mode, 'input': src,
                                  'expected': expected,
                                  'states_per_chunk': n or p4_chunks.SUB_STATES[name],
                                  'chunks': len(chunks),
                                  'p4_sha256': hashlib.sha256(p4_path.read_bytes()).hexdigest()})
                      + '\n')
            for i, (c, j, chunk) in enumerate(chunks):
                v = read(chunk)
                image = x.mode(u, mode, v)
                for state, coeff in image.items():
                    x.add(total, state, coeff)
                out.write(json.dumps({'index': i, 'data_chunk': c, 'sub': j,
                                      'first': chunk[0][:2], 'last': chunk[-1][:2],
                                      'n_states': len(chunk), 'image': packed(image)}) + '\n')
            if expected is None:
                ok = not total
            elif expected == 'grade2':
                ok = all(x.grade(s) == 2 for s in total)
            else:
                ok = total == read(fields[expected])
            assert ok, ('control failed', name)
            out.write(json.dumps({'total_terms': len(total), 'matches_expected': True,
                                  'total': packed(total) if expected == 'grade2' else None})
                      + '\n')
        tmp.replace(path)
        print(json.dumps({'control': name, 'chunks': len(chunks), 'total_terms': len(total),
                          'seconds': round(time.monotonic() - started, 1),
                          'peak_rss_MiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024}),
              flush=True)


if __name__ == '__main__':
    main()
