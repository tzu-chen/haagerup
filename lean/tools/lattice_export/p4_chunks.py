#!/usr/bin/env python3
"""The chunking spec of the triplet data, shared by gen_p4.py (Lean data), export_p4_controls.py
(partial results of the mode engine) and the future Lean replay generator.

Written 4 October 2026.  Pure functions on the vectors of p4.json; import, do not run.

States.  A field of p4.json is a list of terms [momentum (8 ints), codes, 4 coefficients]; its
states are sorted by (momentum, codes), which is the order `LatticeVOA.stateCmp` of the Lean
model (lexicographic momentum, then codes, shorter prefix first).

Data chunks (built in Lean as P4Data<F><c>.lean, F = P plus, Z zero, M minus).
    data_chunks(v)  : DATA_CHUNKS consecutive blocks of the sorted states, each cut moved forward to
                      the next change of momentum.  A single root vector (E_L, F_L) then maps each
                      chunk to a vector supported on its own momentum classes, so the left-current
                      controls are checked chunk by chunk (P4EL*, P4FL*: done).
Control sub-chunks (not built yet).
    control_subchunks(v, control) : for each data chunk c, consecutive sub-chunks of at most
                      SUB_STATES[control] states, as (c, j, terms).  For E_R, F_R (seven root
                      vectors) and L(2) = omega_(3) the images of different momenta can cancel or
                      combine, so the replay needs the partial images as data:
        1. export_p4_controls.py writes, per control and sub-chunk, image_(c, j) = cur_(n) sub_(c, j)
           (mode engine; the root runs it);
        2. a Lean generator writes, per sub-chunk, a QVec data file `p4<F>_<c>_<j>` (one QA
           coefficient per state) and per control the check
               sort4 (toVec4Q (modeQRF cur n p4<F>_<c>_<j>)) = image_(c, j)
           (ModeHH.lean: modeQRF, the fastest kernel evaluator; link toVQ_modeQRF = modeC)
           with the image as Vec4 data, plus per data chunk the check that its sub-chunks add up
           to p4<F>_<c> (with zero components dropped), and per control the merge check
               sum_(c, j) image_(c, j) = expected (0, q0, q- or the L(2) total);
        3. the link: toVQ_modeQRF, toV4_toVec4Q give cur_(n) q = expected in V.
    SUB_STATES is sized from the measured kernel costs with modeQRF (Benchmark.md section 5):
    E_R/F_R about 36 ms per state, omega_(3) about 30 ms per state; target about 2.5-3 s and
    at most 1.4 GiB per check file.
"""
DATA_CHUNKS = 4
SUB_STATES = {'eL_qp': 600, 'fL_qp': 600, 'eR_qp': 75, 'fR_qp': 75, 'fR_q0': 75, 'fR_qm': 75,
              'L2_qp': 90}


def sorted_states(v):
    return sorted(v, key=lambda t: (tuple(t[0]), tuple(t[1])))


def data_chunks(v, k=DATA_CHUNKS):
    """k consecutive blocks of the sorted states, cuts moved forward to changes of momentum."""
    v = sorted_states(v)
    size = (len(v) + k - 1) // k
    cuts, i = [0], size
    while i < len(v):
        while i < len(v) and v[i][0] == v[i - 1][0]:
            i += 1
        if i < len(v):
            cuts.append(i)
        i += size
    cuts.append(len(v))
    return [v[a:b] for a, b in zip(cuts, cuts[1:])]


def control_subchunks(v, control, sub_states=None):
    """[(c, j, terms)]: sub-chunks of at most sub_states states inside each data chunk c."""
    n = sub_states or SUB_STATES[control]
    out = []
    for c, chunk in enumerate(data_chunks(v)):
        for j, a in enumerate(range(0, len(chunk), n)):
            out.append((c, j, chunk[a:a + n]))
    return out
