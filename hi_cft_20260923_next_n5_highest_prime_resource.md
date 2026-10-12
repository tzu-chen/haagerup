# Bounded N5 current-highest projection consumer

Producer: `hi_cft_20260923_next_n5_highest_prime.py`. Preparation performed
syntax parsing only; root alone may execute numerical work.
Frozen producer SHA256:
`63b0c9cf9883204cd93c9577a952a3e73c591dc117059bc80bc7f6461a1635a0`.
Independent structure audit passed the projection mathematics, raw-word
provenance, row reduction, checkpoints and resource caps. The exact-consumer
author separately audited the paired schema and provenance. No source
correction remained after adding the requested optional early-success path.

The input is a closed selected-N5 SQLite database and matching JSON summary.
For one nonnegative Cartan weight, every saved raw normal column is projected
with the two commuting rational polynomials

    P_w(FE) = product_(j=w+2,w+4,...≤Jmax) (1−FE/[(j−w)(j+w+2)/4]).

The reviewed grade-five bounds are Jmax=(4,27); E acts before F. Every
denominator is checked nonzero modulo the saved split prime. Each projected
vector is checked to be killed by both raising operators. Targets also pass
projection idempotence. Twelve original-engine current-action comparisons,
the two sl2 bracket normalizations and all cross-current commutators run
before projection. The current-action cache is the frozen audited helper.

Input raw vectors are streamed one at a time. The source-state list has at
most120000 grade-five states. The new encountered-state map has the same cap;
only states actually occurring in the selected projected block are retained.
At most40000 terms are permitted in a vector or projection intermediate,
300 independent projected rows,250000 row-cache terms,300000 cached primitive
current-action terms and50000 such entries. A projection step holds the
current vector, raised vector and lowered vector; it releases intermediates
before the next factor. No ambient basis, dense matrix or eigensolver exists.

Conservative liveness: up to0.10GiB source state storage,0.15GiB new state and
reverse-ID maps,0.15GiB current-action cache,0.04GiB row LRU,0.10GiB live sparse
intermediates/serialization and0.15GiB Python/library reserve, around0.69GiB
at the explicit caps. The expected small weight benchmark should be lower.
A1GiB RSS boundary is checked after each current action and source column;
the safe launcher enforces3GiB AS. These are lower than the permanent caps.

The SQLite cap is512MiB, with at most16million saved raw/echelon terms,
8MiB output and4MiB input SQLite caches, file-backed temporary storage and
no mmap. Checkpoints commit after each target and approximately20seconds
of columns. A timeout or cap stop rolls back the current transaction and
retains the preceding atomic checkpoint. Reusing the same new output is
allowed only with identical source hashes, selected weight and factors.
No original input file is changed. The process has a global alarm, default
300seconds and maximum600seconds; an external timeout provides a backstop.

Known op7 regression, whose unprojected exact identities have already passed:

    python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=5s 310s python hi_cft_20260923_next_n5_highest_prime.py --seconds 300 --weight 1,15

For new op6 information, after its fresh producer is closed, specify its
`--database` and `--source-summary`, a new `--output`, and one of weights
`1,9`, `1,7`, `1,5`. Each selected source column receives a projection record;
independent projected raw columns carry their original row ID, full source
word and ordered rational factors. The exact projected consumer can replay
that chain over Q(sqrt13,sqrt(-3)) and solve a much smaller pivot matrix.

Passing this prime pilot only supplies discovery data. A nonzero residual
against a partial selected source span is not a new-generator proof. Exact
full sparse residuals are required for positive membership certificates.
The all-source-columns flag refers to the saved block, not the full N5 space.
The optional `--early-contained` checks after25 columns or10 new ranks and
permits success from a sufficient subset, setting that flag false when
columns remain. The default still projects the complete saved block.
All permanent single-job, host-reserve, two-thread and no-worker rules apply.
