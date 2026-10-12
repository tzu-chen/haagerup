# Serial H4 exact relation batch: allocation and source review

23 September2026. Producer
`hi_cft_20260923_next_structure_h4_bulk.py`. Root alone may launch.
The author has run no numerical job. This is a new allocation review for
field-matrix rank at most300, not an inherited rank64 authorization.

## Finite scope

The wrapper authenticates the permanently immutable N4 database and exact
grade-three manifest, reads the322 P3 row weights, and groups every
highest-left target by its actual Cartan weight. The default left list is
operators0 through8, hence2898 targets. Operator9 follows from the total
stress/Sugawara identity already independently audited in
`hi_cft_20260923_next_structure_h4_certificate.md`. An optional full ten
families gives3220 targets. No other operator selection is accepted.

The nonempty blocks use the frozen native H4 consumer unchanged. Blocks
are processed in increasing rank, in one process and one thread in
FLINT, with no subprocesses or workers. Each block has its own resumable
exact SQLite identity artifact. The wrapper adds a source-bound policy
and full target-plan digest, so a restart cannot silently change the
left-family selection or target list. Prior completed block identities
are retained and checked by the existing consumer.

Targets in blocks with no selected normal or P4 column must vanish
exactly. They are directly generated from the first block's authenticated
exact input cache and recorded in its separate `zero_relations` table;
they never enter the count of ordinary nonempty-block relations. A
nonzero such target stops with a failed assertion. The final global
count includes both kinds and must equal2898 or3220 before the complete
status is emitted.

The main summary is a progress index. The source-bound per-block SQLite
artifacts, complete sparse residuals and zero-target records are the
mathematical certificates. No modular upper-rank inference is made.

## Initial bounded launch

Use300 seconds for the first call, batch8, address limit3GiB, the normal
8GiB process-group watchdog and32GiB host-memory reserve, at most two
CPUs/threads, and the single team-wide job lock. Root must retain its
external wall timer because Python's signal handler does not preempt a
ctypes call while native code is executing. The wrapper's global alarm
covers planning and all blocks, rather than restarting for each block.

The same actual block matrix and input cache are reused across all
target batches within a block. Between blocks the consumer, exact vector
cache, matrices, connections and native solve temporaries are released;
mode caches are explicitly cleared. Native matrices are freed in the
wrapper's existing `finally` block after each solve. Input rows remain
disk-backed and are separately reauthenticated in every block.

At field rank300, the largest rational regular matrix has1200 squared
entries; actual reviewed N4 ranks are smaller. Native base fmpq entries
occupy about22MiB before large numerators and denominators. The Python
field matrix has at most90000 entries. Include the128MiB bounded vector
LRU, approximately0.1--0.2GiB input/interpreter/state overhead, the three
P4 fields, eight full sparse targets, native integer/rational workspaces
and copies. For the observed modest exact coefficient sizes, estimated
peak is approximately0.5--1.0GiB, but this is not a worst-case arithmetic
height theorem. Clearing rational denominators inside a native solver
can enlarge row least-common-multiples, and determinant/solve intermediates
can exceed the input coefficient heights. The4096-bit output check does
not constrain those native intermediate heights. The inherited1.4GiB
candidate-boundary RSS stop and hard
3GiB address ceiling provide the backstop for unexpectedly large native
intermediates. Never raise those ceilings on failure.

Existing raw-vector2048-bit, relation4096-bit,12000-term vector,
16MiB record and2-million persisted exact-term caps apply separately to
each block. SQLite has an8MiB page cache, mmap disabled, disk-backed
temporary storage and a512MiB database cap per block. Most imported
S2/S3 data are replicated on disk across blocks; reserve several GiB
of disk for a complete run. This replication does not retain all blocks
in RAM. A later storage optimization can share authenticated input rows,
but is unnecessary for this initial bounded pilot.

Root's prior native benchmark established three complete exact sparse
identities at field rank31 in2.33 seconds with approximately0.102GiB RSS.
That supports trying this bounded serial pilot; it does not establish
an upper runtime or arithmetic-height bound for every larger block.
