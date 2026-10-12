# Exact lower-closure consumer: allocation and proof scope

Prepared23 September2026; root coordinates execution. Producer:
`hi_cft_20260923_next_structure_lower_closure.py`, frozen SHA256
`015ae0525f94219a64c8554c1df9fa05cd669135981dab70c535ed4e13ee1b1f`.
No job was launched by the structure agent.

The consumer uses the root's independently controlled GMP field adapter,
the unchanged lattice mode engine through grade three, and the authenticated
exact S2/S3 checkpoint. The3970 checks comprise ten quasiprimary identities,
2400 weight-two mode-zero/mode-one memberships,1440 current mode-zero/mode-one
memberships, and120 L(1)S2 memberships. The two neutral mode-zero families
run before the charged fields. Some checks are algebraically redundant,
but all are retained as an independent finite replay.

The exact input has approximately225000 sparse terms and is capped at300000.
Allowing up to about1KiB per parsed term, including state keys, four GMP
rationals and dictionary overhead, gives a conservative0.30GiB input
budget. Temporary JSON rows are capped at8MiB by the frozen streaming
reader. Mode caches have128/512/512 entries; their grade-three sparse
outputs and intermediate targets are expected to remain below0.20GiB.
Sparse reduction keeps one target, one residual and at most956 relation
coefficients. SQLite has an8MiB page cache, no mmap, and a256MiB disk-size
cap. Including interpreter, source fields and transient copies, reviewed
expected peak is below0.70GiB; a768MiB measured-RSS boundary stops after
the current finite target.

Execution requires a positive address-space limit at most2GiB. The default
requested call budget is300seconds, with a hard alarm fifteen seconds
later; root should set the launcher wall limit above that alarm. The
permanent safe launcher still enforces the teamwide exclusive numerical
slot, host-memory reserve, thread and CPU caps. The expired September15
exception is not used.

Each exact reduction records its source-bound target recipe, target digest,
all number-field coefficients of the basis relation, and its exact residual
in SQLite. Metadata and records commit atomically every20seconds or at a
clean stop. An alarm or MemoryError rolls back the current transaction;
the last SQLite metadata is authoritative even if a convenience JSON file
is stale. A nonzero exact residual is recorded and stops the consumer.
Only zero residuals count as PASS; modular coincidence is not used.

The output certifies the finite lower relations needed by
`hi_cft_20260923_next_structure_recursive_strong_certificate.md`, including
its Virasoro reduction. It does not by itself prove properness: the exact
A0P3 normal-span identities at weight four remain a separate gate.
