# Independent audit of the exact selected N5 consumer

23 September 2026. Source review only; no execution. Reviewed
[next_n5_exact_selected](hi_cft_20260923_next_n5_exact_selected.py)
and its grade-four provider initialization and reconstruction paths.

The exact field adapter and grade-five recursive mode engine are
installed before provider construction. The h4.Consumer constructor
does not reinstall the older grade-four engine, so later grade-five
targets are not silently truncated. Its smallest nonempty Cartan
block is used only to initialize a bounded provider; the provider's
raw normal-word reconstruction works for arbitrary row IDs across
blocks. No restriction to that dummy initial weight is imposed by
the vector method.

Separate grade5:/target: names in the N5 database and normal:/input:
names in the provider database prevent ID collisions. Each grade-five
raw word is reconstructed from the saved recipe using exact S2/S3
inputs or exact raw N4/canonical P4 fields. Every reconstructed column
and target is specialized back to the authenticated prime record and
must agree on the complete sparse vector.

The selected pivot matrix uses raw exact columns, not modular echelon
rows misread as exact vectors. A nonzero modular pivot minor supplies
the anticipated invertibility; the exact FLINT solve checks it anew.
The regular representation correctly embeds the field into four by
four rational multiplication blocks. The gate is at most300 field
coordinates and at most three right-hand sides here. After solving,
the entire sparse identity is checked; agreement only at the pivot
coordinates cannot produce a false membership certificate.

The two exact-vector caches have separate bounded accounting, along
with term, record and coefficient-height caps. SQLite keeps provider
and N5 records in distinct databases. Discarding an uncommitted provider
cache on interruption is safe: its words remain reconstructible, and
the already committed N5 vectors and exact relations retain source
bindings. All-grade exhaustion and a characteristic-zero rank upper
bound are explicitly outside the output's scope.

The three-GiB hard address limit remains essential during native exact
solves. Python SIGALRM need not interrupt a long ctypes call until it
returns, so root must additionally wrap the process in an external
timeout as the producer documentation requests. No cap increase or
parallel job is authorized by this review.

No mathematical blocker was found. For provenance when reading the
cached-v2 pilot, the author was additionally asked to authenticate its
separate mode_cache_v2 ancestry. Complete exact reconstruction and full
residual verification already protect the mathematics independently
of the cached prime algorithm.

The final source adds and passes review of that nested cached ancestry
check. It also records matrix coefficient height and a four-copy native
matrix allocation estimate, refusing estimates above512MiB before
calling FLINT. This is explicitly a preflight estimate rather than a
guarantee about all native workspaces; the hard cap remains authoritative.
Reviewed frozen source hash:
017356463be10b392c63c82c7a31a33a544777fa06cbb188a5a5efc37793cf73.
