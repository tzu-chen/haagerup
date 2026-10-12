# Exact projected N5 relations

`hi_cft_20260923_next_n5_projected_exact.py` consumes a closed
`selected-n5-highest-prime-v1` SQLite/JSON pair. Preparation used reading,
editing and syntax compilation only. Root owns every numerical launch.

The source ordinary N5 word is reconstructed by the frozen exact selected-N5
consumer, which in turn reconstructs grade-four normal words and imports the
canonical exact P4 triplet. This new consumer rederives, rather than trusting,
the ordered rational factors

    product_(h>w, h=w mod2) (1 - F0 E0 / ((h-w)(h+w+2)/4))

for LEFT then RIGHT, with ambient highest-weight bounds4and27. Bounds follow
from lattice norm≤10 in grade five and Cartan norms2and78. Intermediate
coefficients are exact elements of Q(sqrt13,sqrt(-3)); no lifted residue is
treated as an exact coefficient.

Each projected raw column and target must specialize back to the source
prime vector. Both raising-current zero modes must annihilate each exact
projected target. A selected square exact pivot solve is then followed by
the entire sparse residual. Only an exact zero residual proves an identity.
No characteristic-zero rank upper bound is needed. A positive certificate
concerns the projected channel; recovering the complete A0P4 family uses
the separately audited K-equivariance and Clebsch--Gordan triangular argument.

## Resource estimate before a run

* Default projected rank64; CLI hard maximum300, with any increase from64
  requiring root review. The inherited native matrix preflight uses actual
  coefficient heights and stops above a512MiB workspace estimate.
* Three disk-backed vector caches are live: grade-four provider128MiB,
  ordinary grade-five provider128MiB, and projected grade-five cache64MiB.
  Their total estimated LRU retention is320MiB.
* Source states are bounded by71052 grade-four and120000 in each grade-five
  table. The projected source normally has far fewer. Metadata/pivot lists
  are small. Primitive creation/vertex/basis-mode caches remain64/64/128.
* Each exact intermediate has at most40000 sparse terms and2048-bit field
  coefficients. Projection can hold an input, its raised and lowered images,
  and an updated copy simultaneously. Artifact decompression is bounded32MiB
  (16MiB in the inherited grade-four reader). Reserve0.3–0.5GiB for these
  transient objects, state tables, parsed JSON and interpreter/library memory.
* Three derived SQLite files each have a512MiB page limit and independent
  two-million saved-term limit; rollback journals may require more disk.
  No complete database is deserialized, mmap is disabled, and temporary
  storage is on disk. Each cache/provider has source-bound checkpoints.
* Expected peak for rank≤64 is about0.8–1.2GiB RSS, compared with the measured
  ordinary three-target exact run at0.649GiB. A1400MiB RSS boundary and3GiB
  hard AS ceiling apply. Permanent6GiBAS/8GiBgroupRSS/32GiBhost reserve and
  at most two CPU threads remain unchanged. FLINT itself uses one thread.
* Initial600seconds is a bounded pilot, not a completion promise. Projection
  current modes may dominate even when the native matrix is small.

Use an external timeout around native FLINT calls; Python SIGALRM can be
deferred while ctypes is in native arithmetic. The command tail inside the
root-only normal safe launcher with3GiBAS is:

```sh
timeout --signal=TERM --kill-after=5s 620s python hi_cft_20260923_next_n5_projected_exact.py --database CLOSED_PROJECTED.sqlite --source-summary CLOSED_PROJECTED.json --output NEW_EXACT.json --seconds 600
```

Input summary and SQLite metadata must agree on source graph, weight,
projection, cursor, rank and target readiness/count. Local row, target and
state IDs and counts are validated. Full graphs authenticate the original
ordinary N5 source, any cache ancestry, raw grade-four words, exact P4 artifact,
projector and this exact consumer. Each resulting relation stores projected
raw column IDs, exact field coefficients, target recipe and full residual.
Changing source or code requires new output names after the first checkpoint.
