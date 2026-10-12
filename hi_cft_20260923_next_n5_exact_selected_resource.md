# Exact selected grade-five relation consumer

`hi_cft_20260923_next_n5_exact_selected.py` is a root-only consumer. No numerical
run was made by its author. Syntax compilation and independent source audits
by `structure_routes` and `c2_axes` passed before launch.

It proves at most the three selected identities `A[7]_0 P4_plus/zero/minus`.
It reconstructs genuine raw grade-four normal words, forms the selected
grade-five normal words, and checks every reconstruction against its saved
good-prime specialization. A square exact pivot solve is followed by the
**entire sparse residual**, so success means an exact identity over
`Q(sqrt(13),sqrt(-3))`. It does not prove a characteristic-zero rank upper
bound, exhaust the grade-five normal span, or establish properness alone.

The source N5 writer must be closed. Both its SQLite file and readable JSON
summary are authenticated, along with the source DAG and canonical P4
artifact. Cached-v2 sources additionally authenticate wrapper/helper bindings
and their immutable ancestor SQLite hash. Pass the cached source paths explicitly
when using the resumed pilot. The original pilot stopped with ranks82,161,250
and no contained targets; an exact solve against that incomplete column family
is unlikely to help. Prefer the subsequently completed containment snapshot.

## Allocation and wall-time review

* One serial Cartan block at a time, smallest first. Hard selected rank gate300;
  FLINT receives a rational regular-representation system of size at most1200.
  At most three right-hand sides are live, normally only one in each block.
* Grade-four provider and grade-five consumer each have a128MiB estimated LRU.
  Exact vectors remain disk backed; neither the whole normal span nor all
  checkpoint rows are simultaneously deserialized.
* Primitive caches are64creation,64vertex,128basis-mode entries. Source state
  tables are capped at71052 grade-four and120000 grade-five states. Source
  accepted row/pivot metadata is small. Canonical P4 has only6989 total terms.
* An individual exact vector has at most40000 terms and2048-bit coefficients.
  One compressed record expands to at most32MiB in the new consumer; the old
  provider retains its16MiB limit. JSON text, parsed lists, coefficient objects,
  the current output dictionary, and a copied target residual can overlap.
  Reserve roughly0.25–0.4GiB for these transient objects, state tables, caches
  outside the LRUs, interpreter and native-library baseline.
* Each derived database has a512MiB page cap and an independent two-million
  retained-term cap; SQLite caches total24MiB including the two source readers.
  Temporary files use disk and memory mapping is disabled. Rollback journals
  can require additional disk space, not a second resident database.
* Before each native solve the consumer records actual coefficient height and
  estimates four dense regular-matrix copies, with64bytes plus rounded
  numerator/denominator limbs per entry. Estimates above512MiB stop for
  review. This is a workspace estimate, not a proven bound on all FLINT
  allocations. The hard process address limit is the final protection.
* Expected peak with modest observed coefficients is approximately0.7–1.2GiB
  RSS. A boundary stops at1400MiB RSS; the reviewed hard AS ceiling is3GiB.
  The permanent6GiB AS/8GiB group-RSS and32GiB host reserve remain unchanged.
* Exact grade-five mode expansion may dominate;600seconds is an initial
  bounded pilot, not a completion promise. Each completed target and each
  reconstructed-vector checkpoint survives interruption. The grade-four
  provider has its own source-bound resumable cache.

FLINT runs one thread. Native ctypes calls may defer Python's SIGALRM handler;
an **external process timeout is required**, in the same guarded process group.
Root must use the sole numerical slot, the normal host-memory checks and
`hi_cft_safe_run.py`, with a reviewed3GiB AS profile. The command tail is:

```sh
timeout --signal=TERM --kill-after=5s 620s python hi_cft_20260923_next_n5_exact_selected.py --seconds 600
```

No worker processes or detached jobs are used.

## Certificate and resume

Grade-four names stay `normal:<id>` / `input:<id>` in a separate provider
database; grade-five names are `grade5:<id>` and `target:<id>`. Every saved
exact vector and relation has a SHA256 of canonical JSON. Relations store the
complete raw-word column coefficient list and full residual. Only an empty
exact residual passes. A nonzero residual refutes membership in the selected
column subset only. Rank and allocation stops preserve earlier identities.

Sources are frozen once the first checkpoint is made. To change code or import
a different source snapshot, use new output names; existing outputs reject
different source hashes. The optional `--weight 1,15` supports a small first
block benchmark without claiming the other two targets have been proved.
