# N4 normal-span pilot: resource and certificate review

23 September 2026. Producer: `hi_cft_20260923_next_n4_strong_pilot.py`.
No numerical job was run by the producer's author. The source passed Python
syntax compilation. Root owns every launch and the team-wide numerical slot.

## Scope and decisive outcome

The producer imports only the exact grade-two and grade-three blocks from
`hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024`. It checks their
hashes and the frozen source hashes, the exact dimensions 120 and 956, and
the recorded normal grade-three dimension 634. It authenticates the saved
mode-word graph without loading the old grade-four vectors.

At the good split prime 1000003, with roots sqrt(13)=231543 and
sqrt(-3)=1000, it builds normal weight-four words from K(-1)S3, T S3,
and all ten highest weight-two fields (-1)S2, then closes under the two
current lowering zero modes. The ten fields include both neutral stresses.
It tests their zero modes on the last 322 exact S3 rows and subsequently
checks all remaining required singular products in weights zero through
three. The first 634 S3 rows and the exact generation history establish
the recursive-generator premise independently of properness.

Normal rows and tested singular-product rows have separate echelon spans.
Test rows never enlarge the normal span. Their union is also tracked: rank
6011 of genuine U words contradicts the independently proved conditional
character statement proper U implies dim U4=6010, and therefore proves
U=B through the established dichotomy. The producer automatically stops
on that rank. A failed normal-span test at a smaller union rank alone is
not a properness contradiction. Passing a modular containment test is
not an exact containment proof.

## Liveness and bounds

The intended launch has a 3 GiB address-space ceiling and a 600-second
hard Python alarm, inside the permanent safe launcher. A candidate-boundary
RSS check stops at 768 MiB. The latter is not a hard per-allocation limit;
the address limit and launcher remain the hard resource backstops. The
maximum permitted per-call alarm is 900 seconds, for an explicitly reviewed
resume. Root must not run another numerical job concurrently.

Conservative expected peak is approximately 0.5--0.75 GiB RSS, with 3 GiB
address space providing allocator headroom. This is an estimate, not a
measurement. Included live allocations are:

* At most 300000 imported sparse terms (the saved input is approximately
  224508), their state tuples, finite-field coefficients, and a second set
  of integer echelon dictionaries for the lower-grade membership tests:
  approximately 100--170 MiB including Python object overhead.
* At most 71052 interned B4 states and their index/weight dictionaries:
  approximately 35--60 MiB. The ambient basis is never enumerated.
* One shared LRU cache of reduced rows, including union rows, limited to
  500000 integer sparse terms: approximately 50--80 MiB. Raw words remain
  on disk and only one is decoded for a lowering action.
* Primitive-action caches: 512 vertex and 512 basis actions, plus 128
  creation lists. Each action has fixed output momentum and at most the
  726 oscillator monomials at weight four. Allow approximately 200--300
  MiB in the conservative full-cache case, including tuple/Fraction
  overhead. Both `x.creation` and `e4.creation` are rebound to the bounded
  wrapper, because e4.vertex accesses its own module's creation global.
  Caches are cleared after each atomic save.
* Bounded JSON buffers, one decoded row, current mode output/reduction
  scratch, eight MiB of SQLite page cache, and interpreter/library state:
  approximately 80--130 MiB. The input importer streams a block one row
  at a time and discards each row's serialized elimination metadata.
  Every decoded record is bounded by eight MiB, every accepted/output
  sparse row by 20000 terms. No all-block decoded JSON array is live.

These deliberately overlapping upper allowances approach the RSS stop
boundary. If observed liveness does so, stop and reduce cache bounds in a
new source-bound consumer; do not raise the permanent ceilings. A single
mode can temporarily finish before the candidate-boundary RSS check.

The combined persisted raw and echelon term count is capped at 16 million.
The SQLite database has a hard 512 MiB page cap, 8 MiB page cache, mmap
disabled, and temporary storage on disk. Allow another 512 MiB of disk for
the rollback journal. A full database produces an error and retains the
previous committed checkpoint. It does not allocate the database in RAM.

No reliable wall-time prediction is available before the pilot. There are
6692 descendant seeds, 1200 weight-two seeds, at most twice the accepted
normal rank lowering calls, 3220 zero-mode tests, and 24916 lower-mode tests.
Many vanish or are cheap, but exact lattice action and sparse reduction
cost vary by Cartan block. The first 600 seconds supplies a resumable
measurement, not a promised completion time.

## Atomicity and provenance

SQLite commits states, raw rows, reduced rows, independent union rows,
failure witnesses, and stage cursors in one transaction at stage boundaries
and approximately every 20 seconds. The JSON file is a readable atomic
summary; SQLite is authoritative. The hard alarm rolls back the current
transaction, preserving the last committed cursor. A synchronous reviewed
bound commits a bounded-stop checkpoint. Source hashes include this new
producer, so the file must be frozen after the first launch; a changed
producer requires an explicit new consumer/import lineage.

Every normal row stores its original raw vector, reduced vector, pivot,
Cartan weight, SHA256 raw-vector digest and mode recipe. The `normal_row`
recipe always refers to the prior row's RAW vector. Thus current closure
has a short genuine characteristic-zero normal-word DAG, with no arbitrary
lift of modular echelon coefficients. Exact input references resolve to
the authenticated frozen characteristic-zero checkpoint. Independent
singular-product rows similarly store their raw words and reduced residuals.
Replaying sparse elimination over the fixed prime validates the rank;
recomputing the field-valued words validates the action provenance.

For a positive certificate, select any independent short normal-word
columns from a Cartan block, solve for required target coefficients over
Q(sqrt(13),sqrt(-3)), and verify each entire sparse residual exactly zero.
No characteristic-zero normal-rank upper bound or modular containment
extrapolation is needed. See
`hi_cft_20260923_next_structure_recursive_strong_certificate.md`.

Root launch template after checking the host reserve and sole-job slot:

```sh
python hi_cft_safe_run.py -- python -c 'import resource,runpy; resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3)); runpy.run_path("hi_cft_20260923_next_n4_strong_pilot.py",run_name="__main__")' --seconds 600
```

An outer reviewed timeout can provide an additional wall-clock backstop.
The launcher still enforces the permanent host reserve, thread/CPU limits,
group RSS watchdog, and team-wide lock. This note authorizes no agent job.
