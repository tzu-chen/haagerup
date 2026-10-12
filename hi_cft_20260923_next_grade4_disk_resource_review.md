# Disk-backed exact grade-four continuation

Producer: `hi_cft_20260923_next_grade4_disk.py`. The preceding producer,
mode engine, and checkpoint24 are unchanged. This producer reuses their
arithmetic and exact generation order. Only storage and cache management
change. The implementing agent ran bytecode compilation and lightweight
source/metadata reads, not the importer or any numerical calculation.

## Measured starting point and largest-block risk

Root reports that S3 completed in 377.54 s at 0.197 GiB RSS. The first S4
pilot stopped at its saved-term cap after 41.34 s, with 836 S4 rows and
0.718 GiB RSS. The checkpoint records 998456 sparse terms across S1–S4,
of which 224508 belong to S1–S3. It occupies 28 MiB compressed on disk.
Its maximum retained coefficient height is 410 bits.

The old numerical log records a largest ambient Cartan block of 3078,
and its zero-weight S4 target has rank 280. Thus a dense exact zero block
could contain 861840 coefficient entries by itself. At roughly 700 bytes
per entry it could exceed 0.5 GiB before transient allocations. At this
producer's conservative accounting rate for 410-bit coefficients it exceeds
1 GiB. The existing exact zero block has only 50 rows, so its present size
does not establish that the completed block fits. **A whole-block cache is
therefore not an adequate memory design.**

The replacement automatically streams an oversized block one row at a
time. It does not require the zero block, a second source block, or all S3
to reside in RAM. No coefficient-arithmetic change is needed for this
storage redesign.

## Allocation and liveness review

* The indexed SQLite database stores all exact rows, elimination recipes,
  field provenance, and the logical Cartan-block keys. It has an 8 MiB
  SQLite page cache, disabled memory mapping, file-backed temporary storage,
  and a 1 GiB main-database page limit. A 45 s uncommitted transaction can
  additionally use a rollback journal; this is disk space, not compute RAM.
* The decoded-row LRU is grouped by Cartan block. Its default conservative
  accounting cap is 384 MiB and its accepted maximum is 512 MiB. Eviction
  drops whole old blocks where possible; an oversized active block evicts
  its oldest individual rows. Thus all blocks can exceed the cache cap on
  disk while resident decoded data remains bounded.
* Accounting uses 1024 bytes per term for Python dictionaries, state tuples,
  number-field and Fraction objects, plus eight full-height integers per
  term, eight times the serialized recipe size, and a per-row allowance.
  This deliberately overcounts shared coordinates and small integers. The
  unchanged 2048-bit coefficient cap also covers elimination coefficients
  and normalization. This estimate is checked by the separate soft RSS
  guard during the pilot, not treated as an exact measurement.
* One row is capped at 12000 terms and 8 MiB serialized JSON. The known
  ambient block bound 3078 is much smaller, but is not trusted as a proof
  gate. At maximum allowed coefficient height a single row's conservative
  decoded estimate is below about 36 MiB. A cache miss may briefly retain
  that row in addition to the LRU, before eviction. The source row is used
  to form one candidate vector; target elimination streams earlier rows.
* Frozen checkpoint blocks are imported with a streaming JSON decoder.
  A complete block's `rows` array is never deserialized. During import or
  loading, one encoded row, its parsed JSON lists/strings, and its decoded
  exact dictionary can coexist. Budget 0.2 GiB for these transient objects,
  including serialization of one new row. The field file has a separate
  16 MiB decompressed-input cap and is small in the existing checkpoint.
* Mode caches are reduced to creation128, vertex512, and basis-action1024,
  and cleared at every checkpoint. Budget 0.35 GiB for these caches and
  temporary mode expansions. Grade-four Heisenberg oscillator partitions
  have at most 726 monomials for a fixed momentum, so individual cached
  actions are also small compared with a full block.
* Row/block indexes, stage cursors, source hashes and field definitions
  are small. Retained proof coefficients live on disk with their rows.

These figures suggest a peak below 1.2 GiB for the intended pilot, with
material uncertainty from Python allocator retention and coefficient
growth. Keep the **3 GiB address cap and 1800 MiB soft RSS stop**. The
permanent launcher still enforces one job, two CPUs/threads, 8 GiB group
RSS, at least 32 GiB host MemAvailable, and applicable cgroup limits.
The redesign changes neither permanent caps nor concurrency policy.

## Atomicity and provenance

SQLite uses FULL synchronous mode and rollback-journal transactions.
Accepted rows and the corresponding exact generation cursor are committed
together. A forced kill rolls back to the preceding completed transaction.
Cache eviction cannot lose a dirty row because its insertion is already in
the current SQLite transaction. The database's `state` record is authoritative;
`manifest.json` is a human-readable copy written after each commit.

Import verifies the original manifest and every compressed block hash,
preserves all source hashes and exact provenance, and retains the old
stage/cursor (stage0, cursor836). Import progress records both block and row
cursors, so interrupted import resumes without duplicate insertions. The
old 836 rows are reused. Each compressed row has a bounded gzip decoder
and its original reduction/word recipe. Original `--phase audit` and
`--phase replay` semantics remain available against the row store.

The new source is hash-bound on first import. Freeze it before that launch.
A storage/decompression error exits and preserves the last committed
checkpoint; it is not interpreted as an exact vanishing result. An operation
or time-budget stop returns 75 after committing completed work.

## Proposed bounded pilot, root only

Inspect current host/cgroup memory first. No other numerical job may run.
Import is estimated at 30–90 s; this is unmeasured. Disk decompression and
repeated sparse elimination can make the full continuation considerably
slower than the in-memory pilot. Measure before extending its time budget.

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=15s 180s python hi_cft_20260923_next_grade4_disk.py --store-dir hi_cft_20260923_next_grade4_disk_checkpoint --phase import --seconds 120 --cache-mib 384 --soft-rss-mib 1800
```

Then a separate 180 s generation pilot, from the same database:

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=15s 240s python hi_cft_20260923_next_grade4_disk.py --store-dir hi_cft_20260923_next_grade4_disk_checkpoint --phase grade4 --seconds 180 --cache-mib 384 --soft-rss-mib 1800
```

The producer time budget is checked between operations. The outer timeout
is the hard wall-time boundary. Compare cursor advance, total terms on disk,
reported cache estimate, actual sampled RSS and database size before running
another bounded continuation. Exact full S4 and low-mode stability remain
unfinished until the respective completion flags are recorded.
