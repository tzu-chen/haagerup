# Whole-left-field mode cache and fast N4 v2

New sources:

* `hi_cft_20260923_next_prime_mode_cache.py`
* `hi_cft_20260923_next_n4_union_cached_v2.py`

No numerical execution was performed by the author. Both sources passed
Python syntax compilation. The frozen fast N4 checker and all frozen mode
engines remain unchanged.

## Arithmetic and controls

For a fixed left field a, the map v -> a_n v is linear over the selected
finite field. The helper caches the ENTIRE a_n action on a single lattice
basis state. It then combines right-input coefficients using ordinary
Python integer multiplication, addition and reduction modulo 1000003.
There are no floating operations and no extrapolation to characteristic
zero. Initialization explicitly rejects the tuple-valued exact field.

The key is (registered-left token, mode, right basis state). The registry
retains a strong reference to each original left dictionary, preventing
identity reuse, and a separate snapshot for the uncached oracle. Registered
left dictionaries are immutable by contract; this holds in the frozen
checker, whose ten source fields are loaded once and never modified.
The primitive engine/field installation must also remain fixed after
constructing the helper.

After the checker has loaded all fields, the wrapper compares ten whole
mode outputs against the original mode function: five different left
fields, each on a full saved grade-three vector and on its coefficientwise
sevenfold rescaling. At least three comparisons must be nonzero, and the
second calls exercise cache hits and plain-integer right coefficients.
The records include source words, vector sizes and output digests. Only
after all ten comparisons pass is x.mode replaced for the main loop.

## Provenance and resume

The closed original fast-checker database is copied with SQLite backup to
a NEW database. Its existing source_sha256 binding and verified prefix of
checks remain intact. A separate `mode_cache_v2` record binds this wrapper,
the cache helper, the frozen original checker, the old database SHA256,
old metadata digest and imported cursor. Source changes are rejected before
the new checker is resumed. The original file is never modified.

The wrapper reuses the frozen Checker's atomic row/cursor transactions,
rank arithmetic, status handling and resource boundaries. Cache statistics
are inserted into its metadata at every save. An alarm rolls back only the
current transaction. Cache contents need not survive a restart: they change
performance, not the source words or results.

The initial source has 1797 of 3220 targets passed. The intended new run
checks only the remaining 1423; this cursor is validated from the database
rather than hardcoded. All output remains finite-prime membership evidence.

## Resource estimate before launch

The original fast checker measured approximately 0.215GiB peak RSS.
The composite cache is capped simultaneously at 300000 output terms and
50000 entries, including empty actions. A conservative allowance of
384 bytes per retained term plus 320 bytes per entry is approximately
126MiB, before a small registry and one working output. Strong references
retain only the ten already-live left fields in this consumer. Allow
another roughly 10--30MiB for control copies, scratch and allocator effects.

Expected total is approximately 0.4--0.6GiB RSS, below the inherited
768MiB candidate-boundary stop. Keep the 3GiB address limit and permanent
launcher watchdog/reserve. The original primitive cache caps remain
creation128, vertex512, basis512; the original dense Cartan-block cache
remains64MiB. All are included in the measured starting point. A single
composite basis action is capped at50000 terms and a registry at256 fields;
the actual grade-four output blocks are much smaller. Large actions that
fit the single-action bound but exceed the remaining cache budget trigger
LRU eviction, never growth beyond the stated caps.

The source checker database is capped at64MiB. Backup uses small SQLite
page caches and disk I/O, not an in-memory database clone. Allow64MiB for
the new database and another64MiB rollback journal. The N4 source span is
still opened read-only with a4MiB page cache.

First call: root only, through `hi_cft_safe_run.py`, AS3GiB, default600s
hard alarm. At most two CPUs/threads and one numerical job team-wide.
The actual acceleration is unmeasured; cache-hit/miss statistics and mode
time will determine whether further use is worthwhile. No speedup factor
is assumed in the proof or resource estimate.
