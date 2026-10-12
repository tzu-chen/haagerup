# Prime-support subset for direct exact N5

These two new sources leave all frozen v1 code and artifacts unchanged:

* `hi_cft_20260923_c8two_n5_prime_support.py` is a standalone, standard-library
  finite-prime support extractor.
* `hi_cft_20260923_c8two_n5_direct_exact_v2.py` subclasses the frozen direct
  exact consumer, changing only the selected column set and its pivot coordinates.

The root alone may run either script, serially through the permanent guarded
launcher. Keep the reviewed3 GiB AS ceiling,1400 MiB exact-consumer RSS boundary,
32 GiB host reserve and at most two CPUs/threads. The native exact solve still
requires an external timeout. The permanent6 GiB/8 GiB ceilings are unchanged.

## Mathematical criterion

For at most300 saved projected raw columns and at most three targets, the
helper constructs the saved square prime pivot minor. It solves that minor
using independent forward elimination/back substitution over F_1000003,
checks the solution against every matrix entry, and then verifies the target
relation on every sparse coordinate while streaming the raw columns from disk.

It selects the union of columns with nonzero prime coefficients for at least
one target. A separate row-independence calculation reselects coordinate rows
giving an invertible minor for these columns; a second solve verifies the
restricted minor against the original prime coefficients. The helper records
both original and selected ranks, all selected column IDs, coordinate-state
IDs, prime coefficients and whether there was any reduction. Empty support
is allowed only when all complete prime target vectors are zero.

This is a proposed subset for exact verification. A coefficient that is zero
at the prime may be nonzero over the number field. The exact consumer therefore
reconstructs every selected ordinary recipe and projector, validates its prime
specialization, solves the smaller exact minor, and checks the full exact sparse
residual. A nonzero residual is a failed subset attempt, not a proof that the
target is outside the full normal span. The frozen v1 consumer remains the
fallback, using a fresh output path. If support is dense, v2 records no gain.

The exact modes, caches, number field, FLINT adapter,2048-bit vector bound,
4096-bit relation bound, rank≤300 and512 MiB native preflight are unchanged.
The integer-residual optimization is deliberately not added here; this adapter
uses the already audited exact residual implementation.

## Allocation and time estimate before first launch

Standalone support extraction is expected to use **less than128 MiB RSS**
and ordinarily finish within30 seconds; neither estimate has yet been measured.
Use a first120-second allowance. Its largest dense matrix has90,000 Python
integer entries (about3 MiB); forward-elimination copies and selected-minor
storage add several MiB. It never loads all sparse columns together. At most
one decoded40,000-term column, three40,000-term target dictionaries, and three
residual dictionaries (individually capped120,000 states) coexist. Compressed
input, bounded32 MiB decompression and JSON decoding can temporarily overlap.
The4 MiB SQLite page cache, streaming1 MiB hash buffers and ordinary Python
runtime bring the conservative review estimate to **192 MiB peak**, still
far below the3 GiB launcher ceiling. There are no workers, NumPy or BLAS calls.

The helper checks eight deterministic known-solution systems, eight independent
restricted minors, and refusal of a singular matrix. These controls run only
when the root launches the extractor or v2 adapter. The implementing agent has
only syntax-checked the sources.

Within v2, support extraction runs before the exact provider and action caches
are created, so its dense matrix and decoded column allocations are released
before the larger exact phase. Only the small support record remains. The exact
phase retains the v1 estimate **0.7–1.3 GiB RSS**, with128+64+128 MiB bounded
caches, at most three live targets and the native512 MiB preflight. A successful
reduction lowers exact column reconstruction and native matrix cost. Use600
seconds internally and an external620-second timeout for the first exact run;
no speedup is assumed before measurement.

## Source binding and restart behavior

The helper authenticates the closed prime database, matching summary and full
source graph, and records its own source hash. It refuses a live rollback
journal and caps the source file at512 MiB. The v2 metadata extension binds the
helper's complete deterministic support decision and the v2 adapter source.
Timing/RSS observations are kept separately so policy equality is stable on
resume. The frozen v1 source graph and canonical H4/P4 provider lineage remain
intact. Separate v2 output paths are required; this adapter does not migrate a
completed v1 relation database. It protects new code, source and temporary paths
against overwrite. Atomic exact-vector and relation checkpoints retain the
frozen behavior.

Suggested root-only payloads (inside the appropriate guarded launcher):

```text
python hi_cft_20260923_c8two_n5_prime_support.py --database CLOSED.sqlite --source-summary CLOSED.json --output NEW_support.json --seconds 120
python hi_cft_20260923_c8two_n5_direct_exact_v2.py --database CLOSED.sqlite --source-summary CLOSED.json --output NEW_exact_v2.json --max-rank 300 --seconds 600
```

The support-only output is diagnostic. The v2 consumer recomputes and
authenticates selection itself, so it does not trust an editable support JSON.
