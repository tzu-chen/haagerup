# Independent X3 replay review

New checker: `hi_cft_20260923_next_x3_replay.py`. Syntax passed; no
execution by the author. Root alone owns the numerical slot.

The completed v2 producer retained2,911,752 input/raw/echelon sparse terms
and used0.300 GiB peak RSS. This checker retains only independently
rebuilt echelon rows, the state catalog and one Cartan-weight tuple per
accepted word. Raw vectors and their producer rows are parsed one line
at a time and discarded after comparison. Expected peak RSS is0.15–0.35
GiB; retain the conservative1 GiB RSS review threshold and3 GiB hard AS
limit. No mode-engine cache or collection of X2 raw vectors is created.
Source hashes stream1 MiB chunks, records are limited to2 MiB each, and
summary/committed record caps are16 MiB /384 MiB. The permanent machine
limits and required safe_run launcher remain in force.

The checker independently eliminates every committed raw X3 vector
modulo1000003, in the original row order and lexical state-pivot order.
Its future reductions use only its own rebuilt rows. It verifies every
normalized row against the saved row, row/vector digests, source hashes
(including nested X2/replay and exact S3 sources), rank and term counts,
Cartan block ranks, grade-three state catalog, and the acyclic word graph
with correct field grades, mode indices and Cartan weights. It verifies
the v1 ancestry certificate hash and the imported prefix against both
the old vector file and the initial bytes of the new vector file.

It does not recompute vertex-mode coefficients or unrecorded dependent
candidates; therefore it independently certifies the rank of the saved
vectors and checks their provenance graph, not the producer's complete
mode calculation or exhaustion assertion. The conditional U3=956 result
needs only the10630 lower rank and the frozen word provenance, not
exhaustion. No characteristic-zero upper rank is inferred from reduction.

Time is likely seconds to tens of seconds; a sub-few-second runtime is
not promised for10630 rows. A600-second internal alarm and external630s
timeout bound the first run. Failure produces no success certificate.

Suggested root-only command:

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=15s 630s python hi_cft_20260923_next_x3_replay.py
```
