# X3 v2 measured-budget continuation review

New source: `hi_cft_20260923_next_x3_conditional_rank_v2.py`.
The v1 producer and its checkpoint remain unchanged. This source has
passed syntax checking only; the author has run no numerical work.

The root's v1 pilot reached rank8290 at1,999,987 combined stored terms
in148.70 seconds, using0.174 GiB peak RSS. The stop was the internal
term-review cap, not a process/machine resource limit. The reviewed v2
term cap is4,000,000. Linear scaling of that measured peak suggests
about0.35 GiB; allow0.6 GiB expected for import, caches, Python objects,
one candidate/elimination workspace and JSON temporaries. There is no
claim that this is a hard analytical RSS ceiling. The1 GiB RSS review
threshold at completed-candidate boundaries and3 GiB hard address-space
limit are unchanged. All permanent machine limits remain unchanged:
root owns the sole numerical slot, safe_run must be used, the group-RSS
watchdog is8 GiB, host MemAvailable reserve32 GiB, and at most two CPUs /
threads. Do not increase those permanent ceilings.

V2 delegates all mode calculations, candidate order and integer sparse
elimination to the frozen v1 source. It changes the internal term cap
and checkpoint format, adds an explicit import and stronger streaming
reload checks, and optionally permits one extra rank beyond the equality
threshold. It remains limited to600 seconds per invocation, including
verification/import/reload. Completion time is unknown; the remaining
closure/charged-field stages may cost more than the initial seed stage.

Import verifies the complete v1 source-hash map and the committed JSONL
prefix hash. It copies only those authenticated bytes to a separate v2
vector file; it never edits, truncates or resumes v1. The v2 certificate
binds both producers, all inherited mathematical sources, the old summary
file hash, and an ancestry record with the old prefix hash/byte count,
rank and term count. Existing old rows and their exact mode-word DAG are
retained verbatim. Newly accepted rows use the same provenance schema.

No complete vector JSON document is parsed in memory. Prefix copy streams
one line at a time; subsequent resume parses one line at a time directly
into retained raw/echelon dictionaries. Each record is capped at2 MiB,
the entire committed record file at384 MiB, and the summary at16 MiB.
A grade-three homogeneous vector has at most11586 state coordinates, so
the individual-record cap is comfortably above its expected serialized
size. V1's two-million-term prefix is never duplicated as a deserialized
list during import. The old/new files coexist on disk, not as two copies
of the vectors in RAM.

Atomic-prefix checkpoints retain the v1 semantics: JSONL flush/fsync,
then atomic summary replacement, every30 seconds at candidate boundaries
and every stage. Interruptions preserve the previous committed prefix.
An interrupted initial import can leave only the authenticated imported
prefix; restart verifies that prefix before creating its summary. Resume
may discard only the v2 uncommitted tail. All source hashes are immutable
after the first v2 checkpoint. Reload verifies raw/echelon hashes,
weights, state ranges, nonzero residues, pivots and counts, but does not
claim independent recomputation of the elimination or vertex modes.

Default stop rank10630 proves U3=S3 of dimension956 conditional on U
proper. `--stop-rank10631` permits one extra independent vector; that
would contradict properness using dimB3=11586 and S3 subset U3 of
dimension956. A saturated10630 v2 checkpoint may be resumed with the
10631 option without editing its source. A complete exhausted certificate
or already-reached requested threshold is refused.

Root-only suggested equality-threshold launch:

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=15s 630s python hi_cft_20260923_next_x3_conditional_rank_v2.py
```

Root-only optional contradiction-threshold continuation:

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=15s 630s python hi_cft_20260923_next_x3_conditional_rank_v2.py --stop-rank 10631
```
