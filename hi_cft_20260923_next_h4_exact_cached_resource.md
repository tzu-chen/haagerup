# Exact H4 action-cache continuation

Root-only producer `hi_cft_20260923_next_h4_exact_cached.py` and helper
`hi_cft_20260923_next_exact_mode_cache.py`. No computation during preparation.
The original bulk directory must be closed. A new directory copies and
hashes its bounded JSON/SQLite files; the ancestor is never edited. Original
source bindings stay intact and a separate exact-cache lineage binds this
wrapper, helper and every ancestor artifact in each new block checkpoint.

The helper memoizes the complete exact action of one registered left field
on one lattice basis state. Number-field linear accumulation is exact and
identical to the original bilinear mode. The cache holds immutable copies
of registered fields, keyed by their full contents, avoiding identity reuse
and permitting the same fields from successive blocks to share actions.
Unregistered fields use the original engine. Twenty full-vector controls
compare ten operators at modes-1,0,1 and scales1 and1+sqrt(13) against that
engine before the cache supplies proof targets. Native solves and full sparse
residual checks remain those of the independently audited frozen consumer.

The cache has a conservative192MiB storage estimate cap,30000entries,
32registered fields of at most500terms,20000terms per cached basis action,
and2048-bit coefficient ceiling. The estimate includes state and rational
objects, limb sizes and LRU overhead. Hard3GiB AS and the existing1400MiB
RSS boundary remain unchanged. The measured uncached consumer used less
than0.3GiB on the first blocks; the additional cache should leave expected
RSS below0.7GiB there. Larger native blocks retain the same hard cap and
existing checkpoint controls. No workers or additional compute threads.

Copying is at most4GiB total,512MiB per file, with constant-size streaming
buffers; a new directory adds at most the ancestor size initially. A whole
job external timeout with a20-second grace over the selected600/900second
bulk window bounds both copying and native calls. The original safe launcher
enforces the shared lock, host reserve, affinity and process-group watchdog.

This is an arithmetic performance change, not a broader certificate claim.
Only exact zero residuals accepted by the frozen consumer count as identities.

The independent structure agent audited the helper, copied-checkpoint
lineage, constructor/save order and resource controls. Root subsequently
corrected one list/tuple concatenation to iterable unpacking; the reviewer
confirmed the fix. The twenty oracle comparisons now use the ambient stress
as the right input and require nonzero results, in addition to exact equality.
Both source files are frozen after those changes.
