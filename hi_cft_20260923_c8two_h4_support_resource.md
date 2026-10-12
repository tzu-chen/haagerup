# Per-target support minors for the last twelve H4 identities

New root-only adapter: `hi_cft_20260923_c8two_h4_support.py`. It imports the
closed normalized directory into a new authenticated copy, preserving all118
completed relations and cached raw vectors. Original sources/artifacts stay
frozen. No resource ceiling is increased:3 GiB AS, inherited1400 MiB RSS
boundary,32 GiB host reserve, at most two CPUs/threads, rank≤300 and native
preflight≤512 MiB. Use external620-second timeout around copy plus computation
for a600-second initial allowance; the inner main resets its Python alarm and
ctypes native solves need external interruption.

The failed normalization changed maximum matrix height only280→277 bits.
This adapter instead uses the original authenticated raw-column matrix so its
good-prime specialization is unaffected by arbitrary field scalars. It computes
at most three target vectors at a time and solves the full280-dimensional prime
pivot matrix for these RHS using the independently controlled support helper.
For each target separately it retains only nonzero prime coefficient columns,
reselects an invertible coordinate minor, and rechecks that smaller prime solve.
There is no union of supports across targets that could needlessly increase rank.

Each selected exact minor undergoes the unchanged actual-height512 MiB native
preflight. If even one individual support remains too large, the measured rank,
height and estimate are checkpointed and the job stops. Otherwise its exact
solution is padded with zeros to the original280-column basis before the frozen
full integer residual. A prime-zero coefficient is not assumed exact-zero;
only full characteristic-zero residual vanishing certifies containment.
The original normal-word relation format and coefficients are preserved.

The cache-trim proxy sees the selected rank during native solving and restores
the full rank in a finally block before residual verification. Its saved event
records the actual selected native dimension. This does not change the column
list, pivot list or extended-rank certificate metadata. Completed earlier blocks
have no pending targets and are simply retained with authenticated new policy.

Additional allocations above the reviewed trim pipeline are the280² prime
integer matrix (about3 MiB), a bounded elimination copy, and row-reference lists
for one selected exact minor (under1 MiB). The original exact matrix remains
live. At most three3078-term targets coexist (smaller than the old batch8).
Native preflight/caches/intermediate bounds remain unchanged. Expected peak is
0.8–1.3 GiB RSS if a selected minor passes; this is an estimate, not a cap waiver.
Prime support solves and reselection should take seconds to tens of seconds for
the twelve targets; exact/native timing depends on measured supports. No timing
or support arithmetic has been executed by the implementing agent.

Lineage binds the helper, adapter, closed normalized files and all prior
normalization/trim/targeted sources recursively. Final provenance readers must
authenticate `per_target_prime_support.policy` as well as the existing nested
policies. Copying is streamed through1 MiB buffers into a temporary directory,
checks hashes, then atomically renames; each file≤512 MiB, aggregate≤4 GiB disk.

Suggested root payload:

```text
python hi_cft_20260923_c8two_h4_support.py --seconds 600
```

Only syntax checks have been run by the implementing agent.
