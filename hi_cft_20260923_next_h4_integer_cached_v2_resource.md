# Integer residual continuation and explicit32-RHS batches

New sources: `hi_cft_20260923_next_integer_residual.py` and
`hi_cft_20260923_next_h4_integer_cached_v2.py`. Neither frozen mode-cache nor
cached-bulk source is edited. No numerical job was run by the author.

Each raw column has a cached common denominator D_j and four integral
coordinates per state. Each relation coefficient is c_j/C_j. With
L=lcm(D_target,C_j D_j), the helper computes

    (L/D_target) target_integer
      - sum_j [L/(C_j D_j)] mul_K(c_j,column_j_integer)

using the exact rules s²=13,t²=-3. FastField rational coordinates are created
only for a nonzero residual, using Fraction objects directly so Python's
integer-to-decimal digit limit cannot destroy a large failure witness.
Source coefficient heights are bounded2048bits, relation coefficients4096,
the common denominator32768bits and the accumulator20000states. Separate
denominator metadata survives eviction from the64MiB integer-column LRU.
Column identities are immutable within each Consumer instance.

Controls before new certificate writes comprise16 deterministic synthetic
systems covering all four field components, denominator clearing, exact
cancellation, nonzero residual and cached reuse, plus the first actual H4
relation compared to the original FastField residual and a nonzero rational
perturbation compared by both methods. Existing source records and exact
relation coefficient format remain unchanged.

The new adapter accepts explicit `--integer-batch 32` (default32, maximum32).
The native solver already supports64RHS; no native or mode source changes.
The copied target loop bounds every target by3078states before appending it
and retains the2048-bit coefficient bound. At typical measured coefficient
sizes,32live targets require roughly70MiB, versus35MiB for16; native RHS and
solution arrays add only a fewMiB. The full field pivot matrix and its solve
remain serial, with existing rank≤300 and the3GiBAS ceiling. Batch size is
recorded explicitly in the new policy and solver metadata; the old public
bulk CLI's16limit is not silently changed.

Live retained caches are192MiB exact whole-action,128MiB exact raw vectors,
and64MiB integer columns,384MiB total. Before constructing a cleared record,
its integer storage estimate must be≤96MiB. The accumulator allocation
estimate must be≤512MiB, including maximum source/coefficient heights and
sum growth. Target integer rows, one active integer column, batch targets,
source state tables and parsed records coexist with those caches. The20000
accumulator-state check occurs at column boundaries; a generic intermediate
union can transiently contain40000states before stopping. The reviewed H4
Cartan spaces have width at most3078, so this generic extreme is outside the
intended run;3GiBAS remains the hard fallback protection. The normal
expected peak is approximately0.7–1.1GiBRSS; boundary checks retain the existing
1400MiB stop. Conservative exceptional preflights may stop earlier. The hard
3GiBAS bound remains the final allocation protection; permanent6GiBAS,
8GiBgroupRSS,32GiBhost reserve and twoCPUthread limits remain unchanged.

Migration is allowed only after the prior cached writer closes. It copies
at most200JSON/SQLite files, each≤512MiB and together≤4GiB, without loading
them into memory. Original file hashes are verified on each copy. The copied
old exact_cache_lineage policy is validated and remains the old wrapper's
STATE policy, so existing per-block assertions keep their exact meaning.
A separate integer_residual_lineage manifest binds both new sources, the
old wrapper/helper, every closed cached-ancestor file, the explicit batch
and that legacy policy. Completed exact records are retained verbatim.

Root alone launches after the numerical slot is free. Use the normal safe
launcher with3GiBAS and an external timeout (native ctypes calls may defer
Python alarms), for example this command tail:

```sh
timeout --signal=TERM --kill-after=5s 620s python hi_cft_20260923_next_h4_integer_cached_v2.py --integer-batch 32 --seconds 600 --batch 16
```

Use a new destination directory for different source or batch policy. The
new helper performs a complete exact residual check and supplies no modular
or tolerance-based acceptance path.
