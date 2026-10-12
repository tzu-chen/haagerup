# Prioritized primitive N5 candidate order

New wrapper: `hi_cft_20260923_c8two_n5_primitive_priority.py`.
All frozen sources remain unchanged. Root-only serial numerical launch,
3 GiB AS,1 GiB prime RSS boundary,32 GiB host reserve, at most two CPUs/threads.
Use300 seconds internally and an external320-second timeout for a first run.

The wrapper keeps exactly the frozen primitive candidate family and target
list. It places all primitive products first, in their existing order. It then
places descendants in operator order E_left,E_right,translation,H_left,H_right,
F_left,F_right. Within each operator, the canonical P4 source fields precede
saved raw grade-four rows; the sort is stable within these groups. No candidate
is omitted or duplicated. This is a performance heuristic, not an additional
mathematical assumption or an exhaustion claim.

The new input subclass and source file are installed only inside this process.
The wrapper hash enters the complete source graph before checkpoint comparison,
and the entire reordered recipe list has a new task digest. It cannot resume
an old-order checkpoint. The candidate-count metadata records the exact order.
All inherited oracle controls, term/rank/cache/database bounds, atomic updates
and immutable source checks remain. Expected peak remains0.4–0.8 GiB RSS;
sorting at most30,000 small recipe references adds under a few MiB. Runtime
improvement is unknown until measured.

The frozen `hi_cft_20260923_c8two_n5_primitive_exact.py` consumes these artifacts
without changes: recipes and source schema are identical, and the complete
source graph includes the ordering wrapper. It recomputes prime support,
reconstructs ordinary and projected vectors and checks full exact residuals.

Suggested root payload, within the guarded launcher:

```text
python hi_cft_20260923_c8two_n5_primitive_priority.py --weight 0,2 --output NEW_priority.json --seconds 300
```

No `--order` option is exposed: this new wrapper's ordering policy is fixed and
explicit. Only syntax checks have been run by the implementing agent.
