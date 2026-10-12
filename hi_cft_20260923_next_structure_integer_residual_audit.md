# Independent integer residual continuation audit

Read-only source audit completed on 2026-09-23, before the root-coordinated
continuation. No numerical job was run by the auditor.

Reviewed sources:

- `hi_cft_20260923_next_integer_residual.py`, SHA256
  `782538a65c4a5ef3c9553a6463089a8dbf9b85d205e5a9ad2ca4d0ae100ee5e3`;
- `hi_cft_20260923_next_h4_integer_cached_v2.py`, SHA256
  `663ca02887cf23cfaf6bde151b6f917d4290c2abec7a0623db4a5bb47211736e`;
- the new resource note, the frozen cached wrapper, H4 consumer, and native
  FLINT interface used by these sources.

The independent review passes. Clearing a column denominator D_j and relation
coefficient denominator C_j, then multiplying by
L=lcm(D_target,C_j D_j), gives exactly the original full sparse residual.
All four products in Q(sqrt(13),sqrt(-3)) have the correct signs and factors.
Only genuinely nonzero residual coordinates are converted back to rational
field elements. The Fraction-based conversion avoids Python's decimal digit
limit in this conversion step.

The sixteen synthetic systems exercise all field components, rational
denominators, cancellation, nonzero residuals, and cached-column reuse. The
first actual relation is compared to the original rational implementation;
a nonzero perturbation is independently checked by both implementations.
These are meaningful runtime prerequisites, not results inferred from this
source audit.

The source graph retains the previous exact action-cache policy without
rewriting its meaning. A separate policy binds both new sources, all files
of the closed cached ancestor, and the effective batch. Existing exact
relations remain unchanged. Per-block source checks and full exact sparse
residual acceptance remain in force.

The native interface explicitly accepts at most 64 right-hand sides, so the
new maximum of 32 is within its reviewed interface. The target-width guard,
96 MiB cleared-record preflight, bounded caches, 1400 MiB boundary check,
and hard 3 GiB address-space limit remain applicable. The accumulator can
briefly contain more than 20,000 states during one column subtraction before
its boundary check; the exceptional maximum is the union of two capped
20,000-state vectors. Thus its advertised 20,000-state allocation estimate
is not a strict instantaneous RSS bound. The hard address-space limit is the
allocation backstop, and this caveat does not alter exact acceptance.

This audit authorizes no independent launch and proves no new H4 identities.
Root owns the single numerical slot and must read the runtime control and
full-residual results before extending the mathematical certificate.
