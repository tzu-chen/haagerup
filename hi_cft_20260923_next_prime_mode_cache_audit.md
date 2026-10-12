# Independent audit of the bounded composite mode cache

23 September 2026. Source review only; no execution. Reviewed
[prime_mode_cache](hi_cft_20260923_next_prime_mode_cache.py) and
[n4_union_cached_v2](hi_cft_20260923_next_n4_union_cached_v2.py).

For a fixed left field a and mode n, the VOA action a_n is linear
in its right input. Computing it on each right basis state and summing
with finite-field coefficients is therefore identical to the original
mode routine. The helper is explicitly restricted to the installed
prime-field representation. Left fields are the ten authenticated,
unchanged operator dictionaries: strong references prevent Python ID
reuse, and snapshots isolate the oracle input. These facts make the
identity/mode/state key valid within the caller's immutability contract.
Plain integer modular outputs are compatible with the old checker.

The cache caps both300000 retained terms and50000 entries; thus empty
actions cannot defeat the term bound. The single-action50000-term
cap,256 registered-left limit and the caller's fixed ten operators
bound the remaining cached structures. As usual the single output
is computed before its cap check, so the hard launcher remains required.
The additional cache is consistent with the retained3GiB address cap
and the existing768MiB RSS stop at completed-target boundaries.

The wrapper migrates a closed checker database to a new path. It
checks the ancestor's source bindings, cursor/row count, and zero
residual prefix. It leaves the old Checker's source_sha256 unchanged;
new wrapper/helper hashes and ancestor hashes are recorded separately.
This is correct because the inherited Checker's __file__ still names
the original checker. The source database is rehashed after copying,
and resume checks the new ancestry. No prior artifact is overwritten.

Before replacing x.mode, ten whole-vector comparisons against the
original routine use five distinct left fields and right-vector scales
one and seven, explicitly exercising cache hits and scalar linearity.
The same source-bound target loop and full int64 block residual checks
then run unchanged. These controls preserve the previous scope:
finite-prime membership only, without characteristic-zero containment
or a properness claim. No blocker was found in the source review.
