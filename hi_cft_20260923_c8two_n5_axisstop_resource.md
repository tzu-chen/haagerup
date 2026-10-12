# Certified identity-factor skipping for N5

New wrappers `hi_cft_20260923_c8two_n5_axisstop_prime.py` and
`hi_cft_20260923_c8two_n5_axisstop_exact.py` leave every frozen source unchanged.
Both retain the full, source-bound ordered FE factor list in metadata. During
evaluation, if the actual raising action E_axis(v) vanishes, every remaining
factor `(1-F_axis E_axis/lambda)` for that axis acts as identity. Only those
factors are skipped; the other axis is still processed. If v itself is zero,
all remaining factors act as identity. The two current algebras commute, and
factors are ordered LEFT then RIGHT. This argument is exact over both the
pilot field and the original number field; no tolerance or rank heuristic is
used. Final grade/weight assertions, highest checks, ordinary-vector digest,
complete projected specialization and full exact relation residual remain.

The prime wrapper inherits the prioritized primitive candidate order and binds
its new source hash before checkpoint creation. The exact wrapper inherits
primitive recipes and prime-support selection, and binds its implementation
in `axis_stop_exact_extension`. Final certificate aggregation must validate
that nested source graph along with primitive and support extensions. Fresh
output paths are required. The unchanged CLI is inherited from each frozen
parent wrapper. No factor count or denominator is modified, so old and new
prime artifacts have the same mathematical projection convention.

Resource bounds are unchanged: root-only serial guarded jobs,3 GiB AS,
prime1 GiB/exact1400 MiB RSS boundaries,32 GiB host reserve and at most two
CPUs/threads. The optimization adds only a two-element set. All40k-term,
2048-bit vector, rank300,512 MiB native-preflight, cache and database limits
remain. External native timeout is mandatory. Proposed first allowances are
300 seconds prime/external320, and600 seconds exact/external620.

The saved high14 exact run spent68.33 seconds reconstructing columns and only
1.78 seconds afterward; the high12 resumed run spent68.09 seconds reconstructing
and4.73 seconds afterward. Thus repeated mode/projection work is the justified
first optimization. Integer residuals may help later but are not changed here.
No extra complete-projector oracle is required: each skipped factor's identity
is justified by the computed zero raising action itself. Existing original-mode
controls remain. Only syntax checks have been run by the implementing agent.
