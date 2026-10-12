# Targeted exact weight-four continuation

New producer `hi_cft_20260923_c8two_targeted_h4.py` reads a separately
source-bound saturation request's `additional_tests` list and proves only
those exact A0P3 identities. It writes a new output directory and never
imports, modifies or relabels the old bulk records. Completion explicitly
means the requested subset; the original full-block count is retained.
The independent saturation theorem and seed records are still required
to infer the entire gate.

It reuses the frozen exact mode cache, integer-cleared complete residual
engine, rational regular-representation FLINT solver, and their synthetic,
actual-oracle and perturbed-target controls. Policy hashes bind this new
source, all adapters, the requested JSON and the original full block plan.
Resume requires identical policy. Every requested target must be an actual
saved P3 input for operator 0 through 8 in a reviewed nonzero Cartan block.

At most 16 targets are batched (default 8), each with at most 3,078 terms
and 2,048-bit field coefficients. Exact relations retain the 4,096-bit
bound. Selected block ranks are at most 300 (actual maximum 280). A new
native preflight uses the actual matrix coefficient height and refuses
an estimated workspace above 512 MiB. The rational matrix dimension is
four times the field rank. This estimate is conservative preflight, not
a claim about all internal FLINT allocation; hard AS remains the backstop.

Retained caches are 192 MiB exact actions, 128 MiB reconstructed vectors,
64 MiB integer columns, totaling 384 MiB estimated storage. Targets,
pivot matrix, one active cleared column, integer residual accumulator,
state tables, Python and serialization coexist. Existing vector/height,
96 MiB cleared-record and 512 MiB integer-accumulator checks remain.
Expected total peak is roughly 0.7–1.1 GiB RSS for measured coefficient
heights, with the unchanged 1,400 MiB internal boundary and 3 GiB hard
address cap. Stop and redesign on a cap; do not raise it.

Root alone may launch after independent review and confirmation that the
numerical slot is free. Use the normal safe launcher, a bounded internal
timer no greater than 900 seconds, and an external timeout with a short
kill-after backstop for native calls. Permanent 8 GiB group RSS, 32 GiB
host reserve, two threads/CPUs, and one-job restrictions apply. Preparation
so far was editing and syntax compilation only.
