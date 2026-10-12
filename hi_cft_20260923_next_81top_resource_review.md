# Exact mixed-sector top pilot: resource and proof review

23 September 2026. No numerical or exact run was launched by this agent.
Only syntax compilation was performed. Root owns the sole numerical slot.

Producer: `hi_cft_20260923_next_81top_exact.py`.

## Concrete pilot

    python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 300s python hi_cft_20260923_next_81top_exact.py --sector ++ --seconds 280 --output hi_cft_20260923_next_81top_pp.json

The internal 280-second alarm raises a bounded-stop exception even during
ordinary Python arithmetic. The outer timeout and permanent launcher
provide independent enforcement. The permanent 8 GiB group RSS watchdog,
32 GiB host reserve, and two-CPU/thread policy remain unchanged. No worker
process, dense commutant matrix, NumPy, SymPy, or ambient oscillator basis
is used. The other single-sector selectors are `+-`, `-+`, and `--`;
`--sector=--` avoids command-line ambiguity. `all` processes four sectors
sequentially inside the same time limit.

## Allocation estimate before a run

Each sector has 81 root states. There are 15 original operators (six
currents, eight certified primary fields, one certified stress) and their
explicit PCT adjoints, stored as sparse 81-column dictionaries. The total
saved operator cap is 100,000 nonzero entries, coefficients at most 2048
bits per numerator/denominator. At that deliberately pessimistic cap,
coefficient tuples, Fractions, integers, and dictionary slots consume
approximately 0.2 GiB. The expected count is much lower because each
operator has one Cartan weight shift. New operator pairs add at most
13,122 entries before the global cap check, below another 0.03 GiB.

The cyclic span holds at most 81 rows, each within a single Cartan weight
block; even treating every row as dense adds fewer than 6,561 entries.
Its reduction recipes, JSON output construction, and input JSON
deserialization add conservatively 0.04 GiB. The source JSON is 157 KiB.
Bounded dot/coordinate/gauge caches, field copies, Python runtime, and
temporary Fraction arithmetic add conservatively 0.1 GiB. One completed
sector's small row/provenance record persists when the next sector starts;
previous matrices are released as the local variable is rebound. Target
peak RSS is below 0.5 GiB (normally below 0.15 GiB), well inside the 2 GiB
hard address-space cap. These are allocation estimates, not measurements.

The first-sector time estimate is 30–180 seconds; the hard pilot determines
actual time. No extrapolation justifies exceeding the 300-second pilot.
Output is atomically replaced after each completed sector and on a handled
stop. A killed partial sector is not reported as a completed certificate.

## What a success proves

The E8 overlattice cocycle is built from exact rational Gram matrices and
gauge-matched to the old E6+A2 cocycle. Both isotropic glue lines and both
nonzero cosets are supported. Within one coset the pulled-back positive
Hermitian metric is rational after choosing a common normalization. Each
generator matrix's weighted adjoint is checked exactly against the
matrix of its PCT adjoint, another certified U-field. Thus the tested
associative operator algebra is closed under adjoints.

A chosen joint Cartan eigenspace has dimension one. If its vector is
cyclic, any invariant orthogonal decomposition would put that entire
eigenline in a single summand; cyclicity then forces that summand to be
the entire 81-dimensional space. This proves irreducibility. Cyclicity
alone would not suffice without the unique-eigenline and adjoint facts.
Every accepted cyclic row records its parent operator word, reductions,
normalization, and exact coefficients for replay. Operators have exact
content hashes and the source/certificate hashes are recorded.

The result is a top-space statement. Conditional on the independently
proved bound h<2 for every simple U-module, a mixed lattice sector starts
at h=1 and has no possible later U top; then an irreducible 81-dimensional
top proves that its whole U restriction is simple. The two E8 glue
restrictions are dual, but can be isomorphic to each other.
