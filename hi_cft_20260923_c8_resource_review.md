# Constructive c=8 continuation

23 September 2026. The low-energy candidates suggested directly by the
chain data have already been tested in the linked earlier reports. No new
high-confidence short list was found. This continuation targets an actual
subalgebra of B=V_(E6+A2), rather than adding candidate exclusions.

The first new computation constructs the weight-zero, one and two spaces
of this lattice VOA, with dimensions 1,86,1370. Lattice momenta through
norm four and oscillator monomials are explicit. Sparse current-mode
matrices, their products on small highest-weight spaces, and small SVDs
are used; no many-body lattice diagonalization runs.

Estimate: fewer than two million sparse entries and a bounded cache of
current actions, below 0.3 GiB RSS including Python, NumPy/SciPy and
temporary copies. Use a 2 GiB address cap, the permanent 8 GiB group
watchdog, 32 GiB host reserve, two threads/CPUs and one numerical job.
Every run uses hi_cft_safe_run.py. The initial MemAvailable was 46.7 GiB.
The launcher checks actual memory and cgroup limits at launch. Computation
has a 600-second alarm; increasing grades requires a new allocation review.

The immediate constructive target is to locate the prescribed weight-two
Haagerup fields inside the ambient multiplicity spaces and check their
OPE products. A low-grade match alone will not establish a VOA or a
Haagerup defect action. Prior certificates and tracked files are retained.

The next construction step uses a 232-dimensional candidate field space
inside the 1370-dimensional ambient grade, and nine current matrices on
that space. Their dense complex storage is below 8 MiB. The selected
120-dimensional frame depends on nine real angles. A full residual and
its analytic nine-column Jacobian use below 25 MiB; allow solver copies,
sparse modes, caches and library workspaces for a total RSS estimate
below 0.5 GiB. The same 2 GiB address cap and 600-second alarm apply.
Only this one numerical job runs. This is a constructive numerical
search; failure to find a solution is not an exclusion.

The OPE verification streams one 1370-by-1370 sparse mode matrix at a time
and multiplies it into a 1370-by-120 frame (2.6 MiB). It retains no ambient
three-index tensor. Allow 0.7 GiB RSS including the bounded vertex cache,
sparse assembly lists, temporary copies and workspaces. The 2 GiB address
cap, permanent watchdog/reserve and a 600-second alarm remain in force.

Exact verification uses sparse dictionaries over Q(sqrt(13),sqrt(-3)),
through grade two only. The scalar-mode cache is bounded at 12000 entries;
the 120 field vectors are reduced in separate Cartan-weight blocks. No
1370-cubed tensor or symbolic dense matrix is allocated. Budget 0.8 GiB
RSS for rational coefficients, caches, workspaces and temporary products,
under the same 2 GiB address cap, watchdog/reserve, and 600-second alarm.

Grade three is a separate bounded numerical check. Enumerate lattice
momenta through norm six first, and refuse an ambient grade above 20000.
Stream 120-column mode images (at most 38.4 MiB complex storage) into
separate Cartan-weight blocks; retain at most 1600 independent vectors.
Never allocate the full product tensor or all pair images. Allow 1 GiB
RSS including sparse current matrices, caches, QR workspaces and copies,
with the same 2 GiB address cap and a 600-second alarm.

The exact grade-three span uses the same sparse oscillator formulas and
Cartan blocks, with a 1600-vector stop. It first runs modulo a split prime
and can then run over the degree-four number field. Retained vectors and
two bounded 12000-entry scalar caches are budgeted below 1 GiB RSS;
coefficient growth remains guarded by the 2 GiB address cap, 8 GiB group
watchdog and 600-second alarm. Only one such run is permitted at a time.
