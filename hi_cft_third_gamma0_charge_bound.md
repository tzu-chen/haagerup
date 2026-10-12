# A bounded charge test for the gamma0 A1-plus-three-torus branch

15 September2026. Source prepared for ROOT's guarded exact slot; no
execution by this agent. The modular trace identities are those in
the independently audited flavoured-character calculation.

Suppose W1=A1_k plus a three-dimensional abelian radical. In the
gamma0 character the c1,d1,d4 ground dimensions are3,7,5 and their
weights are1/3,6/13,5/13. For a finite SU2 irrep of dimension n,
the Dynkin index in long-root normalization is n(n²-1)/6.
The positive trace identity gives

    4+9 t_c1+t_d1+3 t_d4=4k.

The maximal indices in those dimensions are4,56,20, giving k<=39.
There are only3,15,7 integer partitions of the three dimensions,
so every level needs at most315 partition triples.

Choose orthonormal Hermitian radical currents, so their current
form kappa is the3-by-3 identity. The same modular identity becomes

    9 Q_c1+Q_d1+3 Q_d4=4 I_3.                        (1)

Every SU2 isotypic multiplicity space is a representation of the
commuting radical. Selfcontragredience pairs each nonzero charge q
with -q inside the same SU2 irrep. An irrep of dimension n occurring
m times therefore supplies at most floor(m/2) charge-pair directions.
The sum of these counts across the three grounds must be at least3.
This rank condition and the index equation use only finite
representation theory and selfcontragredience; they do not use
coset energy or a Frobenius–Schur sign.

For the following stronger test assume in addition that the
irreducible modules are unitary, or explicitly that the joint
affine/Heisenberg commutant energy is nonnegative. A charge q on
an SU2 irrep of dimension n in a ground of weight h obeys

    |q|²/2 <= h-(n²-1)/(4(k+2)).                     (2)

The integrable affine label also requires n<=k+1. A charge pair
contributes2n qq^t to its ground trace. With modular coefficient
w=9,1,3, its maximum contribution to the trace of(1) is consequently

    4 w n [h-(n²-1)/(4(k+2))].                      (3)

Summing(3) over every possible paired copy gives an upper bound;
it must be at least Tr(4I_3)=12. At least three pairs must have
strictly positive available energy. These tests are necessary only:
they do not require the charge vectors to exist in a common lattice
or prove that their covariance matrices can satisfy(1).

The helper records trace-only, trace-plus-rank, and energy-capacity
survivors separately. It deliberately permits every finite SU2
partition before imposing the stated conditions; no real versus
quaternionic restriction is needed for an upper bound.

## Source and allocation envelope

`hi_cft_third_gamma0_charge_bound.py` uses only the standard library.
At most39*315 partition triples are considered, each containing at
most15 one-dimensional summands in total. Exact Fraction arithmetic
has small fixed denominators, and output stores only feasible
witnesses and per-level counts. A conservative64MiB total process
estimate is below the128MiB guard. The helper has a30second alarm,
immutable source hash/recheck, and refuses existing outputs.

ROOT command, only after independent source/algebra review:

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_gamma0_charge_bound.md --audit-json hi_cft_third_gamma0_charge_bound_guard.json -- python hi_cft_third_gamma0_charge_bound.py --output hi_cft_third_gamma0_charge_bound_results.json

An energy-stage exclusion retains the explicit unitary-module
premise in(2). The earlier elementary k<=39 exclusion does not
require this additional premise. Neither conclusion identifies
the physical chain with W or its current coset.
