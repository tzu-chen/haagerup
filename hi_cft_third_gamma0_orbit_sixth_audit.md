# Exact affine-orbit and sixth-moment ground support

The new `hi_cft_third_gamma0_orbit_sixth_ground.py` retains every
finite ground representation compatible with the fixed quadratic,
quartic and sixth moments and the forced affine simple-current
extension. It leaves all previous producers unchanged.

## The additional orbit constraint

The retained bosonic extension H+ pairs an integrable affine label
`(ell_a,ell_b)` with `(k-ell_a,l-ell_b)`. Its intertwiner is invertible,
so the two labels have the same multiplicity space. For a physical
module-ground highest vector with finite irrep dimensions `(n,m)`,
the partner's full conformal weight differs by

\[
\Delta=\frac{k+l}{4}-\frac{n+m-2}{2}.
\]

The physical module has no states below its ground. Hence Delta is
nonnegative. If it is zero, the two finite ground multiplicities
are equal. Thus the certificate imposes

* n+m even, individually for each irrep;
* n+m<=22 at `(1,39)` and n+m<=10 at `(3,13)`;
* equal multiplicities of `(n,m)` and `(k+2-n,l+2-m)` at equality.

This uses rationality of the positive-level bosonic affine extension
and ordinary module restriction. It does not require rationality of
the complementary commutant or nonnegative complementary energy in
all W modules. The module's own lower-bounded grading is sufficient.
ROOT and Constraints independently checked this argument.

## Exhaustive reduction

The ten target moments are dimension, left/right quadratic indices,
mixed quartic, twice left/right pure fourth, four times left pure
sixth, twice each mixed sixth, and four times right pure sixth.
All coordinates are integral for finite SU2 times SU2 representations.
Any negative or nonintegral target is refused directly.

For left level one the left multiplicity dimensions are fixed by
`a2=T_left`, `a1=d-2T_left`, with the additional identities
`2S_left=4U_left=T_left`. For level three, they are uniquely fixed by

\[
a_4=\frac{4U_L-5(2S_L)+4T_L}{360},\qquad
a_3=\frac{2S_L-T_L}{12}-6a_4,
\]

followed by `a2=T_left-4a3-10a4` and
`a1=d-2a2-3a3-4a4`. Nonnegative integrality and even `a_n` for even n
are necessary. The finite sixth identity follows directly from the
four left-irrep moment columns for n1 through4; no fitted coefficient
or approximate comparison is used.

Each fixed block enumerates every allowed right partition. It records
its right index, twice fourth, four times sixth, and its multiplicity
at the zero-shift boundary. The n=1 hash retains **all** partitions
with equal recorded values. Including the boundary multiplicity is
essential: equal moments alone do not ensure the same orbit partner.

At level three, once block4 is chosen the mixed quadratic and first
mixed sixth moments determine the required indices of blocks3 and2.
The other mixed sixth moment then fixes block2's fourth moment.
Only these matching hash buckets are combined. Each completed
representation is rechecked against all ten moments and every
zero-shift orbit multiplicity. This avoids a broad Cartesian search
without dropping any possible representation.

The output gives `support_count`, `unique_support` and
`all_support_witnesses` for each ground. There is no first-witness
shortcut. Refusal or uniqueness is reported only after exhaustive
completion within the stated finite domain. The a/c0 records can
reuse an identical target while preserving their separate module names.

## Controls, provenance and liveness

Controls include the known local d5 representations at both pairs,
the valid boundary pair `(1,9)+(4,6)` at `(3,13)`, refusal of its
unmatched `(4,6)` half, and refusal of a negative-shift `(1,23)`
ground at `(1,39)`.

The script binds the quartic and sixth outputs, all three sixth-input
ancestors and their source hashes. The supplied quartic must be the
one bound by the sixth certificate. All inputs are at most2MiB each;
sources are at most128KiB. The reviewed profile is128MiB address
space and a sixty-second alarm. One ground's partition arrays are
live at a time and are released before later grounds and final JSON
encoding. At most four lists of10000 bounded partitions coexist;
outputs retain at most2000 representations per pair. DFS and join
visits are capped at one million per ground and are not stored as
search history. Every resource-cap failure aborts and certifies
neither exclusion nor uniqueness.

Passing supports the necessary finite representation constraints.
It does not prove the required intertwiners, OPE closure or VOA
existence. The author has run no numerical job.

ROOT executed the complete certificate successfully at22:30:23UTC.
Both pairs passed, and **each of all eleven nonvacuum module grounds
has exactly one feasible finite representation** in this relaxation.
The record is `hi_cft_third_gamma0_orbit_sixth_ground_results.json`.
Consequently higher finite Cartan moments of these grounds are fixed;
the separate eighth-moment certificate can test them without selecting
an arbitrary witness.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_orbit_sixth_ground.py --quartic hi_cft_third_gamma0_quartic_results.json --sixth hi_cft_third_gamma0_sixth_results.json --output hi_cft_third_gamma0_orbit_sixth_ground_results.json
```
