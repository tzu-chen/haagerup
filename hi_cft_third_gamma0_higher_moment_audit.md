# Eighth, tenth and twelfth current moments

These certificates use the actual E8 embedding and the now-exhaustive
unique finite representations of all eleven nonvacuum grounds and
W2. No arbitrary support witness is used to determine a higher moment.
They test necessary Jacobi constraints; passing does not construct W.

## Generic normalized Gaussian completion

For even a,b define

\[
R_{ab}=\operatorname{Tr}(h_L^a h_R^b)/2^{(a+b)/2}.
\]

At total degree d=a+b, the completed weight-d form is

\[
H_{ab}=\sum_{i=0}^{a/2}\sum_{j=0}^{b/2}
\frac{a!b!}{(a-2i)!(b-2j)!i!j!}
\left(-\frac{kE_2}{24}\right)^i
\left(-\frac{lE_2}{24}\right)^j R_{a-2i,b-2j}.
\]

This is the Taylor coefficient of the Jacobi Gaussian with normalized
charges h/sqrt2. The degree-eight source checks the generic formula
against the separately audited pure/mixed quartic and sixth formulas.
All finite moments are computed directly from the literal SU2 weights.

Only the scalar R00 has a vacuum pole. If r=i+j, the preceding-current
contribution to the next coefficient is `-24r` times its moment; the
scalar polar contribution at the second next coefficient is
`-72r+288r(r-1)`. The code includes both terms. These are coefficients
of E2^r, with no continuum or large-grade approximation.

Let P_j=D_(2j-2)...D_2D_0 chi. Independent Serre convolutions give the
following vacuum polar, weight-one and weight-two coefficients:

| Degree | Polar | Weight one | Weight two |
|---|---:|---:|---:|
|8|5/54|-29/27|4598/9|
|10|-5/54|40/27|13450/27|
|12|35/324|-170/81|35575/81|

For each polarization, divide its scalar Gaussian polar coefficient
by the corresponding entry in the second column to obtain the exact
particular multiple of P_j. The remainder is holomorphic.

## Complete holomorphic spaces

Write Bi=B(984) and Bw=B(-744), with the same fundamental matrix Xi
and exponent convention as the preceding certificates.

* Degree8: `(Delta/E4)Xi v`, with
  `(Bw-576I)(Bw-1152I)v=0`. The space has dimension9;
  its next coefficient is `(chi_matrix-264I)v`.
* Degree10: `E4*M6` direct sum `E6*M4`, of dimension6+3=9.
  Its next scalar shifts are respectively+720 and-1008.
* Degree12: `Delta*Xi v` for an arbitrary twelve-vector v.
  Its next coefficient is `(chi_matrix-24I)v`.

For degree10, evaluate a holomorphic form at the order-three elliptic
point, where E4 vanishes and E6 is nonzero. The E6*M4 summand spans
exactly the allowed three-dimensional value space. Subtract the
matching form; the difference can be divided by E4 to give a
holomorphic M6 form. The same M4 value map is injective, so the sum
is direct. This proves completeness, rather than merely constructing
nine candidate forms. Degree12 follows directly by division by
Delta and the single-principal-part property of Xi. The exact
certificate also checks independence of every chosen leading basis.

## Exact tests and provenance

For every even polarization, impose all twelve leading ground/current
coefficients, then the independent vacuum weight-two coefficient.
The output distinguishes a failure among the ground rows from an
additional failure introduced by W2. The complete rational solution
and any remaining freedom are preserved. The degree10 implementation
uses nine variables plus three explicitly zero padding coordinates
to reuse the audited twelve-column RREF; the degree12 system uses
all twelve coordinates.

`hi_cft_third_gamma0_eighth_check.py` completed successfully under
ROOT's launcher at22:34:36UTC: both pairs passed all five degree-eight
polarizations. Its result is `hi_cft_third_gamma0_eighth_results.json`.
This adds no exclusion. The separate degree10/12 source is
`hi_cft_third_gamma0_higher_moments.py`.

ROOT executed the degree10/12 certificate successfully at22:40:11UTC
in `hi_cft_third_gamma0_higher_moments_results.json`. Every
polarization passed for both pairs. The complete current-moment tests
through degree12 therefore supply no further exclusion. This is a
precise limit of these fixed-ground and weight-two constraints;
it does not establish all-order Jacobi consistency or existence.

Both readers bind the exhaustive support record, the sixth-moment
record, their bounded JSON ancestry and frozen producer source hashes.
They recheck the lower moments and orbit conditions of every
representation. Inputs are at most2MiB apiece, sources at most128KiB.
Only small exact rational systems are live; no support enumeration,
tensor array or numerical eigensolver is involved. The reviewed guard
is128MiB address space and a thirty-second alarm. The author has
executed no numerical job. No degree14 completeness or exclusion
claim is made.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_higher_moments.py --support hi_cft_third_gamma0_orbit_sixth_ground_results.json --sixth hi_cft_third_gamma0_sixth_results.json --output hi_cft_third_gamma0_higher_moments_results.json
```
