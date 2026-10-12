# The weight-four-generator certificate and its small lower controls

23 September2026. Sufficient criterion, not a completed properness proof.
The exact3970 lower relations passed. The canonical P4 controls also
passed: all18 current-zero identities, all6 direct L(1)/L(2) memberships,
and all3 finite-prime quotient replacements. The actual P4 fields have
2313,2363,2313 sparse terms; root's guarded run took12.7907 seconds and
peaked at approximately0.257GiB RSS. The source-bound result is
`hi_cft_20260923_next_structure_p4_controls.json`, whose exact vector
artifact SHA256 is
`c8c3ce8b8ab361fabca3c54c3f77a234029bf9b62858f74b5991dc5ed73c1d4e`.

The modular N4 pilot has rank6007,
and its first three independent new mode-zero directions have Cartan
weights(0,2),(0,0),(0,-2). Modular dimensions alone are not exact upper
bounds and are not used as containment proofs below.

The subsequent diagnostic `hi_cft_20260923_next_structure_p4_positive.json`
passed all90 exact A_n P4 memberships for all ten primitive highest
fields and n=2,3,4, with outputs respectively in S3,S2,K. Its30 A1P4
targets also reduce to zero at the saved split prime against the selected
6010-column span. Those last30 are not exact membership certificates.
The guarded run took163.27 seconds and peaked at279820KiB RSS. No new
lower-space or rank6011 witness was found; this does not replace Gates4
and5 below.

Write S1=K, S2=A, S3=N3(K,A)+P3, with the existing exact provenance
P3 subset A_0 A+N3(K,A). Put

    W4=N4(K,A,P3)+P4.

Choose actual P4 vectors in A_0 S3+N4. The finite sufficient gates are:

1. The already passed lower relations for K,A and S2.
2. K0W4 subset W4, for example by choosing P4 as an actual finite
   K-representation.
3. L(1)P4 subset S3 and L(2)P4 subset S2.
4. Every highest-left A_0 P3 product belongs exactly to W4.
5. Every highest-left A_0 P4 product belongs exactly to

       N5=K_(-1)W4+T W4+S2_(-1)S3.

Under these gates, K+A+P3+P4 strongly generates U and U1=K. Thus the
actual c=8 subVOA is proper. All ambient mode calculations have left
weight at most two, and the largest required output grade is five.

## Avoiding a circular Virasoro argument

Gate3 cannot be omitted merely by writing P4 as A_0 P3. The formula
L(1)(a_0 p)=2a_1p+a_0L(1)p would then invoke the as-yet-unproved
containment a_1P3 subset S3. Instead directly verify Gate3 on the few
chosen P4 vectors. For a three-dimensional P4 this is six small
calculations with outputs in the already certified grades two and three.

The previous lower relations give L(1)N4 subset S3 and L(2)N4 subset S2.
Gate3 therefore gives the same inclusions for W4. Gate4 and these
inclusions imply, for quasiprimary primitive a in S2,

    2a_1p=L(1)(a_0p)-a_0L(1)p            in S3,
     a_2p=L(1)(a_1p)-a_1L(1)p            in S2,
    2a_3p=L(2)(a_1p)-a_1L(2)p            in K,

for p in P3; a_4p is scalar. Thus all A-with-P3 singular products are
now controlled. Affine normal left fields follow by Wick expansion.

Current commutators on P4 subset A_0 S3+N4 then give K1P4 subset S3:

    k_1(a_0p)=(k_0a)_1p+(k_1a)_0p+a_0(k_1p).

All three terms use relations already established at this point. Gate2
gives zero-current covariance. Higher current modes follow successively
from [L(1),k_n]=-n k_(n+1), or directly from the same mode commutator.

These facts imply

    L(1)N5 subset W4,    L(2)N5 subset S3.

Check on the three displayed seed types. The only nontrivial new terms
are a_0S3 in the L(1) image of a_(-1)S3 and a_1S3 in its L(2) image;
Gate4 and the preceding paragraph supply both. The central scalar
L(2)a term also lies in S3.

Gate5 now yields, for p in P4,

    2a_1p=L(1)(a_0p)-a_0L(1)p            in W4,
     a_2p=L(1)(a_1p)-a_1L(1)p            in S3,
    2a_3p=L(2)(a_1p)-a_1L(2)p            in S2,
     a_4p=L(2)(a_2p)-a_2L(2)p            in K.

The product a_5p is scalar. Consequently all K/A-with-generator singular
products close. The recursive criterion proved in
`hi_cft_20260923_next_structure_recursive_strong_certificate.md` supplies
all remaining pairs, including P4-with-P4, without a left-weight-four
mode engine or ambient grade-seven calculation.

## An exact right triplet can replace the raw modular lifts

The first extra is the genuine vector w=a^(0)_0 r3_000705, with Cartan
weight(0,2). Its nontrivial K-normal components need not vanish, so the
three raw modular extras should not be assumed to form an actual K-module.
Instead project w to left spin0 and right spin1, then lower twice.

For each sl2 use the Casimir

    C=H0²/2+E0F0+F0E0.

On weight0, C=2F0E0; on weight2, C=4+2F0E0. At ambient grade4, lattice
momentum norm is at most8. Since the two Cartan vectors have squared
norms2 and78, their highest weights are at most4 and24 respectively.
Only even highest weights contribute at weights0 or2. Thus finite exact
projectors are

    P_left0 = product_(l=1,2) [1-F_left0 E_left0/(l(l+1))],
    P_right1 = product_(l=2,...,12)
                  [1-F_right0 E_right0/(l(l+1)-2)].

Let v=P_left0 P_right1 w and take P4=span(v,F_right0 v,F_right0² v).
Nonzero v gives the actual K-type(1,3); all18 current-zero-mode identities
can be directly verified. Its provenance remains A_0S3+N4 because current
zero modes are derivations, S2/S3 are K-stable, and A_0N3 subset N4.

Using these projected vectors does not assume they span a characteristic-
zero quotient of dimension three. Gates4 and5 are still exact identity
tests. They will fail if the selected generator list is insufficient.
This is why no modular upper-rank inference is required.

Here N4 and N5 denote the full differential normal spans in the stated
generators. A computational solver may use any source-bound subset of
their actual normal words. An exact identity in that subset is already
an identity in the full span. The proof consequently needs no claim
that the6007 selected normal columns exhaust characteristic-zero N4.
If the finite gates establish properness, the separately proved character
uniqueness then supplies dim U4=6010. The6007 selected columns together
with P4 would then be a basis of U4. This still would not, by itself,
fix the dimension of the full normal span N4 or prove the chosen P4
generators minimal: unselected normal words could add directions not
visible in their reductions at the chosen prime.

## One neutral zero-mode family is redundant

The two primitive neutral weight-two fields used by the producers sum to
omega-Sug(K_left)-Sug(K_right). Only one therefore needs an independent
zero-mode containment test at each gate. The omega zero mode is T. A
Sugawara zero mode is a finite sum of negative current modes applied to
known nonnegative current modes of the input; commuting a current zero
mode across a creation operator only adds another current creation term.
Every summand is consequently a differential normal word of the required
weight.

For P3 these current-mode containments are available before Gate4. For P4
they are available after Gate4 and the direct Virasoro controls, as proved
above, and hence before Gate5. This order avoids using the proposed
neutral reduction to establish its own prerequisites. With the charged
Clebsch--Gordan highest targets, this reduces the grade-five test list
from25 to24 highest vectors. It is an optional reduction of the exact
certificate, not a change to the frozen control producer.
