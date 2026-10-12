# A smaller sufficient set of grade-four zero-mode targets

This is an algebraic reduction, not a new decomposition certificate or a
computed containment. Let Q=S3/N3 and W4=N4+P4. The exact lower controls imply
A_0 N3 is contained in N4. Assuming the already stated K-stability of S3,N3
and W4, zero product induces a K-equivariant map

    A tensor Q -> B4/W4.

For an sl2 highest vector a of highest weight m and a highest vector p of
highest weight n, the following min(m,n)+1 tensors generate the full tensor
product under diagonal sl2:

    a tensor F^j p,   0 <= j <= min(m,n).

Indeed V_m tensor V_n is the multiplicity-free sum of V_(m+n-2j). The tensor
a tensor F^j p has nonzero projection onto the j-th summand: the usual
highest Clebsch--Gordan vector of that summand has a nonzero coefficient
of a tensor F^j p. Its other components belong to the earlier summands
with indices at most j. Induction, semisimplicity and the previously
generated earlier summands therefore recover every summand. This argument
can equivalently use invariant Hermitian forms on finite-dimensional sl2
modules; it concerns only the finite current Lie algebra.

Apply this separately to the two commuting sl2 factors. If a and p have
highest weights(mL,mR) and(nL,nR), it suffices to certify

    a_0(F_L^i F_R^j p) in W4,
    0 <= i <= min(mL,nL),  0 <= j <= min(mR,nR).

No Clebsch--Gordan target sums are required. A lift of a highest quotient
vector p is enough: its raising-current images may lie in N3 rather than
vanish exactly, because the induced map is defined on Q. An exact orthogonal
complement to N3 is consequently unnecessary.

The actual highest quotient basis still must be certified. In each Cartan
weight, act by both raising currents on the saved S3 rows and reduce modulo
the first634 normal rows. The common kernel yields highest vectors in Q.
Keep independent representatives modulo N3, and certify that their lowering
strings span Q (dimension322). This uses only exact grade-three states and
small weight blocks. A predicted character table alone is insufficient.

For the28-copy predicted table in
`hi_cft_20260923_next_strong_grade3_feasibility.md`, the numbers of tests for
the nine independent A families are:

| A type, dimensions | Copies | Tests per copy |
|---|---:|---:|
| (1,1) | 1 | 28 |
| (1,5) | 1 | 130 |
| (1,9) | 2 | 200 |
| (1,13) | 1 | 231 |
| (2,2) | 1 | 76 |
| (2,6) | 1 | 206 |
| (2,8) | 1 | 253 |
| (2,14) | 1 | 315 |

Total1639 instead of2898 highest-left/full-right targets. These counts are
conditional on validating the predicted Q decomposition. Dense quotient
highest lifts can make an individual mode more expensive, and extracting
them has a cost. This is a possible follow-up to the running bulk consumer,
not a reason to discard already certified identities or interrupt its job.
