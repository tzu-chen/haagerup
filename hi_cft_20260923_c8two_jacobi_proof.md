# A grade-five closure proof from lower-grade data

This is a sufficient algebraic proof, pending the source-bound checks named
below. It does not treat an unfinished numerical checkpoint as a certificate.

Use the actual spaces K, S2, S3=N3+P3 and W4=N4+P4 from the finite
strong-generation criterion. Assume Gate4, all its previously certified
lower controls, and the actual current triplet P4. Set

    Q = W4/N4,       N5 = K(-1)W4 + T W4 + S2(-1)S3.

All normal spaces here are the full formal spaces. Selected computational
columns need only belong to them. If P4 is contained in N4, the H=3
strong-generation criterion already proves properness. Otherwise the
irreducible current type of P4 shows Q is exactly the type (0,2), with
basis q_minus, q_zero, q_plus. No characteristic-zero upper rank for a
selected list of normal words is required for this dichotomy.

For a in S2 and p in S3, write beta(a,p)=[a_0 p] in Q. Gate4 makes this
well defined. Define F(a,q)=[a_0 q] modulo N5, using a P4 representative.
The zero-mode derivation identity and Gate4 give S2_0 N4 contained in N5,
so this definition is independent of the representative. Both maps are
equivariant for the two current Lie algebras.

## The two normal-space facts used by Jacobi

The inclusion S2_0 N4 contained in N5 follows by the zero-mode derivation
on K(-1)S3, T S3 and S2(-1)S2, followed by skew reordering. The needed
singular products are precisely the lower controls and Gate4.

Also N3_0 S3 is contained in N5. Write N3=K(-1)S2+T S2. Translation
has (Ta)_0=0. For a current x, a in S2 and p in S3, the iterate formula is

    (x(-1)a)_0 p = sum_(i>=0) x(-1-i) a_i p
                    + sum_(i>=0) a(-1-i) x_i p.

Gate4 and the lower controls put all inner products into W4, S3, S2, K
or the vacuum at the appropriate weight. Repeated translation identities
express the resulting terms in N5. This does not use any unproved
P3-with-P3 product or any grade-five closure assumption.

Consequently, if a_0 b belongs to N3, Jacobi implies

    F(a,beta(b,p)) = F(b,beta(a,p)).                         (J)

The equality follows from [a_0,b_0]=(a_0 b)_0 and the preceding normal-space
facts. This is the only Jacobi reduction needed below.

## Charged fields

The highest weights of the eight charged primitive fields a0,...,a7 are

    (0,4), (0,8), (0,8), (0,12),
    (1,1), (1,5), (1,7), (1,13).

Two existing exact H4 identities have nonzero P4-minus coefficients:

    beta(a3, r3_000910) = c3 q_minus,   c3 != 0,
    beta(a6, r3_000899) = c6 q_minus,   c6 != 0.

Their right-input weights are respectively (0,-14) and (-1,-9).
These statements must be authenticated against the closed exact relation
records, their original normal columns and the canonical P4 source.

Only the bottom witnesses are used in Jacobi. Once F(a,q_minus)=0 is
proved, the highestness of a and current stability of N5 let the right
raising current give F(a,q_zero)=F(a,q_plus)=0 directly.

For b=a3, use a=a0,a1,a2,a5,a6,a7. For b=a6, use a=a3,a4. The exact
current-module decomposition of S3/N3 has no highest types equal to the
corresponding sums:

| b | a | Sum of highest weights |
|---|---|---|
| a3 | a0 | (0,16) |
| a3 | a1,a2 | (0,20) |
| a3 | a5 | (1,17) |
| a3 | a6 | (1,19) |
| a3 | a7 | (1,25) |
| a6 | a3 | (1,19) |
| a6 | a4 | (2,8) |

The zero product of two highest vectors is highest. Thus absence of these
highest types, rather than absence of the corresponding Cartan weight,
gives a_0 b in N3. This distinction matters for (0,16).

For every displayed pair at the bottom witness, the weight of a_0 p is
outside the three weights of Q. Hence beta(a,p)=0. Equation (J) and the
nonzero coefficient of beta(b,p) give F(a,q_minus)=0. Raise this resulting
zero identity, keeping a highest, to obtain the other two right inputs.
The off-weight argument need not hold on raised p and is not used there.
Current covariance then supplies all descendants of each a. These two witnesses therefore discharge every
charged grade-five family, including all its Clebsch--Gordan channels.

The witness reader must verify the two coefficients and source graphs;
the known exact weight dimensions of S3/N3 verify the absent highest types.

## Neutral field

Let C be the span of the charged S2 current modules. Suppose the image of

    C tensor C -> S3/N3,       x tensor y |-> [x_0 y]

is all of the known 322-dimensional quotient. A full rank-322 witness at
a good split prime proves this positive spanning assertion in characteristic
zero: every displayed column is the specialization of an actual vector
in that already known exact quotient. No unknown ambient rank is inferred.
Current closure of the displayed columns must itself be source-bound.

For the retained neutral singlet e and b=a3, this spanning assertion gives

    e_0 b = sum_i t_i (x_i)_0 y_i + n,

where x_i,y_i belong to C and n belongs to N3. Apply zero modes to the
right input p of the nonzero a3 bottom witness. Jacobi and the completed
charged families give

    (e_0 b)_0 p = sum_i t_i [(x_i)_0,(y_i)_0]p + n_0 p in N5.

Here Gate4 places each inner charged product in W4; the charged closure
and S2_0 N4 inclusion place its next product in N5. The N3 term is covered
by the normal-space lemma. A second application of Jacobi now gives

    e_0(b_0 p) = b_0(e_0 p) + (e_0 b)_0 p in N5.

Since b_0 p has a nonzero P4-minus coefficient modulo N4, this proves
e_0 P4_minus in N5. Neutral current covariance gives the whole triplet.
The other neutral field follows from the already audited total-stress
minus Sugawara identity. Thus Gate5 is complete.

## What must be checked before invoking the conclusion

1. All Gate4 identities, combined with the independent raising certificate.
2. The two exact nonzero bottom coefficients and the absent highest types.
3. The exact-quotient charged-bracket spanning witness of rank 322.

If these checks pass, the existing recursive strong-generation theorem
gives U1=K and U proper in B. The conditional-identification theorem then
applies. This note does not assert that the checks have already passed.
