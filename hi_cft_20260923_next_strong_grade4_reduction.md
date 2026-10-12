# A weight-four certificate can imply strong generation through weight three

23 September 2026. New algebraic reduction; independently audited by
structure_routes. It is a sufficient criterion, not a claim that its
remaining exact identities have passed. No numerical job was run here.

Let K, A, P be finite homogeneous spaces of weights 1, 2, 3 in a
nonnegatively graded VOA. Let N be their differential normal-product
span, initially allowing every parenthesization. Assume all singular
products between K,A,P except P with P are exact elements of N, and

    P subset span{a_0 b : a,b in A}+N3(K,A).                 (1)

Then the omitted P-with-P singular products also lie in N. Therefore
K+A+P strongly generates its vertex subalgebra. Every membership test
assumed in the criterion has output weight at most four.

## Proof of the omitted relations

The identities used are zero-mode derivation, skew symmetry, the
commutator/iterate formulas, and differential normal-product expansion;
see [De Sole--Kac, Section 2 and Lemma 3.2]
(https://arxiv.org/html/math-ph/0312042#S2).

For a,b in A, p in P and n>=0,

    (a_0 b)_n p = a_0(b_n p)-b_n(a_0 p).                 (2)

Every a_0 preserves N: it commutes with translation, is a derivation of
each normal product, and its values on K,A,P belong to N by hypothesis.
This argument works before associating or ordering normal words, so does
not assume the conclusion. Thus the first term in (2) is in N.

The vector a_0 p has weight four. Its differential normal expressions
have the following possible shapes, besides derivatives of generators:

    K P, A A, K K A, K K K K.

There can be at most one P factor. All bracketings and derivative
placements are allowed. Applying b_n to these shapes uses only known
A-with-P, A-with-A, and K-with-any-generator singular products. For
example, applying the mode commutator to A_(-1)A introduces a term
(b_j A)_(n-j-1)A. Its only possible weight-three left input occurs at
j=0, and its singular products with A are already known by skew
symmetry. Applying it to K_(-1)P introduces (b_j K)_(n-j-1)P, whose
left input has weight at most two. Derivatives follow from

    b_n T v = T(b_n v)+n b_(n-1)v.

The K K A and K^4 shapes reduce by the same identities. Equivalently,
the weight filtration in the Wick formulas forces every nested term to
involve a known pair: no P-with-P pair can occur inside a weight-four
normal expression acted on by a weight-two field. Thus b_n(a_0 p) is
in N. The remainder N3(K,A) in (1) has shapes T A, T^2 K, K A, K^3;
its modes on p are likewise controlled by the already known pairs.
This proves the omitted singular products, all of output weight<=5,
without evaluating an ambient weight-five vector.

Once every generator singular product closes, the usual induction on
weights in Wick and quasi-associativity gives full vertex-subalgebra
closure and allows normal words to be put in the usual fixed bracketing.
No freeness or independence of normal monomials is required.

## Why the saved S3 meets the structural premise

The frozen producer `hi_cft_20260923_next_grade4_exact.py`, function
`grade3`, first builds K_(-1)S2+T S2 and obtains dimension 634. It then
adds only charged highest-weight fields in S2 acting by mode zero on
S2, followed by the two current lowering zero modes. It has no u_1
closure stage in grade three. Its saved total is 956.

The initial normal space is K-stable. Current zero modes are derivations,
so they send a_0 b to (k_0 a)_0 b+a_0(k_0 b). Since S2 is K-stable,
all later directions belong to S2_0 S2 modulo the initial normal space.
Thus the last 322 independent echelon rows can serve as P. Their exact
saved recipes and eliminations provide (1), even though each row need
not itself be a single zero product. Taking all of S2 as A is harmless.

The existing characteristic-zero checkpoint consequently supplies the
required provenance. It does not yet certify all S2-with-P singular
products or their normal-span relations.

## Concrete remaining pilot

Construct the full normal span

    N4=K_(-1)S3+T S3+S2_(-1)S2.

Modulo the affine normal products already in the first two summands,
S2 has ten highest-weight copies: the eight charged source fields and
two neutral stresses. Highest-left against every right S2 vector,
followed by current lowering, gives every S2_(-1)S2 product. The same
covariance reduces the only new highest-output singular check to these
ten fields acting by mode zero on the 322-row quotient P, provided
lower descendant contributions and the K-stability of N4 are retained.

In a final certificate all lower singular products must also be checked;
their targets are the existing grades<=3. A finite-prime pilot tests
normal-span rank and residuals, with source-bound words. It neither
proves characteristic-zero containment nor properness. Positive exact
normal-polynomial identities, reconstructed and checked over the
original number field, would complete the stated sufficient criterion.

Using only actual u on the left is not currently justified: its K-orbit
need not span all ten copies. All ten are retained in the bounded pilot.
The reduction removes both a weight-three-left lattice-mode engine and
independent P_1 P / P_0 P ambient calculations from that route.
