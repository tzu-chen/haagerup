# Recursive generators reduce the finite OPE certificate

23 September 2026. An algebraic sufficient criterion and an exact certificate
format. No numerical job was launched for this note. This generalizes the
weight-three reduction in `hi_cft_20260923_next_strong_grade4_reduction.md`.
It does not assert that the required membership identities have passed.

## 1. Statement

Let V be a nonnegatively integrally graded vertex algebra, with V0=C1. Fix
finite homogeneous subspaces S_d of weight d for 1<=d<=H. Put K=S_1 and
A=S_2. Let N be the span of the vacuum and all differential normally
ordered words in the S_d, allowing every parenthesization initially.
Assume the following identities hold in V:

1. Every singular product k_n s and a_n s lies in N, for k in K, a in A,
   s in any S_d, and n>=0.
2. For 3<=d<=H,

       S_d subset A_0 S_(d-1) + N_d(S_1+...+S_(d-1)).       (1)

Then N is a vertex subalgebra. In particular S_1+...+S_H strongly
generates the vertex algebra it generates. Every explicit membership
test in condition 1 has output weight at most H+1. No independent
singular-product calculation through weight 2H-1 is required.

Condition 2 is a statement about actual vector identities, not just a
dimension count. Linear combinations in A_0 S_(d-1) are allowed. The
remainder permits arbitrary derivative and normal-product expressions
of weight d in the lower-weight spaces.

## 2. A filtered Wick observation

Suppose singular brackets between all generator pairs of total weight
less than W have already been shown to lie in N. Then the same holds
for singular brackets of normal expressions of total weight less than W.
Moreover, if two normal expressions have total weight W, and at least
one is a derivative or a normal word with at least two positive-weight
factors, their singular bracket is determined by generator-pair brackets
of total weight less than W.

This follows by induction using sesquilinearity, skew symmetry, and the
noncommutative Wick identity

    [x_lambda :yz:] = :[x_lambda y]z: + :y[x_lambda z]:
                       + integral_0^lambda [[x_lambda y]_mu z] dmu.

In its first two terms, each pair has smaller total weight because the
omitted factor has positive weight. In a nested term, a coefficient
x_j y has weight wt(x)+wt(y)-j-1, so its pair with z has total weight
at most W-1. Derivatives are removed by sesquilinearity before applying
the induction. If the composite is on the left, first use skew symmetry;
the final substitution -lambda-T only differentiates an already known
normal expression. Null relations among normal words cause no problem.

These are identities inside the given vertex algebra, not an assertion
that a proposed nonlinear presentation is freely generated. The source
for the identities is [De Sole--Kac, Section 2, Definition 2.2 and equations
immediately following it](https://arxiv.org/html/math-ph/0312042#S2).

## 3. Proof of the criterion

For a in A, the zero mode a_0 commutes with translation and is a derivation
of every normal product. Condition 1 therefore implies a_0 N subset N,
before any ordering or reassociation of normal words.

Prove all generator singular products s_n t lie in N by lexicographic
induction on

    (wt(s)+wt(t), wt(s)).

Pairs with left weight 1 or 2 are condition 1. For left weight d>=3,
apply (1). A derivative or composite normal remainder has its singular
products with t controlled by strictly smaller total weights, by the
filtered Wick observation. For a zero-product summand s=a_0 b,
wt(b)=d-1, use

    (a_0 b)_n t = a_0(b_n t) - b_n(a_0 t).                (2)

The first term lies in N: b_n t has smaller total pair weight and a_0
preserves N. The second input a_0 t is a normal expression of weight
wt(t)+1 by condition 1. Every derivative term and every product with at
least two factors is handled by smaller-total-weight brackets. The only
remaining possibility is an undifferentiated single generator of weight
wt(t)+1. Its pair with b has the original total weight but smaller left
weight d-1. Thus it is an earlier lexicographic case. If wt(t)=H, such
a single generator does not occur, since the generator list stops at H.
This proves (2), including n=0, without circularity.

All generator singular products now close in N. Induction with the same
Wick identities makes all singular products of N close in N. Translation
and all normal products preserve N by its definition, so every negative
mode preserves N as well. Hence N is a vertex subalgebra. Standard
quasi-associativity puts its words into a fixed normal ordering if desired.

## 4. Application and the unproved gate

For H=3 the saved S3 provenance has the required form

    S3 = N3(K,A) + span(A_0 A),

with the 322 additional directions produced after the 634-dimensional
normal part. It is enough to test K-with-S and A-with-S singular products
in the exact normal spans through weight four. If the weight-four check
fails, a prospective P4 can consist of the new A_0 P3 directions modulo
N4. The general criterion would then ask for the enlarged generator
list's K/A products through weight five. This is a possible iteration,
not an assertion that it stops at any particular H.

In the present task, proving the H=3 identities would imply that U1=K1,
and therefore U is proper in B. Every source field used in the certificate
must first be an unconditional U-vector. Conditional conclusions such as
"if proper then U3=S3" cannot supply a membership identity in this proof.

## 5. Positive exact certificates after a modular pilot

A modular calculation should retain the original short normal words,
not just the normalized echelon vectors. For each Cartan block choose
some normal-word columns v_1,...,v_r that are independent at one good
split prime, and retain r ambient pivot coordinates. The resulting
r-by-r minor M is invertible over the number field

    F = Q(sqrt(13),sqrt(-3)).

Indeed its determinant has a nonzero reduction at the selected field
embedding, and therefore cannot vanish in F. For each desired singular
product t, solve M c=t on these pivot coordinates, reconstruct c in F,
and then verify the full sparse-vector identity

    t = sum_j c_j v_j                                      (3)

over F. Only a verified identity (3) is a containment certificate. It is
unnecessary to prove that the chosen columns exhaust the entire normal
span: any subset of actual normal words furnishing (3) suffices. Thus
the final proof does not rely on a characteristic-zero rank extrapolation
from the modular pilot.

There are two useful solver formats:

* Direct exact solve: expand multiplication by each field element into a
  4-by-4 rational matrix and solve the resulting 4r-dimensional rational
  system with FLINT. Solve all right-hand sides for a block together.
* Modular solve: for each good completely split prime p, solve at all four
  choices sqrt(13)=+/-s and sqrt(-3)=+/-t. Inverse sign transforms recover
  the four field coordinates modulo p; combine them by CRT and rational
  reconstruction. If any of the four minors is singular, discard that
  prime. Reconstruction is a candidate-finding step; (3) is the proof.

If c_(epsilon,delta) is one reconstructed solution coordinate evaluated
at (epsilon*s,delta*t), its four field coefficients modulo p are

    c0 = sum c_(epsilon,delta)/4,
    c1 = sum epsilon*c_(epsilon,delta)/(4s),
    c2 = sum delta*c_(epsilon,delta)/(4t),
    c3 = sum epsilon*delta*c_(epsilon,delta)/(4st).

Certificate records should include source hashes, exact word recipes,
Cartan weights, the pilot's selected columns and pivot coordinates,
exact reconstructed coefficients, and the exact zero residual in (3).
The verifier can stream one target and one normal-word block at a time;
it does not need the full ambient weight-four basis or simultaneous
copies of every target. It should retain explicit coefficient/term caps.

During current-lowering closure, apply the current to the accepted raw
normal-word vector, rather than its modularly normalized echelon vector.
The accepted raw vectors and their echelon reductions span the same
modular space, so this does not change the closure argument. It retains
short exact mode-word recipes instead of requiring integer lifts of long
modular elimination combinations. The same principle favors 322 raw
zero-product lifts for P3: their independence modulo the known exact
634-dimensional normal space can be certified at a good prime, and the
known exact 956-dimensional S3 then proves they form a complement.

For the final exact verification, clear denominators in each input word
and in the target separately. After clearing the common denominator of
the reconstructed coefficients, (3) becomes an identity of integral
four-tuples. GMP/FLINT integer accumulation avoids a Fraction gcd for
each sparse term. In the basis (1,s,t,st), s^2=13 and t^2=-3,

    (a,b,c,d)*(e,f,g,h) =
      (ae+13bf-3cg-39dh,
       af+be-3ch-3dg,
       ag+ce+13bh+13df,
       ah+de+bg+cf).

The highest-weight reduction still needs all ten primitive weight-two
highest fields, including the two singlets, and all P3 quotient lifts.
Known K zero-mode covariance and K-stability of the full normal span
then extend these identities to the remaining left fields. Lower
singular products must also be justified; Section 6 gives an algebraic
way to do this for the P3 inputs. No numerical execution is authorized
by this note.

## 6. An additional weight-three Virasoro reduction

This section is specific to H=3. Assume K is the retained affine current
space; S2 is K-stable, contains its affine normal descendants, and

    S3 = N3(K,S2) + span{a_0 b: a,b in S2}.

Assume all singular S2-with-S2 products have been certified to lie in
the expected spaces S3,S2,K,C1. Assume the analogous current-with-S2
relations. These are actual identities, not conditional character data.
Let A_high be the ten primitive highest-weight representatives, and
assume L(1)a=0 for each a in A_high. In the present construction this
follows from K-equivariance of L(1): none of their K-types, including
the two singlets, occurs in K1. Current-zero-mode descendants remain
quasiprimary.

The S3 provenance and current commutators then give

    K_0 S3 subset S3,    K_1 S3 subset S2,    K_2 S3 subset K,
    L(1)S3 subset S2,   L(2)S3 subset K.

For example, for a quasiprimary a in S2 and b in S2,

    L(1)(a_0 b) = 2a_1 b + a_0 L(1)b,
    L(2)(a_0 b) = 3a_2 b + a_0 L(2)b.

Here L(1)b is a retained current and L(2)b is scalar. For a current k,
the commutator [k_n,a_0]=sum_j binomial(n,j)(k_j a)_(n-j) reduces the
positive-current claims to the already known S2-with-S2/current
relations. Derivatives and affine normal remainders obey the same
inclusions by the ordinary Virasoro and current identities. This also
justifies the K-with-P3 singular products without separate ambient
calculations.

For the normal weight-four space constructed in the pilot,

    N4 = K_(-1)S3 + T S3 + S2_(-1)S2,

these relations imply

    L(1)N4 subset S3,    L(2)N4 subset S2.                (4)

It suffices to prove (4) on the highest-left normal seeds and their
K-lowerings. Virasoro modes commute with current zero modes. On a
quasiprimary highest-left seed a_(-1)b, the two relevant identities are

    L(1)(a_(-1)b) = 3a_0 b + a_(-1)L(1)b,
    L(2)(a_(-1)b) = 4a_1 b + kappa_a b + a_(-1)L(2)b,

where L(2)a=kappa_a 1. Every term is in the stated smaller space.
The current and translation seeds are immediate from the inclusions
above.

Now suppose the exact mode-zero certificates a_0 p in N4 have passed,
for a in A_high and every P3 lift p. Then

    2a_1 p = L(1)(a_0 p) - a_0 L(1)p             lies in S3,
     a_2 p = L(1)(a_1 p) - a_1 L(1)p             lies in S2,
    2a_3 p = L(2)(a_1 p) - a_1 L(2)p             lies in K.

The product a_4 p has ambient weight zero and is automatically scalar;
higher modes vanish by nonnegative grading. The possible L(2)a vacuum
term in the Virasoro commutator vanishes in these nonnegative modes.
Thus no separate exact reconstruction of a_n p for n>=1 is necessary
once the premises of this section have been certified. Keeping the
pilot's direct lower-mode checks is a useful independent cross-check.

The remaining finite exact gate is therefore the full S2-with-S2
singular closure, the existing affine covariance/current relations,
and the ten highest-left mode-zero products against P3. This does not
justify omitting the neutral S2_0 S2 checks: those are among the premises.
