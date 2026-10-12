# Independent audit: universal modular data in the Z3+3 branch

23 September2026. Audited `hi_cft_20260923_next_m3_universal_data.md` by
algebra and primary-source checking only. No numerical computation.

**Verdict: passes under its stated hypotheses.** In particular it uses
the actual connected etale B/U algebra1+X. It does not classify all
near-group associators and does not assume their unitarizability. It
forces the S,T data needed by the existing character obstruction.

## Induction and indicators

The induction-of-unit/formal-codegree inputs are the general spherical
results in [Ostrik, Section2](https://arxiv.org/html/1309.4822#S2),
not rank-three classification conclusions. The twist-trace formula is
[Ng--Schauenburg, Theorem4.1](https://arxiv.org/html/math/0601012#S4),
which applies to spherical fusion categories and their induced center
twist. The canonical positive spherical structure and the untwisted
pointed subcategory are essential explicit assumptions here.

I checked the general3k calculation. The four codegrees are
3s,9s/d^2,3,3. Since each I(1) summand has one vacuum in its forgetful
image, irrational coefficient comparison forces

    F(X)=1+kr,
    F(Y)=1+a+kr, F(Y')=1+a^2+kr,

after exchanging Y,Y'. The norm-four induction vectors I(a),I(a^2)
have one known summand each and exactly one further common summand.
Their remaining norm-three parts must be multiplicity-free. This gives
the stated C,D,E,D',E' list without omitting a possible multiplicity.

The first indicator for a, with its third indicator fixed at one, gives

    2+2t_C+t_D+t_E=0,
    k+c t_C+p t_D+q t_E=0.

Positivity in the third-indicator trace forces each twist to be a cube
root. The first displayed equation rules out t_C=1 and forces
t_C=zeta, t_D=t_E=zeta^2, up to conjugation. The second then gives
c=k and p+q=k. Ribbon duality preserves twists, so the primed partners
have the same twists as their unprimed partners.

The squared dimensions of the nine known center objects sum to

    18+18kd+(6k^2-4pq)d^2.

Subtracting from9s^2 and dividing by d^2 gives6+3k^2+4pq exactly.
For I(r), the known first-twist trace simplifies to

    d[k(d-k)+(p-q)^2 zeta^2].

Thus its negative divided by d is the asserted S1. The second-twist
known contribution is its conjugate, while
3s/d=2d-3k=sqrt(9k^2+12). This independently verifies both moment
formulas, including the sign of the Frobenius--Schur indicator term.

## Pointed splitting and the remaining twists at k=1

Now one of p,q is zero. The corresponding D,D' have dimension one,
forget to a,a^2, and exhaust the nontrivial invertibles: any unidentified
simple has dimension n*d, which cannot equal one. They form the pointed
Z3 category with nondegenerate quadratic form q(a)=zeta^2. Therefore
the modular centralizer decomposition applies.

The claims D*X=E and D*C=Y or Y' are justified by forgetful images
and dimensions together: no unidentified object of dimension n*d
can compete with dimensions1+d or2+d. Balancing gives trivial
monodromy with D in each case, so X,C belong to the centralizer M.
All remaining pointed-factor orbits have three objects. The leftover
sum of n^2 is nine, hence M has exactly three further objects, each
of dimension d. This proves rank(M)=6, not merely an upper bound.

Dividing the two indicator moments by the twist sums of the pointed
factor gives

    sum z_i=(-1-i*sqrt(7))/2=A,
    sum z_i^2=-1/2-i*(epsilon-1/2)*sqrt(7).

For epsilon=-1 the second sum has modulus four, contradicting the
three unit-modulus summands. For epsilon=1 it equals A. The identities
A^2+A+2=0 and e2=e3*conjugate(e1) then force e2=conjugate(A),e3=1.
The cubic has precisely the nonresidue seventh roots with exponents
3,5,6. No assumption about unknown fusion coefficients is used here.

## The actual extension algebra fixes the first three rows

Because M is a full tensor subcategory and contains the object1+X,
the actual B/U multiplication and its separability morphism also lie
in M. Its twist is trivial and its positive dimension is s. Therefore
local modules have global dimension three and preserve multiplicative
central charge. The restriction maps intertwine normalized modular
matrices by [Kirillov--Ostrik, Theorems4.1 and4.5](https://arxiv.org/html/math/0101219#S4).
These theorems require neither a C* structure nor a unitary realization.

A positive fusion category of global dimension three is pointed: there
are at most three simples; a putative rank-two case would require a
self-dual object of dimension sqrt(2), incompatible with x^2=1+n*x
for integral n. Thus the local category is the pointed Z3 category.
Its central charge fixes its quadratic form to have nontrivial twist
zeta, for the orientation used in the root note.

A nonvacuum simple local module cannot have a vacuum in its underlying
M-object, because induction reciprocity identifies that multiplicity
with Hom_A(A,M). Enumerating nonnegative combinations of the dimensions
1,1+d,2+d,d,d,d then shows that the only dimension-s underlying object
without a vacuum summand is C. Thus the branching columns really are
1+X,C,C. The possible expressions1+X and2*1+Z_i are excluded precisely
by that reciprocity argument.

Applying S_M b=b S_local yields the displayed first three rows. For
example the vacuum restriction column gives row sums
S_hat(i,1)+S_hat(i,X)=s,s,2s,0,0,0. The two identical C columns give
S_hat(i,C)=s,s,-s,0,0,0. This verifies every entry and normalization.

## Real S and the last block need no C* assumption

The first three simple objects are self-dual by their distinct dimensions;
the last three are self-dual because their twists are distinct and ribbon
duality preserves the twist. One can prove reality of S without invoking
any categorical unitarization: for a self-dual simple object i the fusion
matrix N_i is real symmetric. Its Verlinde eigenvalues S_ij/S_0j are
therefore real. Positive S_0j then makes all S_ij real. The modular
identity S^2=I supplies row orthogonality.

For the remaining block H, orthogonality to the dimension row gives
sum_j H_ij=d. In the STS identity, the (i,vacuum) entry on the left is

    -d^2+d*sum_j H_ij z_j.

The right entry is i*Dhat*d*z_i^(-1), so equation(4) follows with the
stated sign and coefficient. Its real and imaginary parts, together
with the row sum, determine each real row uniquely. Three distinct
points on a circle cannot lie on a line, so the3-by3 coefficient matrix
is nonsingular. Existence is guaranteed by the original modular category;
symmetry and the other modular equations therefore impose no additional
choice. This establishes uniqueness of S for the already fixed T.

## Reference model and orientation

[Abhishek--Grover--Jatkar--Singh, Table4 and Eq.(3.8)](https://arxiv.org/pdf/2312.00275)
give the six G2 level-three twists and S matrix. Its normalized dimension
row, reordered as1,64,27,7,77,14, is proportional to
1,1+d,s,d,d,d. Its1+64 extension has the required branching pattern.
Thus it is a model for the uniquely determined data, up to reversal.

With the root note's explicit zeta=exp(2*pi*i/3), M has C twist zeta
and seventh-root exponents3,5,6. This is **the reverse G2_3 orientation**;
the pointed factor has twist zeta^2 and is reverse A2_1. Conjugating
the entire derivation gives standard G2_3 tensor A2_1. There are no
independent choices of reversing just one factor in this argument.

The prior harmonic-theta note needs only these modular data, positivity
of nonvacuum lowest weights, c=8 and the actual vacuum branching identity
chi_1+chi_X=chi_B. It does not need a tensor-equivalence classification
of the boundary fusion category. Its two current bounds, at least15
and at least14, therefore exclude the entire stated pseudounitary m=3
branch when dim U1=6. This conclusion does not settle the m=6 branch or
properness itself.
