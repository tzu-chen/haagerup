# Universal modular data for the remaining Z3+3 branch

23 September 2026. **Independently audited.** This argument removes the
C*-classification hypothesis from the earlier m=3 character exclusion.
See `hi_cft_20260923_next_m3_universal_independent_audit.md` for the
independent mathematical and primary-source checks. No numerical job is used.

Assume the already established proper rank-four branch: C is the positive
spherical boundary fusion category, its fusion ring is Z3+3, its pointed
subcategory is untwisted, Z(C)=Rep(U), and the actual connected etale
algebra for B/U is 1+X. These assumptions do not include unitarizability
of C as a tensor category.

## Center induction, including a useful generalization

Write the near-group multiplicity as 3k and its noninvertible as r:

    ar=ra=r, r^2=1+a+a^2+3kr,
    d=dim(r), d^2=3+3kd,
    s=2+kd, Dim(C)=3s.

The four one-dimensional fusion-ring characters have formal codegrees
3s, 9s/d^2, 3, 3. Consequently

    I(1)=1+X+Y+Y',
    dim(X)=d^2/3=1+kd, dim(Y)=dim(Y')=s,
    theta_X=theta_Y=theta_Y'=1.

Using FI(1)=4*1+a+a^2+3kr, Frobenius reciprocity, and coefficient
comparison in Q(d) gives

    F(X)=1+kr,
    F(Y)=1+a+kr, F(Y')=1+a^2+kr.

Here Y and Y' can be exchanged. Further,

    FI(a)=1+4a+a^2+3kr,
    FI(a^2)=1+a+4a^2+3kr.

Thus I(a), I(a^2) each have norm squared four, contain Y,Y'
respectively, and have mutual inner product one. Their remaining
summands are multiplicity-free, with exactly one in common:

    I(a)=Y+C+D+E, I(a^2)=Y'+C+D'+E'.

No summand here coincides with X or another summand of I(1).
For nonnegative integers c,p,q we have

    F(C)=a+a^2+cr,
    F(D)=a+pr, F(E)=a+qr,
    F(D')=a^2+pr, F(E')=a^2+qr,
    c+p+q=2k.

Duality pairs D with D' and E with E'; C is self-dual.
The untwisted condition gives nu_3(a)=1. Positivity of dimensions
and the center indicator formula force all four twists in I(a)
to be cube roots of unity. The first indicator, separated over the
linearly disjoint fields Q(d), Q(zeta_3), reads

    2+2 theta_C+theta_D+theta_E=0,
    k+c theta_C+p theta_D+q theta_E=0.

Counting cube roots in the first equation and then applying the second
gives, for one primitive cube root zeta,

    theta_C=zeta, theta_D=theta_E=zeta^2,
    c=k, p+q=k.

The primed twists equal their unprimed partners by ribbon duality.
Every other central simple Z_j forgets to n_j r, and global dimension
gives

    sum_j n_j^2=6+3k^2+4pq.                    (1)

The first two indicators of r then give

    S1 := sum_j n_j^2 theta_j
        = k^2-kd-(p-q)^2 zeta^2,
    S2 := sum_j n_j^2 theta_j^2
        = conjugate(S1)+epsilon sqrt(9k^2+12), (2)

where epsilon=nu_2(r) is +1 or -1. These formulas come from the
multiplicities k,k,k,c,p,p,q,q in I(r), followed by 3/d=d-3k.

## Specialize to k=1: a nondegenerate pointed factor is forced

Now {p,q}={0,1}. Label D to have p=0. Then D and D' are the two
nontrivial invertible central objects, with F(D)=a and F(D')=a^2.
Their twists are zeta^2, so they generate the nondegenerate pointed
category P=P(Z3,q(a)=zeta^2). It is not Tannakian. Hence

    Z(C)=M tensor P

for its modular centralizer M. No C* structure is used in this
factorization. Every P orbit has three objects with equal dimension.

The nine already identified central simples form three such orbits:
dimensions 1, 1+d and s=2+d. For example D tensor X=E, since its
forgetful image is a+r, and therefore X centralizes P:

    theta_(D tensor X)/(theta_D theta_X)=zeta^2/zeta^2=1.

Similarly D tensor C is one of Y,Y', as is seen from its forgetful
image; C centralizes P since 1/(zeta^2 zeta)=1. The representatives
1,X,C in M thus have dimensions 1,1+d,s and twists 1,1,zeta.

For the remaining objects, equation (1) gives sum n_j^2=9. The free
three-object P orbits reduce this to sum_orbits n_j^2=3. Therefore
there are precisely three more simple objects in M, all of dimension d.
In particular M has rank six, and Z(C) has rank eighteen. Let their
twists be z_1,z_2,z_3.

## The three remaining twists are forced by two moments

Choose zeta=exp(2 pi i/3); the other choice conjugates everything.
For k=1, equations (2) give

    S1=(-sqrt(21)+i sqrt(3))/2,
    S2=(epsilon-1/2)sqrt(21)-i sqrt(3)/2.

The sum of twists of P is 1+2zeta^2=-i sqrt(3), and its squared-twist
sum is i sqrt(3). Factoring the three remaining P orbits gives

    sum z_i = A := (-1-i sqrt(7))/2,
    sum z_i^2 = -1/2-i(epsilon-1/2)sqrt(7).

If epsilon=-1, the second sum has absolute value four, impossible for
three unit complex numbers. Thus epsilon=1, and both sums equal A.
Since A^2+A+2=0, Newton's identity gives

    e2=(A^2-A)/2=conjugate(A).

For three unit complex numbers, e2=e3 conjugate(e1). Since A is
nonzero, e3=1. Their characteristic polynomial is consequently

    t^3-A t^2+conjugate(A)t-1.

Its roots are precisely zeta_7^3,zeta_7^5,zeta_7^6. The conjugate
orientation gives the quadratic-residue orbit. These are the two
G2 level-three twist patterns.

## Branching forces the first three S rows

The actual algebra A=1+X for B/U belongs to M, since X centralizes P.
Its dimension is s. Its local module category M_A^0 has dimension

    Dim(M)/s^2 = (3s^2)/s^2 = 3.

It is the pointed Z3 category with twist zeta: its multiplicative
central charge equals that of M, namely i, since Z(C) has central
charge one and P has central charge -i. The nonvacuum local modules
have dimension one internally, hence underlying M-object dimension s.
They cannot contain the vacuum, since A is the unique simple local
module receiving a map from the unit under induction reciprocity.
The list of six M dimensions then forces each of these two local
modules to have underlying object C. (Other sums with dimension s
would require a vacuum summand.)

Thus the restriction columns of the local extension are

    1+X, C, C.

Use the standard modular-data intertwining relation for a connected
etale algebra. Set Dhat=sqrt(Dim(M))=sqrt(3)s, and S_hat=Dhat S.
Together with symmetry and the known dimension row, it gives

    S_hat(1,*) = [1,1+d,s,d,d,d],
    S_hat(X,*) = [1+d,1,s,-d,-d,-d],
    S_hat(C,*) = [s,s,-s,0,0,0].              (3)

For example the vacuum restriction column gives S_i1+S_iX, and
either other column gives S_iC. Their entries follow from the
three-by-three pointed S matrix and the duplicate restriction C,C.

## The remaining S block is unique

All six simples of M are self-dual: the first three have distinct
dimensions, and the last three have distinct twists. Its S matrix is
therefore real: its fusion matrices are real symmetric, and Verlinde
diagonalization makes S_ij/S_0j real; S_0j is positive. This does not
assume C* unitarizability. Write H for the last three-by-three block
of S_hat. Orthogonality with the first row of (3) gives

    sum_j H_ij=d.

The modular identity with unnormalized T=diag(theta),

    S_hat T S_hat = i Dhat T^(-1) S_hat T^(-1),

in position (i,1) gives

    sum_j H_ij z_j = d+i Dhat z_i^(-1).       (4)

Each real row of H is uniquely determined by its real sum and the
real and imaginary parts of (4). The three points z_1,z_2,z_3 are
distinct on the unit circle, hence not collinear, so the coefficient
matrix with rows 1, Re(z_j), Im(z_j) is invertible.

Consequently dimensions, T, and S are forced, up to simultaneous
permutation and conjugation. The known G2 level-three category in the
corresponding orientation has exactly these data, so M has its modular
data and Z(C) has those of G2_3 tensor A2_1 or their joint reversal.
This conclusion is about S,T; no tensor-category uniqueness claim is
needed for the earlier character obstruction.

The independent audit passes, so the two harmonic-theta character
exclusions eliminate the entire pseudounitary Z3+3 branch
in the present VOA problem, without a C*-unitarizability assumption.
The k=2 case admits p=q=1 in this induction calculation and requires
a separate argument.
