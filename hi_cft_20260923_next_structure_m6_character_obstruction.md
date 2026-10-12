# Character obstructions for the two standard Z3+6 center orientations

23 September 2026. Exact algebra and theta identities; no computation
was launched for this note. For the explicit center category

    M tensor Rep(A2,1),   M=Rep(A2,9)_Z3^local,

the c=8 vacuum current dimension satisfies

    dim V1=8+A,   A>=0 integer.

For its reversed ribbon category it satisfies

    dim V1=5+12P,   P>=0 integer.

Thus neither category can be that of the proper candidate U, whose
current dimension is six. These statements use the established
extension B=V_(E6+A2), with B=V plus one simple module, and positivity
of all nonvacuum lowest weights. They do not classify all categories
having the Z3+6 fusion ring; the source-scope qualification is below.

## A three-dimensional modular projection

Use Yu's labels I,Y1,Y2,Y3,Y4,Y5,X1,X2,X3, with

    d=3+2sqrt(3),
    dim(Y1)=dim(Y2)=dim(Y3)=dim(Xi)=d,
    dim(Y4)=2d+2, dim(Y5)=2d+1.

Their twists are i for Y1 and Xi, -1 for Y2,Y3, exp(4pi i/3)
for Y4, and 1 for I,Y5. The explicit S matrix is in
[Yu, Lemma3.4 and Proposition3.5](https://arxiv.org/html/2312.12195v2#S3.SS1).
Its positive normalization is 4d. The extension's nonvacuum object
is uniquely (Y5,0), by quantum dimension and twist, so

    chi_(I,0)+chi_(Y5,0)=chi_B.

The S matrix is invariant under all permutations of the quartet
J={Y1,X1,X2,X3}, and under interchange of Y2,Y3. The T matrix
has the same invariances. Average over these permutations, and over
charge conjugation of the A2 factor. This is a modular projection;
it does not require those distinct actual characters to agree.

For each averaged A2 label put

    a=(chi_Y1+chi_X1+chi_X2+chi_X3)/4,
    b=(chi_Y2+chi_Y3)/2,
    v=(chi_I-chi_Y5, -2a, -2b).

The complementary three-dimensional block has

    S_v = -1/2 [[1,2,1], [1,0,-1], [1,-2,1]],
    twist exponents = (0,1/4,1/2).

This follows directly by subtracting the I and Y5 rows and averaging
the four J rows. Before the -2 changes of coordinates, the block is

    [[-1/2,2,1], [1/4,0,1/2], [1/4,1,-1/2]].

After tensoring with the two-dimensional A2 character block and
multiplying by eta^8, this is the Weil representation of

    L=A1 orthogonal-direct-sum A1 orthogonal-direct-sum A2,

restricted to the subspace invariant under interchange of the two
A1 factors and conjugation of A2. Its discriminant form is

    D=(Z2)^2, q(x,y)=(x+y)/4,   tensor Z3, q(s)=s^2/3.

The notation q(x,y) uses x,y in {0,1}; equivalently q=(x^2+y^2)/4.
The three first-factor coordinates are 00, the average of10 and01,
and11. This proves the modular identification without assuming
independence of irreducible characters.

## Original orientation: at least eight currents

Only the four J labels with A2 vacuum can contribute nonvacuum
character poles: their possible lowest weight is1/4. Let A be the
sum of these four top dimensions, counting zero when a lowest
weight has been lifted by an integer. The v_middle pole coefficient
is -A/2.

The affine reference W=(A2,9 extended by its Z3 simple currents)
tensor A2,1 has16 currents. Its only such polar top is the eight-
dimensional adjoint top of Y1 at weight1/4. The Xi weights start
at5/4. Thus its A value is8.

Let H be the harmonic quadratic

    H=energy_(A1+A1)-energy_A2,

where energy is squared norm divided by two. Its vector-valued
harmonic theta series has weight four and the required Weil
transformation. Its two needed coefficients are

| coordinate | exponent | Theta_H coefficient |
|---|---:|---:|
| 10 or01, A2 vacuum | 1/4 | 1/2 |
| vacuum | 1 | -2 |

The polar row contains the two vectors plus/minus one-half of an
A1 root, each with energy1/4. The vacuum row counts four A1 roots
with H=1 and six A2 roots with H=-1.

Subtract the affine projected character vector. Its only possible
nonvacuum pole is matched by

    eta^8 delta v = lambda Theta_H,   lambda=8-A.

To justify equality, subtract the right side divided by eta^8.
The remainder is a weight-zero form for a finite-image modular
representation, holomorphic in the upper half-plane and at every
cusp. It is constant. The only T-fixed coordinate before the eta
multiplier is (00,A2-nonvacuum), and S does not preserve that line,
so there is no invariant constant and the remainder is zero.

Since the B vacuum character is fixed, delta v_vac=2 delta chi_V.
Consequently the vacuum q coefficient gives

    2(dim V1-16)=-2lambda,
    dim V1=8+A>=8.

## Reverse orientation: current dimension5 modulo12

The reversed ribbon category has the same averaged real S matrix
and opposite twist exponents. Its eta^8-multiplied block is the Weil
representation for -D, of signature4 modulo8. Realize -D by the
positive rank-four lattice with basis a,b,c,d and Gram matrix

    [[2,-1,-1,-1],
     [-1,2,0,0],
     [-1,0,2,0],
     [-1,0,0,4]].

The first three vectors span A3; the determinant is12. Set

    w=d+a+(b+c)/2,   w^2=3,   w perpendicular A3.

Discriminant generators can be chosen as

    x=(b+d)/2, y=(c+d)/2, z=2w/3.

The first two have order2, q(x)=q(y)=3/4, and their mutual
pairing is integral. The last has order3 and q(z)=2/3. Its pairings
with x,y are integral. These generators therefore realize -D.

Project the theta series to the same swap-invariant, separately
conjugation-invariant subspace as the character block. The polar
coordinate is (x+y,z), represented by -w/3, because x+y is
congruent to w and2w belongs to the lattice. Its unique shortest
vector has norm1/3 and energy1/6. Swapping x,y fixes this coordinate;
conjugating z replaces it by the negative coordinate. Ordinary and
even-polynomial theta series agree on a coordinate and its negative,
so this projection does not halve the polar coefficient.

Uniqueness of the shortest vector follows without enumeration:
any nonzero A3 dual-lattice projection has squared norm at least3/4,
larger than1/3, while the perpendicular projection of the lattice is
Zw. The coset's perpendicular coordinates are -1/3 modulo integers;
requiring zero A3 projection leaves only -w/3 at this norm. The
opposite coordinate contains +w/3. There are twelve norm-two roots,
all in A3: a nonzero d-coordinate gives perpendicular norm at least3.

Use projected ordinary theta Theta (weight two), harmonic polynomial

    H=norm_A3-3 norm_(A3-perpendicular),

and F=-6D2Theta, where D2=q d/dq-E2/6. The needed coefficients are

| coordinate | exponent | F | Theta_H |
|---|---:|---:|---:|
| vacuum | 0 | 1 | 0 |
| vacuum | 1 | -84 | 24 |
| polar (11,nonvacuum) | 1/6 | 0 | -1 |

Indeed Theta_vac=1+12q+..., giving D2Theta_vac=-1/6+14q+....
The polar derivative coefficient vanishes because1/6-1/6=0.

The only nonvacuum poles of the reversed character block occur at
weight1/6 in (Y2 orY3,A2-nonvacuum). Put

    P=dim top(Y2,s1)+dim top(Y3,s1),

again counting zero if a lowest weight is lifted. Contragredience
makes the sum for s2 equal, so averaging A2 does not change P.
The projected v_last pole coefficient is -P. Pole cancellation gives

    eta^8 v=F+P Theta_H.

There is no constant remainder: none of the exponents
-1/3-(0,1/4,1/2)-(0,1/3) is an integer, so T has no fixed vector.
Finally, chi_B=q^(-1/3)(1+86q+...), and eta^8 begins
q^(1/3)(1-8q+...). Thus the vacuum q coefficient on the left is
2 dim V1-94. Comparison yields

    2 dim V1-94=-84+24P,
    dim V1=5+12P.

Since P is a nonnegative integer, dim V1 cannot equal6.

## Scope of the category identification

These are exclusions of two explicit ribbon categories. In
[Yu, Theorem3.6](https://arxiv.org/html/2312.12195v2#S3.SS1), the proof
constructs a category by condensation from M and then shows that it
has the Z3+6 fusion rule. This argument supplies the stated model;
it does not by itself classify every pseudounitary categorification
of that fusion rule. A separate uniqueness or unitarity/classification
argument is required before converting this into a universal
exclusion of the rank-four multiplicity-six alternative.
