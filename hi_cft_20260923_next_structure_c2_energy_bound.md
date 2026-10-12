# An orthogonal-energy proof of C2-cofiniteness, with a finite grade bound

23 September2026. This is independent of the earlier weak-module
completion argument. It proves C2-cofiniteness of U directly from
the certified positive stress identity and regular unitary factors.
An intentionally loose explicit bound is

    (U/C2(U))_n=0 for n>16748.

This is a strong-generation bound. It is not a bound on the weights
of intermediate states in words in the originally prescribed weak
generators, and it does not settle properness.

## General orthogonal-energy lemma

Let V be a unitary VOA of CFT type with finite-dimensional graded
pieces. Suppose A_i are PCT-invariant regular unitary vertex operator
subalgebras whose intrinsic weight agrees with ambient weight on
their states. They need not share V's full conformal vector. Assume
their intrinsic energy operators are self-adjoint, and

    omega_V=sum_i c_i omega_i,   c_i>0.

The same argument allows normalized compact-group averages of
conjugate subalgebras. For an irreducible ordinary A_i-module M put

    C2_Ai(M)=span{a_(-2)m : a in A_i, m in M}.

Every such quotient M/C2_Ai(M) is finite dimensional by
[Abe--Buhl--Dong, Proposition5.2](https://arxiv.org/html/math/0204021#S5).
There are finitely many irreducible modules. Thus the number

    D_i=max{intrinsic L_i(0)-weight in M/C2_Ai(M) : M simple}

is finite. This maximum includes the ordinary lowest weight of M,
not merely its grade above that lowest weight.

Regularity decomposes V, viewed as a weak A_i-module, into ordinary
simple modules. The unitary form makes the decomposition orthogonal:
take orthogonal bases of the multiplicity spaces. In the present
positive-energy setting these may also respect the commuting ambient
grading. Equivalently, everything below can be checked separately
inside each finite-dimensional ambient grade and then summed.

Define C2_Ai(V) using a in A_i and m in V. It is a direct sum of the
corresponding module C2 spaces, and

    C2_Ai(V) subset C2(V).

Since C2_Ai(M) is homogeneous for L_i(0), its orthogonal complement
contains no intrinsic energy greater than D_i. Multiplicity spaces
can have arbitrarily high ambient energy; L_i(0) acts trivially on
that extra multiplicity grading, which is why this does not affect
the bound. For every v in C2(V)^perp one therefore has

    <L_i(0)v,v> <= D_i <v,v>.

If v also has ambient grade n, the positive stress identity gives

    n ||v||^2 = sum_i c_i <L_i(0)v,v>
               <= (sum_i c_i D_i) ||v||^2.

It follows that C2(V)^perp has no grades above sum_i c_i D_i.
Grade-by-grade orthogonal complements identify it with V/C2(V), so
V is C2-cofinite. No commutativity between the different stress
operators is used.

For a compact average, apply the same bound to every conjugate A_i,
whose module bound D_i is unchanged, and integrate. All integrations
here occur on a finite-dimensional ambient grade. Since the group
acts by automorphisms of V, every conjugate algebra is still in V.

## An explicit general module bound

Suppose the highest nonzero grade of A/C2(A) is at most R. Choose
homogeneous representatives of this quotient, excluding the vacuum.
For an irreducible ordinary module M of lowest weight h, choose any
nonzero top vector; it generates M. The module spanning theorem
of [Buhl](https://arxiv.org/abs/math/0111296), in the normalization
of [Abe--Buhl--Dong, Remark3.2 and Theorem3.3](https://arxiv.org/html/math/0204021#S3),
permits ordered indices

    x1_(-n1) ... xt_(-nt) w,
    n1>=...>=nt>-L,   L<=R,

with positive n strictly decreasing and each nonpositive n repeated
at most2R-1 times. If n1>=2, this vector is already in C2_A(M).
Among the remaining monomials, n=1 occurs at most once and adds
at most R to the energy. The indices n=0,-1,...,-R+1 add at most
R-1,R-2,...,0, each at most2R-1 times. Therefore a uniform bound is

    D(A) <= h_max + R + (2R-1)R(R-1)/2.                 (1)

This proof gives an upper bound even when some allowed spanning
monomials vanish or their relations reduce the degree further.

## Bounds for the four factors in the certified identity

The original positive identity is

    omega_U = omega_(A1,1)
              +(3403/4563)omega_(A1,39)
              +(25/6)average(p)
              +(25/26)average(z),

where p is the Potts stress and z is the PF13 stress. All these
subalgebras are already proved to be inside U.

For affine A1 at level k, its vacuum C2 quotient has highest grade
at most2k; see the basis in
[Arakawa--Lam--Yamada, Eq.(7.1)](https://arxiv.org/html/1207.3909#S7).
An integrable affine module is generated from its finite-dimensional
horizontal top by negative current modes. Modulo module C2 only
the modes j(-1) remain. Their commuting action factors through the
vacuum C2 algebra, so the module quotient is generated as a module
over that graded algebra by its top. Consequently

    D(A1,k)<=h_max+2k=k/4+2k=9k/4.                    (2)

For clarity, the action used here is [a][m]=[a_(-1)m]. The standard
iterate and commutator identities show it is a well-defined action
of A/C2(A) on M/C2_A(M). The PBW statement is special to current-
generated affine modules; it is not assumed for parafermion modules.

For PF13, ALY's C2 embedding theorem and its graded computation
(Theorem7.3 and Lemma6.9) give R<=26. The largest actual ordinary
lowest weight is42/13, as in the previously verified PF13 top table.
Equation(1) gives

    D(PF13)<=16601+42/13=215855/13.

For Potts=PF3, R<=6. One can check this small-level case directly,
without extending a theorem whose proof assumes k>=5. Its C2
algebra is generated by x=[omega], y=[W3], of weights2,3.
The identities at k=3 in
[Dong--Lam--Yamada, AppendixB](https://arxiv.org/html/0809.3630#A2),
using W4=W5=0, give

    y^2=25650 x^3,   x^2 y=0.

The operator W3_1 descends as a derivation (its zero mode is zero
in the C2 Poisson algebra), with

    W3_1(x)=3y,   W3_1(y)=38880 x^2.

Applying it to x^2y=0 gives192780 x^4=0. Hence the quotient is
spanned by1,x,y,x^2,xy,x^3, all of weight at most6. Its ordinary
module lowest weights are0,2/5,1/15,2/3; thus (1) yields

    D(Potts)<=171+2/3=515/3.

Substitute these safe estimates into the stress identity:

    D <= 9/4 +(3403/4563)(351/4)
             +(25/6)(515/3)+(25/26)(215855/13)
       = 25,474,585/1521
       < 16749.

Thus no C2 quotient class of U has integral grade16749 or higher.
This bound can be improved substantially by computing the actual
module C2 quotients, but no such computation is needed for finiteness.

## Consequence and limitation

Homogeneous representatives for U/C2(U), and therefore a finite
strong generating set for U, can be chosen in weights at most16748.
This result concerns the actual spaces U_n. It supplies neither an
identification of those spaces with the certified bounded-word
spans S_n nor a maximum intermediate grade for words in the original
weak generators. In particular it does not repair the false general
claim that closing the weight-one and weight-two singular products
prevents later words from creating new currents.

## A finite algebraic properness criterion that the bound does give

Although it does not bound weak-word excursions, the bound D=16748
does reduce properness to a finite polynomial feasibility problem.
For each1<=j<=D choose an unknown finite list G_j of vectors in the
known ambient B_j, allowing redundant or zero entries. At most dimB_j
entries are needed in each degree. Set G_1 to the six certified K
currents, and require the original weight-two generators, including
omega_B, to be in the span of G_2 and the known strong monomials of
weight two. One may impose PCT stability by using real coordinates
in PCT-real ambient bases.

Let N_w(G) be the finite span of normal-ordered products of
derivatives of the chosen vectors, of total weight w. For every pair
a in G_i,b in G_j impose

    a_n b belongs to N_(i+j-n-1)(G)
    for 0<=n<=i+j-1.

Only ambient spaces through weight2D-1 are used. Membership can be
written with auxiliary scalar coefficients as polynomial equations:
the ambient mode products are fixed bilinear maps, and each strong
monomial is polynomial in the unknown generator coordinates.

The usual strong-closure argument now shows that the span of all
normal-ordered products and derivatives is a vertex subalgebra W.
One proves closure under singular products by induction using the
commutator/iterate identities, since every singular product has
weight strictly below the sum of its two input weights; derivatives
and normal ordering provide the remaining operations. All n>=0
products are required here, including n=0. Checking only n>=1 would
not suffice.

This W contains the original generators and omega_B, hence U subset
W subset B. Its weight-one space is exactly K_1 because normal
ordering and differentiation of positive-weight generators cannot
create any additional weight-one vector. Thus a solution proves
properness. Conversely, if U is proper, choose homogeneous C2
representatives of U in degrees<=D and add its prescribed generators;
the C2 bound supplies a solution with W=U.

This is a finite algebraic equivalence, not a practical computation
proposal: the ambient spaces near weight2D are far beyond the
resource limits. It can become useful only if a much smaller strong
generating set is found and its singular-product closure is verified.
