# Universal current-trace consequences: gamma1 and the gamma0 level60 branch

15 September2026. Exact algebra under the strongly regular unitary VOA
premises below. No computation was run by this author. ROOT and
CFT_constraints independently audited the key identities and representation
arguments; a separate bounded certificate records the finite bookkeeping.

**Conclusion.** There is no strongly regular unitary c8 VOA with actual
Haagerup-center modular representation and the gamma1 character
(dimW1=19). For the gamma0 character(dimW1=6), every simple A1 current
factor has level at most39, excluding the principal level60 host33.
The stronger radical and product constraints below give a universal
lower bound40/17 on the central charge of a current-generated coset
of such W.
These conclusions use neither rationality of a residual coset nor a
properness assumption for a restricted hypergroup action. They are
statements about this rational chiral VOA realization, not a direct
identification or exclusion of a nonrational lattice-chain continuum.

## 1. Primary inputs and normalization

The exact trace-space construction, source transcription and first
executed certificate are in
[the flavoured-trace audit](hi_cft_third_flavoured_trace_audit.md).
Its primary inputs are
[Krauel–Mason Theorem1](https://arxiv.org/pdf/1103.0994),
[Evans–Gannon equations(1.24),(2.7)](https://arxiv.org/pdf/1006.1326),
and the independently matched weight-two dimension formula.
The S matrix is the actual twelve-module modular representation,
not just a choice acting on the linearly dependent unflavoured
characters. Haagerup S²=1 makes all these modules selfcontragredient.

[Dong–Mason, Corollaries4.1 and4.3](https://arxiv.org/pdf/math/0601569)
give the reductive weight-one Lie algebra, positive integral affine
levels, and integrability of every W-module for each affine factor.
The positive Cartan rational form and rational charges on every
module follow from [Mason, Sections8–11](https://arxiv.org/pdf/1110.0544),
especially equations(19),(25),(28). For the radical specifically,
Theorem3 and Remark4 give an actual positive-definite lattice VOA
whose weight-one space is the radical. Modules restrict to ordinary
modules of that regular lattice VOA, with real dual-lattice charges.
Multiples of lattice vectors have integral eigenvalues on every W
module and span its radical real form. Thus their quadratic charge
traces are positive semidefinite. No arbitrary irrational Cartan
subspace is asserted to contain a lattice. No positive-energy bound
for complementary module conformal weights is used in the final
global gamma1 proof.

Write Q0 for the trace of u0² on W1 and Qc,Q1,Q4,Q5 for its trace
on the c1,d1,d4,d5 ground spaces in EG's order. Let kappa=u_1u.
For a simple factor g_k, Q0/kappa=2hdual/k. In an A1 factor,
the ordinary SU2 indices of dimensions1,2,3 are0,1,4;
the affine normalization divides each by k.

## 2. Two exact identities on the full trace space

The three rational basis vectors of holomorphic M2(rho) in the saved
[certificate](hi_cft_third_flavoured_trace_results.json) all satisfy

    v0+9vc1−vd5=0,
    v0+9vc1+vd1+3vd4=0,
    vd6+vd1−2vd4=0.                               (1)

For gamma1 the particular quadratic trace is

    E2 chi_gamma1/12 + D chi_gamma0/4
                        +(13/28)D(chi_gamma1−chi_gamma0).

Its two functional values are6 and8. For gamma0 the particular trace
is simply E2 chi_gamma0/12+D chi_gamma0/4, because only the vacuum
has a negative q exponent. Its relevant coefficients are

    Qpart0=−1/2, Qpartc=1/4,
    Qpart1=21/26, Qpart4=25/52, Qpart5=7/4,

giving functional values0 and4. Therefore every current obeys

    gamma1: Q0+9Qc−Q5=6 kappa,
            Q0+9Qc+Q1+3Q4=8 kappa;                 (2)

    gamma0: Q0+9Qc−Q5=0,
            Q0+9Qc+Q1+3Q4=4 kappa.                 (3)

Writing Q6 for the d6 ground trace, the third identity is
Q6+Q1−2Q4=2 kappa for gamma0, and4 kappa for gamma1.

These relations concern designated coefficients at different modular
exponents. They are not equal-weight trace sums. Equation(1) on the
complete M2 basis and the particular constants certify that no
uncomputed modular parameter can alter them.

## 3. Immediate restrictions for gamma1

The relevant ground dimensions are c1:3, d1:6, d4:2, d5:8;
their weights are1/3,6/13,5/13,7/13 respectively.

### Radical rank at most one

For a current in the abelian radical, Q0=0. The first identity(2)
gives the quadratic-form identity

    9Qc−Q5=6 kappa.

Since Q5 is positive semidefinite, Qc is positive definite on the
radical. But the selfdual three-dimensional c1 ground has abelian
weight multiset{0,lambda,−lambda}, or only zeros; its quadratic
trace has rank at most one. The positive current metric therefore
forces radical rank at most one. This argument is made on the real
Cartan with self-adjoint zero modes and extends to all directions by
polarization; no integrality of an arbitrarily chosen real direction
is needed beyond the spanning Jacobi cocharacters.

### A1 requires nontrivial c1 action and forbids a radical

For A1_k the first identity gives

    4+9t_c−t_5=6k,

where t_c,t_5 are nonnegative ordinary SU2 indices. Because k>=1,
t_c cannot vanish. Thus on the three-dimensional c1 ground the A1
representation is either2+1 or3. In either case its multiplicity
commutant is abelian, so a second commuting A1 cannot act nontrivially.
Consequently there is at most one A1 simple factor.

Moreover a commuting radical current acts scalarly on each of these
multiplicity-one SU2 types. Each SU2 type is selfdual. Selfduality
of the full c1 representation pairs its radical charge with its
negative within the same SU2 type, forcing every such scalar charge
to zero. The radical trace Qc then vanishes, contradicting the
positive identity above for any nonzero radical current. Thus an
A1 simple factor and a nonzero radical cannot coexist.

This argument deliberately allows2+1. It requires no Frobenius–Schur
indicator calculation or extra claim about symmetry of the module form.

### An A2 factor cannot coexist with A2 or B2

A nontrivial A2 representation on the dimension3 c1 ground would be
3 or3bar, which is incompatible with selfduality without its partner.
Thus c1 is A2-neutral. The first identity gives6−t_5=6k;
nonnegative t_5 and positive integral k force k=1 and t_5=0.
The dimension2 d4 ground is also neutral, so the second identity
requires index2 on d1.

The finite A2 types of dimension at most6 are1,3,3bar,6,6bar.
The latter pair cannot occur in a selfdual space of total dimension6.
Index2 therefore forces the selfdual d1 ground to be exactly3+3bar.
Its A2 multiplicity spaces are both one-dimensional. Every commuting
second A2 acts trivially, contradicting its own required d1 index2.

A commuting B2 likewise acts trivially on d1. Its c1 and d4 actions
are automatically trivial from their dimensions3 and2. The second
identity for B2_k would then read6/k=8, impossible for a positive
integer k. This excludes the A2+B2 combination without a B2 affine
energy bound or unitarizability assumption for every module.

## 4. Exhaustion of all reductive Lie algebras of dimension19

By the classification of finite-dimensional complex simple Lie algebras,
the only simple dimensions below20 are3(A1),8(A2),10(B2=C2),14(G2),
15(A3). The next classical cases B3/C3 have dimension21 and A4 has24.
With radical rank r<=1 the dimension equation is

    3a+8b+10c+14d+15e+r=19.

Its complete nonnegative solutions give exactly five types:

| Lie algebra | obstruction already proved |
|---|---|
|B2+A1³|at most one A1 factor|
|A2²+A1|two A2 factors impossible|
|A1⁶+U1|A1 cannot coexist with a radical|
|B2+A2+U1|A2 cannot commute with B2|
|A3+A1+U1|A1 cannot coexist with a radical|

This exhausts W1, proving the gamma1 conclusion without an embedding
catalog or a conjectural commutant classification. ROOT independently
enumerated the same five cases; the tiny source repeats the finite
integer equation as a bookkeeping certificate.

## 5. Gamma0 excludes every A1 level greater than39

For gamma0 the c1,d1,d4 ground dimensions are3,7,5. Multiplying the
positive identity(3) by the affine level k gives

    4+9t_c+t_1+3t_4=4k.

The ordinary SU2 index of the irreducible dimension d representation
is d(d²−1)/6. For a direct sum of total dimension d this is an upper
bound, since the cubic function is superadditive on positive integers.
Therefore

    t_c<=4, t_1<=56, t_4<=20,
    4k<=4+36+56+60=156,
    k<=39.

The principal A1_60 host33 is excluded as a current algebra of this
gamma0 W. This route does not assume rationality or C2-cofiniteness
of the principal D5/A1 coset; that separate coset question remains
unresolved in the earlier audit.

The third trace identity also gives a useful gamma0 radical bound.
For a radical current set A=Qc,B=Q1,C=Q4,D=Q6. Then

    9A+B+3C=4 kappa,   D=−B+2C+2 kappa
                            =(9A−B+7C)/2 >=0.

On a vector in the common kernel of A and C, the first equality gives
B=4 kappa and the second gives D=−2 kappa, a contradiction. Thus
the radical embeds into the combined charge support of c1 and d4,
whose ranks are at most1 and2. The radical rank is at most3, ruling
out the six-dimensional abelian current algebra.

If gamma0 W1=A1_k+U1³, equality of these support ranks requires A and
C to have ranks1 and2. In the3D and5D grounds, charge pairs of a
nontrivial SU2 type consume at least twice that type's dimension.
Achieving the full respective ranks therefore forces both grounds
to be SU2-neutral. The positive identity becomes t_1=4(k−1).
Enumerating the15 ordinary SU2 representation partitions of dimension7
gives indices0,1,2,3,4,5,6,8,10,11,14,20,21,35,56. Only those divisible
by4 can equal4(k−1), so

    k in {1,2,3,6,15}.                              (4)

This necessary set uses neither a Frobenius–Schur sign nor a module
energy inequality. The certificate separately checks the symmetric
ground representation subset and obtains the same levels. Any further
filter using total ground energy versus affine Sugawara energy must
state its separate unitary-module/positive-coset premise.

### Two A1 factors and the universal current-coset floor

The only other reductive Lie algebra of dimension6 allowed after
radical rank<=3 is A1_(k1)+A1_(k2). Summing the positive trace
identities gives

    4(k1+k2)=8+9 sum(t_c)+sum(t_1)+3 sum(t_4).

For an irreducible product representation of dimensions a,b, the
sum of its ordinary indices is b t(a)+a t(b), where t(n)=n(n²−1)/6.
It is at most t(ab), because

    t(ab)−b t(a)−a t(b)=ab(a²−1)(b²−1)/6>=0.

Superadditivity treats direct sums. Applying the same dimensions3,7,5
therefore gives k1+k2<=40. Concavity of3k/(k+2) makes the maximum
full Sugawara charge occur at k1=k2=20, with complementary charge

    c_full-current-coset >=8−2(60/22)=28/11.

For A1_k+U1³, equation(4) gives k<=15 and hence

    c_full-current-coset >=8−3−45/17=40/17.

The third dimension6 possibility U1⁶ was excluded by the PSD rank
bound. Thus40/17 is the lower bound over every possible gamma0
current algebra. Passing to a smaller current-generated denominator
cannot increase its Sugawara central charge and cannot decrease the
coset charge. This last statement is the standard unitary current
subalgebra Sugawara comparison inside W, and makes no assertion about
unitarity of arbitrary complementary modules. The bound concerns
current-generated cosets; it does not constrain every possible
non-current denominator or every CFT carrying a Haagerup symmetry.

## 6. Exact source and execution scope

`hi_cft_third_flavoured_universal_check.py` is separate from all frozen
numerical files. It hash-verifies the executed exact trace record and
its original producer, checks both functionals on every M2 basis
vector, independently derives the gamma0 particular coefficients from
the published characteristic matrix, checks constants(0,4),(6,8),
and enumerates all five small Lie-dimension solutions. It also checks
the SU2 dimension-index upper bound, the third PSD identity, both
seven-dimensional SU2 index lists, the level-sum bound and the
resulting exact rational current-coset minima.
The analytic representation arguments remain stated in this note,
not disguised as outputs of the integer enumeration.

Only standard-library arithmetic and an input below128KiB are used.
Total process estimate64MiB; first AS guard128MiB and10second alarm.
The author performed only AST parsing. ROOT owns execution:

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_flavoured_universal_obstruction.md --audit-json hi_cft_third_flavoured_universal_guard.json -- python hi_cft_third_flavoured_universal_check.py --output hi_cft_third_flavoured_universal_results.json

The final finite-representation-only global proof was independently
reviewed by Strange in
[its audit](hi_cft_third_gamma1_independent_audit.md), and by ROOT and
CFT_constraints. It supersedes the preliminary standalone B2 argument
that used an affine-versus-total module energy inequality.
