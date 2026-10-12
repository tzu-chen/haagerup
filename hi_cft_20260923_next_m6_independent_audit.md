# Independent audit of the two Z3+6 exclusions

23 September 2026. Read-only algebra and source review; no numerical job.
The balanced exclusion and the universal weighted-character projection
both pass. These arguments use the positive canonical spherical structure
of the actual modular VOA category, not a C* classification.

## Balanced induction pattern

In the p=q=1 pattern the normalized positive vacuum row is

    (b,a,1/3 [three times],1/6 [four times],n_j sqrt(3)/12),
    b=(2-sqrt(3))/12, a=(2+sqrt(3))/12, sum n_j^2=22.

A cyclotomic Galois automorphism reversing sqrt(3) has positive value a
at S00. The normalized signed Galois theorem therefore selects the
unique label X of this vacuum-row value, with positive sign. It forces
the entire X row to be (a,b,1/3,1/6,-n_j sqrt(3)/12). This theorem applies
to general modular categories: see [Dong--Lin--Ng, Theorem II(iii)]
(https://msp.org/ant/2015/9-9/ant-v9-n9-p03-s.pdf).
No assumed unitarizability enters.

Uniqueness of the dimension also makes X self-dual. Its Verlinde
coefficient is consequently

    N_XX^X = a^3/b+b^3/a + 3/9+4/36-22/48 = 4/3.

The arithmetic follows from a+b=1/3 and ab=1/144. Thus this pattern is
impossible. The induction dimensions are those in [Larson, Section 4]
(https://arxiv.org/pdf/1401.1879), under the pointed-associator hypothesis
already established for the actual boundary category.

## Remaining pattern and moment argument

For p=0,q=2, split off the nondegenerate pointed Z3 factor with twist
zeta^2. Its centralizer M has anomaly i, known labels 1,X,Y of dimensions
1,2d+1,2+2d, twists 1,1,zeta, and remaining dimensions n_j d, where
d=3+2sqrt(3), n_j positive integers and sum n_j^2=6.

The first Gauss moment is -2-4i. The second indicator moment is
-2+4i(1-epsilon). The choice epsilon=-1 has modulus sqrt(68)>6 and is
impossible. For epsilon=1,

    sum n_j^2 (1+Re z_j)(1+Im z_j)
      =6+Re(-2-4i)+Im(-2-4i)+(1/2)Im(-2)=0.

Every summand is nonnegative, so z_j is -1 or -i. Their squared
multiplicities are respectively 2 and 4. No inference that all n_j=1
is needed or justified; one n_j=2 at twist -i is allowed at this stage.

## Closure of the weighted character projection

For each pointed label use

    v0=chi_1-chi_X,
    vA=-(1/2) sum_(z=-i) n_j chi_j,
    vB=-sum_(z=-1) n_j chi_j.

The Galois-forced X row gives f=S v0=-v0/2-vA-vB/2. Put U=S vA,
V=S vB. As v0 is self-dual, S^2 v0=v0. Applying the categorical
relation STS=i T^(-1) S T^(-1), with T=(1,-i,-1), gives

    U+V/2 = -v0-f/2,
    iU+V/2 = -i v0/2+vA+i vB/2+f/2.

These independent vector equations hold in the entire character space,
so their solution rules out components outside this projection:

    S vA=-v0/2+vB/2,
    S vB=-v0/2+vA-vB/2.

Thus the block is exactly -1/2 times [[1,2,1],[1,0,-1],[1,-2,1]].
Tensoring the pointed factor and including the c=8 scalar in character
T gives the representation used in the previous harmonic-theta proof.
The calculation does not presume independence of simple characters.

Dimensions and twists are constant on dual labels. Hence each weighted
sum is stable under duality, and the sums at pointed charges +1 and -1
are equal by contragredience. Averaging these two charges does not
introduce half-integral polar coefficients. The quarter-pole coefficient
is -A/2 with A=sum n_j dim(top_j), and the half-pole coefficient is -P
with P=sum n_j dim(top_j); each is a nonnegative integer before the
displayed coordinate normalization. Count zero for a lowest weight
above the polar range.

## Consequence and exact scope

The pole lists, lattice theta coefficients, and constant-remainder
argument in
`hi_cft_20260923_next_structure_m6_character_obstruction.md` apply
unchanged. In the original orientation the only additional poles have
h=1/4 and imply dim U1=8+A. In the reverse orientation they have h=1/6
and imply dim U1=5+12P. Neither permits dim U1=6.

The original orientation has only one T-fixed coordinate before the eta
multiplier; S does not preserve its line. The reverse orientation has
no T-fixed coordinate. Thus in both cases pole cancellation leaves no
invariant constant. The finite-image property of the modular
representation makes the pole-free weight-zero remainder constant
on its finite-index kernel; no uniqueness of arbitrary weight-four
modular forms was assumed.

Therefore both p=q=1 and p=0,q=2 are excluded for the actual proper
rank-four Z3+6 alternative. This establishes a universal exclusion in
the stated pseudounitary setting without identifying the complete
modular data or invoking a C* near-group classification. It does not
establish properness of U in B.
