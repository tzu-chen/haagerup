# Universal character projection for the remaining Z3+6 case

Status: independently audited by exact_grade4, including both moment
identities, twist support, weighted modular closure, both orientations,
and integrality of the polar coefficients. The
balanced p=q=1 case is excluded separately by Verlinde integrality.
The argument below uses only pseudounitarity and the actual B extension.
It does not identify a category from its modular data.

Write d=3+2 sqrt(3), r=1+d, s=2r, and take
zeta=exp(2 pi i/3). In the p=0,q=2 induction pattern, the two dimension-one
central objects, together with the unit, form a pointed nondegenerate
category P with twists 1,zeta^2,zeta^2. Hence Z(F)=P tensor M. The
opposite choice of zeta conjugates the following formulas.

The distinguished X of dimension 2d+1 belongs to M: tensoring by the two
pointed objects gives exactly the other two objects of this dimension,
whose twists are zeta^2. Thus their monodromy with X is trivial. Likewise
the three objects of dimension s give one M object Y with twist zeta.
The known M simples therefore have

    dimensions (1,2d+1,s), twists (1,1,zeta).

Every other M simple has dimension n_j d for an integer n_j>=1. Pointed
factorization acts freely on the corresponding center triples, so the
center dimension identity gives sum n_j^2=6. The anomaly of M is i,
because that of the center is1 and that of P is -i. Its positive
normalization is sqrt(Dim M)=2 sqrt(3) r.

Let z_j be the remaining twists. Its Gauss sum and the center's second
indicator equation give respectively

    sum n_j^2 z_j   = -2-4i,
    sum n_j^2 z_j^2 = -2+4i(1-epsilon), epsilon=nu_2(rho) in {+1,-1}.

For the second identity directly, the known part of theta^2 on I(rho)
has trace Dim F+2i sqrt(3)d. The pointed twist-square sum is i sqrt(3),
and Dim F/d=4 sqrt(3). These give the displayed formula. The epsilon=-1
right side has modulus sqrt(68)>6, so epsilon=+1.

Now each (1+Re z_j)(1+Im z_j) is nonnegative and

    sum n_j^2(1+Re z_j)(1+Im z_j)
      =6-2-4+(1/2)Im(-2)=0.

Every remaining twist is consequently -1 or -i. Their total squared
multiplicities are two and four respectively. This allows either four
dimension-d objects or one dimension-2d object at twist -i. The argument
below works for both possibilities, so no exhaustion by a rank-nine
model is being assumed.

Put a=(2 sqrt(3)-3)/12, b=(2 sqrt(3)+3)/12. The normalized vacuum row of
M is

    (a,b,1/sqrt(3),n_j/4).

Galois conjugation sqrt(3)->-sqrt(3) maps this row to minus the X row,
because sigma(a)=-b and X is the unique object of its dimension in M.
Thus the X row is

    (b,a,1/sqrt(3),-n_j/4).

For each pointed factor label define the following character combinations:

    v0=chi_1-chi_X,
    vA=-(1/2) sum_(z_j=-i) n_j chi_j,
    vB=-sum_(z_j=-1) n_j chi_j.

The first two rows force

    S v0 = -v0/2-vA-vB/2 =: f.

These three combinations are fixed by duality, since dimensions and
twists are unchanged by duality. Hence S^2 v0=v0. Also T fixes v0,
multiplies vA by -i, and multiplies vB by -1. The modular relation
S T S = i T^(-1) S T^(-1) supplies a second independent equation:

    S vA+(1/2)S vB = -v0-f/2,
    i S vA+(1/2)S vB = -i v0/2+vA+i vB/2+f/2.

Solving yields

    S vA=-v0/2+vB/2,
    S vB=-v0/2+vA-vB/2.

Thus, without any assertion about the other rows of S, these characters
carry the same three-dimensional representation used in the earlier
m6 theta obstruction:

    S_v=-1/2 [[1,2,1],[1,0,-1],[1,-2,1]],
    T_v=diag(1,-i,-1).

Tensor this with the pointed P factor, then average its two dual labels.
This is the reverse orientation in
`hi_cft_20260923_next_structure_m6_character_obstruction.md`. Conjugation
gives its original orientation. The actual extension satisfies
chi_1+chi_X=chi_B, so its vacuum coefficient extraction is unchanged.

For the original orientation the polar coefficient in vA is -A/2, with

    A=sum_(quarter-twist labels) n_j dim(top_j)>=0 integer,

counting zero when the lowest weight is shifted past the polar range.
The same harmonic-theta subtraction therefore gives dim U1=8+A>=8.
For the reverse orientation the half-twist weighted sum enters vB;
the earlier coefficient calculation gives dim U1=5+12P, with P a
nonnegative integer. This again cannot equal six. These are statements
about an actual character projection, not linear independence of all
simple characters. The proof of finite-image pole cancellation and the
absence of invariant constants is unchanged in that earlier note.

Primary categorical inputs are Larson, Section4 (center induction),
the ordinary modular Gauss-sum and Verlinde/Galois identities, and
Mueger factorization by a nondegenerate pointed subcategory. Source
links and the normalized Galois theorem are recorded in the balanced
exclusion note. All theta coefficients and lattice discriminant forms
are recorded in the earlier character-obstruction note.
