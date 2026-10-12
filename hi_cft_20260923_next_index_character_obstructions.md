# Index and character constraints after strong rationality

23 September 2026. Bounded algebra/primary-source audit; no numerical
job was launched by the author. This note does not supply a new exclusion
of the remaining rank-four m=3,6 cases or rank-six multiplicity m>=2.

## What the numerical VOA invariants do imply

In the proper case c=8, dim U_1=6, every nonvacuum simple has
0<h<=17/10, and qdim_U(B)=s. Positivity gives

    S_00 = 1/(3s),  Glob(U)=9s^2.

This converts an index upper bound into a lower bound on S_00, but does
not supply that lower bound. Effective-central-charge results bound the
Lie rank by c_eff=8; the present rank two easily satisfies this. They do
not state an upper bound on global dimension in terms of c and h_max.
See [Dong--Mason](https://arxiv.org/abs/math/0201318).

The twist identity theta_M=exp(2*pi*i*h_M) alone also gives no exclusion:
every root of unity has a strictly positive representative h<=1 (using
h=1 for twist one), which fits 17/10. The genuine constraints are that
these representatives must occur in one common character vector, with
nonnegative integral graded dimensions, the prescribed vacuum, and
the known branching identities. The assertion that a root-of-unity
order is bounded by h_max would be false.

## The known mixed character does not distinguish the rank-four cases

The mixed B character is

    chi_mix = chi_(E6,27) chi_(A2,3),

with lowest weight one and top dimension81. Its equality with the
simple U-character chi_Y gives the complete function, not only its
first coefficient. This initially suggests comparing its modular orbit
with the candidate centers, but both surviving rank-four cases already
realize that same function in known conformal embeddings.

For m=3, the Izumi--Xu center is realized by G2_3 tensor A2_1 and
G2_3 embeds conformally into E6_1. Both nonvacuum E6 modules restrict to
the same simple G2 module of lowest weight2/3 and top dimension27.
See [Evans--Gannon](https://arxiv.org/html/1208.1500), introduction, and
[Bischoff--Kawahigashi--Longo, Example5.8](https://ems.press/content/serial-article-files/26302?nt=1).

For m=6, put W=(A2_9 extended by its order-three simple currents)
tensor A2_1. The first factor embeds in E6_1. In
[Yu, Lemmas3.1,3.4 and Proposition3.5](https://arxiv.org/html/2312.12195v2),
the object Y4 has dimension s=8+4sqrt(3), twist exp(4*pi*i/3), and an
S-row supported only on 1,Y4,Y5. Pairing Y4 with the two nontrivial
A2_1 objects gives the twist-one conjugate pair Y,Y*. The E6 fundamental
branch is (2,2)+(2,5)+(5,2), hence exactly Y4. The branching formula is
also displayed in the preceding Example5.8. Thus these Y characters
again equal chi_mix identically.

This is a precise obstruction to excluding these cases by the modular
orbit of chi_Y alone. Categorically the branching map from Rep(B)
already provides its small invariant modular subspace. It is incorrect
to treat all irreducible characters as linearly independent: conjugate
modules and these conformal branchings give actual dependencies.

The affine comparison VOAs have current dimensions22 (m=3) and16
(m=6), whereas the proper U has dimension6. This distinction may exclude
their categories only after a separate character or VOA uniqueness
argument. Braided equivalence of representation categories is not such
a uniqueness theorem.

## A concrete finite character test, with its missing input

For any fixed candidate modular representation (S,T), use c=8 and
T_ii=exp(2*pi*i*(h_i-1/3)). Choose all possible lifts
0<h_i<=17/10, with h_0=0. There are at most two lifts for each nonvacuum
twist. The polar part can occur only at h_i<1/3, including the prescribed
vacuum term q^(-1/3). Its coefficients are the unknown positive integer
top dimensions of the selected polar modules. Impose in addition

    chi_U=q^(-1/3)(1+6q+...),
    chi_X=chi_B-chi_U,
    chi_Y=chi_mix,

and all known extension/branching identities. Weight-zero vector-valued
modular forms with this fixed bounded polar behavior form a finite
dimensional space. A principal-part construction reduces the problem
to linear conditions and coefficient inequalities; invariant constant
vectors, if present, must also be included. Relevant primary methods are
[Bantay--Gannon](https://arxiv.org/abs/0705.2467) and
[Gannon](https://arxiv.org/abs/1310.4458).

A finite collection of Fourier-coefficient inequalities can rigorously
exclude a candidate if it is infeasible. Passing a finite collection
does not prove that all later coefficients are nonnegative, nor that a
VOA exists. Also, finite dimensionality does not by itself prove there
are finitely many integral choices for all polar coefficients; one needs
actual bounding inequalities. Neither reconstruction nor the required
inequalities have been computed in this note.

For the rank-six quadratic family, the fusion ring and its formal
codegrees alone do not yet specify S,T. A character test would first
need a center classification for the higher multiplicities, or a
proved universal index bound. No such bound was verified here.

## A current literature result that applies only after m=1

[Gannon--Schopieray--Yadav, Theorem A(2)](https://arxiv.org/html/2609.25185)
(submitted21 September2026) states the center modular data for spherical
untwisted cyclic Haagerup--Izumi categories. In the positive N=3 case,
the metric-group parameter has prime order13, and its quadratic form
is determined up to isometry. This gives the standard Haagerup modular
data once our multiplicity is proved to be one. The defining fusion
rule in that paper already has multiplicity one, so it must not be used
to exclude the higher-multiplicity quadratic alternatives.
