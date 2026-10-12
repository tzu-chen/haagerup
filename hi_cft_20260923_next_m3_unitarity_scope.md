# The m=3 near-group exclusion: unitarity scope and reverse module bridge

23 September 2026. Source audit and algebra only; no numerical job.

The character calculation in
`hi_cft_20260923_next_structure_m3_character_obstruction.md` excludes the
two specified Izumi--Xu center ribbon categories at c=8 with dimU1=6.
Identifying an arbitrary pseudo-unitary near-group category of type
(Z3,3) with those C*-categories needs an additional theorem.

## 1. What the classification actually classifies

[Larson, Theorem1.1](https://arxiv.org/html/1401.1879) classifies the
possible based rings of pseudo-unitary rank-four categories with a dual
pair. It does not classify associators on the (Z3,3) ring.
[Evans--Gannon](https://arxiv.org/html/1208.1500) develops its corresponding
classification in the C*-setting. The scope is stated explicitly in
[Tucker, Section4, p.349](https://msp.org/pjm/2019/303-1/pjm-v303-n1-p13-p.pdf):
the m=|G| classification there concerns unitary near-group categories.
The same paper's Section5 separately describes the removal of unitarity
by Leavitt-algebra methods for Haagerup--Izumi categories. Those are
different fusion rings; this does not remove the near-group hypothesis.

This audit found no source proving that every pseudo-unitary
(Z3,3) categorification is unitarizable or algebraically equivalent to
one of the classified C*-categories. This is a limitation of the verified
sources, not a claim that no such theorem can exist.

The actual finite-index net inclusion N_U subset N_H does give a unitary
fusion category F_net. The same actual H branching and intertwiner spaces
give rank4 or rank6 on the net side. However, the algebraic category
F=Rep(U)_H and F_net cannot simply be identified from their common
linear branching data. Such an identification would compare the tensor
products and is precisely part of the VOA/net comparison problem.

## 2. A new source does supply the reverse module direction

[Henriques--Tener, arXiv2507.20735v3](https://arxiv.org/html/2507.20735)
(10 October2025) supplies substantially more than the older correspondence
literature. Its TheoremB/8.9 recovers an AQFT-local unitary VOA from its
net. TheoremC/9.5 and Corollary9.7 construct the corresponding unitary
module from a net representation and identify its closed smeared fields.
Remark9.8 permits infinite-dimensional energy eigenspaces, and even
general rotation spectrum, by using an admissible weak module.

Here the recovered vacuum VOA is the actual U, since U is strongly local
as a unitary subVOA of the lattice VOA. Combining their reverse construction
with regularity gives the following useful consequence.

**Claim.** Every irreducible representation of N_U reconstructs an
irreducible ordinary unitary U-module. Consequently, finite direct sums
give a fully faithful linear *-functor

    Rep_net(N_U) -> Rep_unitary(U).

The assertion here is linear, not tensorial. Here is the projection
argument, including the finite-energy issue.

* Start with the dense admissible weak U-module M supplied by
  Remark9.8 on the bounded-energy vectors of the net representation K.
  Its Virasoro zero mode is the net rotation generator, by the argument
  of Corollary9.6 and the field compatibility retained in Remark9.8.
* Regularity of U decomposes M algebraically into ordinary simple
  modules. Choose one nonzero summand S. The inherited positive form
  makes S a unitary module. Let P be the Hilbert orthogonal projection
  onto its closure in K.
* Since S has finite-dimensional eigenspaces, its Hilbert closure has
  exactly the same individual energy eigenspaces as S. Thus P sends
  bounded-energy vectors into S, so P preserves M. The unitary adjoint
  identities show on M that P commutes with every U mode: test the
  equality against S and use invariance of S under the adjoint modes.
* P and 1-P preserve the common core M and commute there with the
  smeared fields. Therefore they commute with their closures and
  adjoints. Theorem9.5 identifies those closures with the net's fields,
  which generate its local algebras. Hence P is a net intertwiner.
* Irreducibility gives P=1. Finite-dimensionality of each S energy
  space then implies M=S, so the reconstructed module is ordinary and
  simple. In particular, the potentially infinite multiplicity allowed
  in Remark9.8 disappears in this application.

For two such simple modules an algebraic module isomorphism is unitary
up to a scalar, since their invariant positive forms are unique up to
scale. It therefore extends boundedly and, by the same common-core
argument, intertwines the nets. Finite direct sums give full faithfulness.
The construction preserves the conformal Hamiltonian and thus conformal
weights, characters and twists. In particular,

    number of simple net sectors <= number of simple U-modules,

and each net-sector character is an actual ordinary U-character.

This deduction uses the explicit module extension in HT Remark9.8.
It does not rest merely on the theorem whose displayed hypotheses ask
for finite-dimensional energy eigenspaces.

## 3. What this new bridge still does not state

HT Section9 proves module reconstruction and field compatibility. It
does not state that reconstruction preserves Connes fusion, the VOA
tensor product, braiding, or the genus-one S matrix. A fully faithful
linear *-functor and preservation of L0 do not imply any of those facts.
Its image is not thereby shown to contain every simple U-module or to
be closed under VOA fusion.

Thus the two possible shortcuts remain unsupported:

    F_net unitary  =>  F unitary,
    S_net known    =>  the U character vector transforms by S_net.

The characters of the reconstructed net sectors lie among the U
characters, whose full span is modular invariant by VOA theory. The
subset itself need not yet be shown invariant, and its transformation
matrix need not yet be identified with net categorical S.

For comparison, [Gui, Theorem3.39 and its proof](https://binguimath.github.io/Files/2020_Strong-Braiding.pdf)
uses a braided C*-tensor embedding to identify quantum dimensions and
then transfer essential surjectivity. Its conditionA assumption on U
is stronger than the reverse linear functor above. Gui's newer
[extension comparison, arXiv2505.03235](https://arxiv.org/abs/2505.03235)
starts from an appropriate known conformal subalgebra and ascends to
extensions; the current inclusion U subset H has the wrong direction
to invoke that theorem directly.

Accordingly, the m3 character exclusion is presently unconditional
for the two explicitly specified centers, and conditional for every
pseudo-unitary (Z3,3) category. It becomes an exclusion of the whole
m3 branch once one proves either algebraic classification of that
branch, unitarizability of F, a suitable tensor comparison, or direct
character covariance with the classified net S matrix.
