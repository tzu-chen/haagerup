# A rank-two ambient inclusion has no intermediate nontrivial commutant restriction

The properness assumption on a restricted quantum operation can be derived
in the finite rational current-frame setting used here. The key is the
actual commutant identity, rather than the polynomial satisfied by a
restricted map. Neither a pointed current algebra nor a normal pair is
needed for the following lemma.

## 1. Exact hypotheses

Let W subset B be a finite local inclusion of simple, unitary, strongly
rational VOAs, compatible with the finite-index conformal-net setting.
Assume its vacuum representation as a W-module has the form

    B = W direct sum X,

where X is a nonvacuum simple W-module. Equivalently, the connected
inclusion has dim End_W(B)=2. Put I=[B:W]=1+dim_W X.

Let H subset W be a simple unitary rational conformal subalgebra for its
own stress tensor. Define the actual commutants

    D0=Com(H,W),    DB=Com(H,B).

Require D0 and DB to be strongly rational and H tensor D0 subset W to
be a finite local conformal extension. In the E8 applications H is the
actual affine algebra with a rational radical-lattice completion inside
W. The compatible restricted expectation gives finite index for
D0 subset DB; passage from that statement to strongly rational VOA
representation theory is part of the explicit unitary VOA/net bridge.
The argument does not prove this bridge from a formal operation on
characters or from a merely linear VOA map.

Then exactly one of the following occurs:

    (a) DB=D0;
    (b) DB=D0 direct sum Y, with Y simple and nonvacuum,
        [DB:D0]=I.

In case(b), the canonical rank is two. If the ambient inclusion comes
from a proper two-element hypergroup, and the operation restricts as a
vacuum-preserving normal UCP map with the given fixed algebra, then its
nontrivial residual operation is proper as well.

## 2. The commutant identity makes induction fully faithful

Set T=H tensor D0 and let A=W be its connected commutative extension
algebra in Rep(T). Decompose A over the distinct simple H-modules:

    A = direct sum_i H_i tensor M_i.

The multiplicity space for H_i=H is exactly D0, by its definition as
Com(H,W). In particular the H-vacuum block is H tensor D0, with no
additional D0 module. This assertion is about the whole vacuum module
H, not just the one-dimensional total conformal-weight-zero space.

For a D0-module Y, let

    F(Y)=Ind_A(1_H tensor Y)

in the semisimple category of right A-modules. Free induction and
Frobenius reciprocity, in the conventions reviewed in
[McRae, Section3.1](https://arxiv.org/pdf/2107.06577), give

    Hom_A(F(Y),F(Z))
      = Hom_T(1_H tensor Y, A tensor (1_H tensor Z))
      = Hom_D0(Y,Z).                                      (1)

All nonvacuum H_i terms vanish in the middle expression. Hence F is
fully faithful: a simple Y induces to a simple object, and different
simple D0-modules induce to different objects. At this point the right
A-modules are not asserted to be local.

Adjunction applied to the local W-module B gives

    Hom_A(F(Y),B)
      = Hom_T(1_H tensor Y,B)
      = Hom_D0(Y,DB).                                    (2)

Thus a simple Y occurs in DB precisely with its induced multiplicity
in B. Whenever it occurs, F(Y) is a submodule of the local object B
and is therefore local. This supplies locality exactly where used.

## 3. Two ambient constituents leave only two possibilities

The vacuum D0 induces to W. Its multiplicity is one. Every nonvacuum
simple constituent Y of DB must, by(1)--(2), induce to the only other
simple W-constituent X. Distinct constituents cannot both do so, and
the multiplicity of Y cannot exceed the multiplicity one of X.

If there is no nonvacuum constituent then DB=D0. Otherwise

    DB=D0 direct sum Y,    F(Y)=X.                        (3)

Normalized quantum dimension in the A-module category satisfies
dim_A F(Y)=dim_T(1_H tensor Y)=dim_D0 Y. On the local objects this is
the W quantum dimension. Equation(3) therefore yields

    [DB:D0]=1+dim_D0 Y=1+dim_W X=I.                      (4)

This proves the lemma without a norm argument, a dimension-field
assumption, a mirror equivalence, or a simple-current decomposition
of W. Those arguments in the earlier
[abelian normal-pair note](hi_cft_third_abelian_normal_pair_index.md)
and [integral-branching note](hi_cft_third_e8_integral_branching_properness.md)
give consistent stronger structural information but are unnecessary
for this dichotomy.

## 4. Canonical rank and the actual residual operation

For finite-index local-net inclusions the canonical and dual canonical
endomorphism spaces have equal dimension by Frobenius reciprocity.
[Bischoff, Corollary4.2 and Proposition4.10](https://arxiv.org/pdf/1608.00253)
identify the multiplicity-free canonical sectors and their extreme
vacuum-preserving operations. A proper two-element ambient hypergroup
therefore gives the assumed decomposition B=W direct sum X.

In the nontrivial residual case, (3) similarly gives canonical rank two.
For the Haagerup quotient, put d=(3+sqrt(13))/2 and I=1+d^2.
The residual operation x has expectation

    E=(id+d^2 x)/I.

Since the residual index is I, the coefficient of the identity in the
canonical Haar expectation is 1/I. There is only one other canonical
extreme operation y. Thus E=(id+(I-1)y)/I and x=y. This proves
properness of the actual restricted operation, rather than merely
existence of some two-element hypergroup with the same fixed algebra.

There is no contradiction with the earlier convex-combination examples:
those produce standalone operations obeying the quadratic relation.
They do not supply a compatible finite rational H tensor D0 extension
inside a rank-two ambient inclusion with D0 exactly Com(H,W).

## 5. Application to the E8 current-host program

Keep the standing hypotheses E=V_E8, B=E^alpha, W subset B, with
[E:B]=3 and [B:W]=I. Choose the actual rational current frame H inside
W. The ordinary fixed-algebra field arguments already exclude DB=D0
in the hosts below: if DB=D_E^alpha this is itself an ordinary cyclic
fixed algebra of the ambient commutant D_E. No lifting of a later
automorphism is required for this trivial-residual case.

* Host0: DB is the actual rank-two lattice V_(L_B), whether alpha acts
  trivially or nontrivially on D_E. The nontrivial branch is proper by
  the lemma and is excluded by the
  [complete proper abelian theorem](hi_cft_third_e8_proper_abelian_exclusion.md).
  Thus the stated rational E8 realization cannot have abelian W1 of
  dimension six, even without assuming properness of restriction.
* Hosts496 and613: the
  [simultaneous-alpha audit](hi_cft_third_alpha_commutants.md) proves
  DB=D_E for every relevant placement. The lemma reduces them to the
  [proper pointed obstruction](hi_cft_third_e8_pointed_hosts.md), which
  excludes both. The independent integral-branching proof is a useful
  alternative check.
* Host379: the [full simultaneous-alpha argument](hi_cft_third_e8_host379_alpha.md)
  proves that every allowed alpha fixes D_E=K(A2,2), so DB=D_E.
  The lemma and the
  [categorical obstruction](hi_cft_kA2_hypergroup_obstruction.md) exclude
  that simultaneous realization.
* Host600: the [full simultaneous-alpha argument](hi_cft_third_alpha_host600.md)
  proves that every allowed alpha fixes its Ising-times-C3 commutant.
  The same conclusion follows from the
  [Ising-times-C3 obstruction](hi_cft_ising_c3_hypergroup_audit.md).

The simultaneous-alpha arguments concern the full VOA commutants,
including lattice and other extension fields. They supply the actual
domains required by the categorical obstructions; equality of the
central charges or of the weight-one fixed spaces alone would not.

All conclusions concern the specified unitary finite-index E8 realization.
They do not establish an identification with the lattice H3 chain or
determine its central charge. The root, integrability, and
strange-correlator agents independently checked the algebraic dichotomy,
including the right-module/locality distinction and the complete
H-vacuum block. No numerical work is used.
