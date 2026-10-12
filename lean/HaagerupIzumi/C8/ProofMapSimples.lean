module

public import HaagerupIzumi.C8.ProofMap
public import HaagerupIzumi.C8.ProofMapConcreteCharacters
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The simple `U`-modules, before and after their identification with the twelve labels

The branching, top-bound and projective-vacuum arrows of Appendices F–G are stated for *all*
simple ordinary `U`-modules, before the manuscript knows how many there are.  Here they are
indexed by an arbitrary type `Simp` with their lowest weights, top dimensions and the class of `U`
itself (`SimpleData`).  Only after the modular data (GSY Theorem A(2), node `modularData`,
line 4053) are the simples identified with the twelve labels `Characters.Label` of the character
table (`SimpleLabels`, an input conditional on `modularData`); this identification is used only
where label-specific facts are needed (the characters and the strong-unitarity count).

That `Simp` is finite (`[Fintype Simp]`) and that the lowest weights are rational (`SD.hw : Simp →
ℚ`) are known before `modularData`: [external] `C₂`-cofiniteness (node `c2Cofinite`) gives a
finite-dimensional Zhu algebra, hence finitely many simple ordinary modules (Zhu; Dong–Li–Mason),
whose conformal weights are rational (Dong–Li–Mason; Miyamoto); eq:top-trace (line 2949) shows
directly that they are real and nonnegative.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Characters

/-- The isomorphism classes `Simp` of simple ordinary `U`-modules: their lowest weights, top
dimensions, and the class of `U` itself. -/
structure SimpleData (Simp : Type*) where
  /-- The lowest weight of the simple module `s`. -/
  hw : Simp → ℚ
  /-- The dimension of the lowest space of `s`. -/
  td : Simp → ℕ
  /-- The class of the vacuum module `U`. -/
  vac : Simp

/-- **[manuscript step] The twelve simples after GSY** (Theorem A(2), line 4053; node
`modularData`): the simple `U`-modules are the twelve modules of the character table, i.e. `Simp`
is identified with `Characters.Label`, compatibly with the lowest weights, top dimensions and the
vacuum ([definitional]: `C.hw l`, `C.td l` are the lowest weight and top dimension of the module
labelled `l`, and `o` labels `U`).  The identification respects the twists: the label `l` carries
the twist `e^{2πi t_l}` (`t_l = twistExp l`) of the modular data, the module `s` the twist
`e^{2πi SD.hw s}` (`θ = e^{2πiL(0)}`, Huang), and `C.hw l ∈ t_l + ℤ` (`CharacterInputs.low`). -/
structure SimpleLabels {Simp : Type*} (md : Prop) (SD : SimpleData Simp) (C : CharacterData) where
  /-- [manuscript step] GSY Theorem A(2): the simples are the twelve labelled modules. -/
  ident : md → Simp ≃ Label
  /-- [definitional] compatibility with the lowest weights. -/
  hw : ∀ (h : md) (s : Simp), C.hw (ident h s) = SD.hw s
  /-- [definitional] compatibility with the top dimensions. -/
  td : ∀ (h : md) (s : Simp), C.td (ident h s) = SD.td s
  /-- [definitional] the label `o` is the vacuum module `U`. -/
  vac : ∀ h : md, ident h SD.vac = .o

theorem card_label : Fintype.card Label = 12 := rfl

/-- After the identification there are exactly twelve simple `U`-modules. -/
theorem SimpleLabels.card {Simp : Type*} [Fintype Simp] {md : Prop} {SD : SimpleData Simp}
    {C : CharacterData} (L : SimpleLabels md SD C) (h : md) : Fintype.card Simp = 12 :=
  (Fintype.card_congr (L.ident h)).trans card_label

#print axioms SimpleLabels.card

end HaagerupIzumi.C8.ProofMap
