module

public import HaagerupIzumi.C8.Category.DoubleDual
public import HaagerupIzumi.C8.Category.MonoidalAutomorphism

@[expose] public section

/-! # Pivotal structures, and their uniqueness on categorifications of the rank-six ring

Pivotal-uniqueness paragraph in the proof of Proposition
`prop:optional-algebraic-identification` (manuscript
`c8_expanded_20260929/haagerup_c8_expanded.tex`, lines 4109–4115): "A pivotal structure on
any categorification of this ring is unique when it exists.  Indeed, the ratio of two such
structures is a tensor automorphism of the identity. ..."

Mathlib has no pivotal categories.  Using the monoidal double-dual functor of
`Category/DoubleDual.lean` (`DoubleDual.doubleDual C`, `X ↦ Xᘁᘁ`, with tensorator
`DoubleDual.μIso` and unit `DoubleDual.εIso`), we define:

* `PivotalStructure C`: a pivotal structure on a right rigid monoidal category (EGNO,
  Definition 4.7.8): a natural isomorphism `a : 𝟭 C ≅ (−)ᘁᘁ` that is monoidal
  (`NatTrans.IsMonoidal`) for the monoidal structure of the double dual.  `app_unit` and
  `app_tensor` unpack monoidality: `a_𝟙 = εIso` and `a_{X ⊗ Y} = (a_X ⊗ a_Y) ≫ μ_{X,Y}`.
* `PivotalStructure.ratio p q = p.iso ≪≫ q.iso.symm : 𝟭 C ≅ 𝟭 C`, with an instance
  showing that it is a monoidal automorphism of the identity (the manuscript's "the ratio of
  two such structures is a tensor automorphism of the identity").
* `Fusion.IsHIRing.pivotalStructure_app_eq`: two pivotal structures agree on the simples
  realizing the rank-six ring; `Fusion.IsHIRing.pivotalStructure_eq` and
  `Fusion.IsHIRing.subsingleton_pivotalStructure`: **a categorification of `eq:rank6-ring`
  has at most one pivotal structure**.  These instantiate `Fusion.IsHIRing.monoidalIso_eq`
  (`Category/MonoidalAutomorphism.lean`: Schur and multiplicativity along fusion channels;
  the based-ring computation `Fusion.IsHIRing.pivotal_unique` is in `Fusion/Pivotal.lean`)
  with `F` the double dual.

Hypotheses (no external theorem or certificate is used): `C` is right rigid
(`RightRigidCategory C`, so `Xᘁᘁ` is the chosen right dual of the chosen right dual),
preadditive, `𝕜`-linear over an algebraically closed field with linear whiskering, has
kernels; the categorification realizes the ring through simple objects `X i` with
finite-dimensional endomorphism algebras such that every `N_{ij}^l ≠ 0` is witnessed by a
nonzero morphism `X l ⟶ X i ⊗ X j` (in a semisimple category
`N_{ij}^l = dim Hom(X_l, X_i ⊗ X_j)`); for the global statements, every object is a finite
direct sum of the `X i`.  Not formalized: existence of a pivotal structure (the manuscript
only uses uniqueness), sphericality, and the comparison with left duals.
-/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Limits DoubleDual

universe v u

/-- A pivotal structure on a right rigid monoidal category (EGNO, Definition 4.7.8): a
monoidal natural isomorphism from the identity functor to the double-dual functor. -/
structure PivotalStructure (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] where
  /-- The natural isomorphism `a_X : X ≅ Xᘁᘁ`. -/
  iso : 𝟭 C ≅ doubleDual C
  /-- `a` is monoidal: `a_𝟙 = εIso` and `a_{X ⊗ Y} = (a_X ⊗ a_Y) ≫ μ_{X,Y}`. -/
  [isMonoidal : NatTrans.IsMonoidal iso.hom]

attribute [instance] PivotalStructure.isMonoidal

namespace PivotalStructure

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Pivotal structures are determined by their underlying natural isomorphism. -/
theorem ext' {p q : PivotalStructure C} (h : p.iso = q.iso) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Monoidality on the unit: `a_𝟙 = εIso`. -/
theorem app_unit (p : PivotalStructure C) : p.iso.hom.app (𝟙_ C) = (εIso C).hom := by
  have h : 𝟙 (𝟙_ C) ≫ p.iso.hom.app (𝟙_ C) = (εIso C).hom :=
    NatTrans.IsMonoidal.unit (τ := p.iso.hom)
  rwa [Category.id_comp] at h

/-- Monoidality on tensor products: `a_{X ⊗ Y} = (a_X ⊗ a_Y) ≫ μ_{X,Y}`. -/
theorem app_tensor (p : PivotalStructure C) (X Y : C) :
    p.iso.hom.app (X ⊗ Y) = (p.iso.hom.app X ⊗ₘ p.iso.hom.app Y) ≫ (μIso X Y).hom := by
  have h : 𝟙 (X ⊗ Y) ≫ p.iso.hom.app (X ⊗ Y) =
      (p.iso.hom.app X ⊗ₘ p.iso.hom.app Y) ≫ (μIso X Y).hom :=
    NatTrans.IsMonoidal.tensor (τ := p.iso.hom) X Y
  rwa [Category.id_comp] at h

/-- The ratio of two pivotal structures, `a ≫ b⁻¹ : 𝟭 C ≅ 𝟭 C`. -/
def ratio (p q : PivotalStructure C) : 𝟭 C ≅ 𝟭 C := p.iso ≪≫ q.iso.symm

/-- The ratio of two pivotal structures is a monoidal (tensor) automorphism of the identity
functor. -/
instance ratio_isMonoidal (p q : PivotalStructure C) : NatTrans.IsMonoidal (ratio p q).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (p.iso.hom ≫ q.iso.inv))

/-- Two pivotal structures with trivial ratio are equal. -/
theorem eq_of_ratio_eq_refl {p q : PivotalStructure C} (h : ratio p q = Iso.refl (𝟭 C)) :
    p = q := by
  refine ext' (Iso.ext ?_)
  have h' : p.iso.hom ≫ q.iso.inv = 𝟙 (𝟭 C) := congrArg Iso.hom h
  calc p.iso.hom = (p.iso.hom ≫ q.iso.inv) ≫ q.iso.hom := by simp
    _ = q.iso.hom := by rw [h', Category.id_comp]

end PivotalStructure

section HI

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜] [Preadditive C] [Linear 𝕜 C] [HasKernels C]
  [MonoidalPreadditive C] [MonoidalLinear 𝕜 C]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pivotal uniqueness on simples (lines 4109–4115): two pivotal structures on a category
whose simples `X i` realize the rank-six ring `IsHIRing R a ρ ρ₁ ρ₂ m` agree on each `X i`. -/
theorem Fusion.IsHIRing.pivotalStructure_app_eq {R : Fusion.BasedRing ι} {a ρ ρ₁ ρ₂ : ι}
    {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m) (X : ι → C) [∀ i, Simple (X i)]
    [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    (p q : PivotalStructure C) (i : ι) : p.iso.hom.app (X i) = q.iso.hom.app (X i) :=
  H.monoidalIso_app_eq 𝕜 X hN p.iso q.iso i

/-- **Pivotal uniqueness** (lines 4109–4115): if moreover every object is a finite direct sum
of the `X i`, any two pivotal structures are equal. -/
theorem Fusion.IsHIRing.pivotalStructure_eq [HasFiniteBiproducts C] {R : Fusion.BasedRing ι}
    {a ρ ρ₁ ρ₂ : ι} {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m) (X : ι → C)
    [∀ i, Simple (X i)] [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    (hss : ∀ Y : C, ∃ (n : ℕ) (k : Fin n → ι), Nonempty (Y ≅ ⨁ fun j => X (k j)))
    (p q : PivotalStructure C) : p = q :=
  PivotalStructure.ext' (H.monoidalIso_eq 𝕜 X hN hss p.iso q.iso)

/-- A categorification of `eq:rank6-ring` has at most one pivotal structure. -/
theorem Fusion.IsHIRing.subsingleton_pivotalStructure [HasFiniteBiproducts C]
    {R : Fusion.BasedRing ι} {a ρ ρ₁ ρ₂ : ι} {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m)
    (X : ι → C) [∀ i, Simple (X i)] [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    (hss : ∀ Y : C, ∃ (n : ℕ) (k : Fin n → ι), Nonempty (Y ≅ ⨁ fun j => X (k j))) :
    Subsingleton (PivotalStructure C) :=
  ⟨H.pivotalStructure_eq 𝕜 X hN hss⟩

end HI

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PivotalStructure.ext'
#print axioms HaagerupIzumi.C8.PivotalStructure.app_unit
#print axioms HaagerupIzumi.C8.PivotalStructure.app_tensor
#print axioms HaagerupIzumi.C8.PivotalStructure.ratio_isMonoidal
#print axioms HaagerupIzumi.C8.PivotalStructure.eq_of_ratio_eq_refl
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.pivotalStructure_app_eq
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.pivotalStructure_eq
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.subsingleton_pivotalStructure
