module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Algebra.Module.Torsion.Field
public import HaagerupIzumi.C8.Fusion.Pivotal

@[expose] public section

/-! # Monoidal automorphisms of the identity functor, and pivotal uniqueness

Categorical half of the pivotal-uniqueness paragraph in the proof of Proposition
`prop:optional-algebraic-identification` (manuscript
`c8_expanded_20260929/haagerup_c8_expanded.tex`, lines 4109–4115): "A pivotal structure on
any categorification of this ring is unique when it exists.  Indeed, the ratio of two such
structures is a tensor automorphism of the identity.  Write its scalar on a simple `Z` as
`t_Z`. ... Thus all six scalars are one."  The based-ring half (a multiplicative function
on the six simples of `eq:rank6-ring` is identically one) is
`Fusion.IsHIRing.pivotal_unique` (`Fusion/Pivotal.lean`).  Here we connect it to monoidal
natural transformations.

A monoidal automorphism of the identity is `η : 𝟭 C ≅ 𝟭 C` with
`[NatTrans.IsMonoidal η.hom]` (Mathlib's notion, for the identity functor with its
canonical monoidal structure).  `isMonoidal_iff` shows that this class says exactly
`η_𝟙 = 𝟙` and `η_{X ⊗ Y} = η_X ⊗ η_Y`.

* `app_tensor`, `app_unit`, `isMonoidal_iff`: the two defining equations.
* `exists_unit_smul_id` (Schur): over an algebraically closed field `𝕜`, on a simple `X`
  with finite-dimensional `End X`, `η_X = t_X • 𝟙` with `t_X ∈ 𝕜ˣ`.
* `mul_eq_of_hom_ne_zero`: if `η_X = s • 𝟙`, `η_Y = t • 𝟙`, `η_Z = u • 𝟙` and there is a
  nonzero `f : Z ⟶ X ⊗ Y` (that is, `N_{XY}^Z ≠ 0`), then `s * t = u` (naturality at `f`
  and monoidality).
* `app_eq_id_of_iso_biproduct`: an endotransformation of `𝟭 C` that is the identity on
  the summands `S j` is the identity on every object isomorphic to `⨁ S`.
* `Fusion.IsHIRing.monoidalAut_app_eq_id`: for simples `X i` realizing the rank-six ring
  of `IsHIRing`, every monoidal automorphism of `𝟭 C` is the identity on each `X i`
  (`pivotal_unique` with `G = 𝕜ˣ`); `Fusion.IsHIRing.monoidalAut_eq_refl`: it is the
  identity if every object is a finite direct sum of the `X i`.
* `Fusion.IsHIRing.monoidalIso_app_eq`, `Fusion.IsHIRing.monoidalIso_eq`: two monoidal
  natural isomorphisms `p q : 𝟭 C ≅ F` to any lax monoidal functor `F` agree on the
  `X i`, and are equal under the same direct-sum hypothesis.  The ratio
  `p ≪≫ q.symm` is a monoidal automorphism of `𝟭 C` (Mathlib instances), so this
  step of the manuscript is proved, not assumed.

Inputs that remain hypotheses (no external theorem or certificate is used):

* Pivotal structures themselves.  A pivotal structure is a monoidal natural isomorphism
  `𝟭 C ≅ (−)**` (EGNO, Definition 4.7.8).  Mathlib has no pivotal categories
  (`Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean` lists them as future work).  The
  uniqueness theorems here are stated for an arbitrary lax monoidal `F : C ⥤ C`; the monoidal
  double-dual functor is constructed in `Category/DoubleDual.lean`, and the instantiation
  (`PivotalStructure`, `Fusion.IsHIRing.pivotalStructure_eq`) is `Category/Pivotal.lean`.
* That the categorification realizes the ring: the `X i` are simple with
  finite-dimensional endomorphisms, and `N_{ij}^l ≠ 0` is witnessed by a nonzero
  morphism `X l ⟶ X i ⊗ X j` (in a semisimple category
  `N_{ij}^l = dim Hom(X_l, X_i ⊗ X_j)`).  For the statements about the whole functor,
  also that every object is a finite direct sum of the `X i` (semisimplicity with the
  `X i` a complete list of simples).
-/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace MonoidalAutomorphism

section Monoidal

variable [MonoidalCategory C]

/-- Monoidality of `η : 𝟭 C ⟶ 𝟭 C` on tensor products: `η_{X ⊗ Y} = η_X ⊗ η_Y` (the
tensorators of `𝟭 C` are identities). -/
theorem app_tensor (η : 𝟭 C ⟶ 𝟭 C) [NatTrans.IsMonoidal η] (X Y : C) :
    η.app (X ⊗ Y) = η.app X ⊗ₘ η.app Y := by
  have h := NatTrans.IsMonoidal.tensor (τ := η) X Y
  simpa using h

/-- Monoidality of `η : 𝟭 C ⟶ 𝟭 C` on the unit: `η_𝟙 = 𝟙`. -/
theorem app_unit (η : 𝟭 C ⟶ 𝟭 C) [NatTrans.IsMonoidal η] :
    η.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  have h := NatTrans.IsMonoidal.unit (τ := η)
  simpa using h

/-- For an endotransformation of the identity functor, Mathlib's `NatTrans.IsMonoidal` is
exactly the pair of equations `η_𝟙 = 𝟙` and `η_{X ⊗ Y} = η_X ⊗ η_Y`. -/
theorem isMonoidal_iff (η : 𝟭 C ⟶ 𝟭 C) :
    NatTrans.IsMonoidal η ↔
      η.app (𝟙_ C) = 𝟙 (𝟙_ C) ∧ ∀ X Y : C, η.app (X ⊗ Y) = η.app X ⊗ₘ η.app Y := by
  constructor
  · intro h
    exact ⟨app_unit η, app_tensor η⟩
  · rintro ⟨hu, ht⟩
    exact
      { unit := by simp [hu]
        tensor := fun X Y => by simp [ht] }

end Monoidal

section Biproduct

variable [HasZeroMorphisms C]

/-- An endotransformation of `𝟭 C` that is the identity on each summand `S j` is the
identity on every object isomorphic to the biproduct `⨁ S` (naturality at the
projections and at the isomorphism). -/
theorem app_eq_id_of_iso_biproduct (η : 𝟭 C ⟶ 𝟭 C) {J : Type*} (S : J → C)
    [HasBiproduct S] (hS : ∀ j, η.app (S j) = 𝟙 (S j)) {Y : C} (e : Y ≅ ⨁ S) :
    η.app Y = 𝟙 Y := by
  have hB : η.app (⨁ S) = 𝟙 (⨁ S) := by
    refine biproduct.hom_ext _ _ (fun j => ?_)
    have h := η.naturality (biproduct.π S j)
    rw [hS j] at h
    simpa using h.symm
  have h := η.naturality e.hom
  rw [hB] at h
  have h2 := congrArg (· ≫ e.inv) h.symm
  simpa using h2

end Biproduct

section Schur

variable (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜] [Preadditive C] [Linear 𝕜 C] [HasKernels C]

/-- Schur's lemma for an automorphism of the identity functor: on a simple `X` with
finite-dimensional endomorphisms, `η_X = t_X • 𝟙 X` for a nonzero scalar `t_X`. -/
theorem exists_unit_smul_id (η : 𝟭 C ≅ 𝟭 C) (X : C) [Simple X]
    [FiniteDimensional 𝕜 (X ⟶ X)] : ∃ t : 𝕜ˣ, η.hom.app X = (t : 𝕜) • 𝟙 X := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id 𝕜 (X := X) (η.hom.app X)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have h : 𝟙 X = @CategoryStruct.comp C _ X X X (η.hom.app X) (η.inv.app X) :=
      (η.hom_inv_id_app X).symm
    rw [← hc, Limits.zero_comp] at h
    exact id_nonzero X h
  exact ⟨Units.mk0 c hc0, hc.symm⟩

end Schur

section Linear

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear 𝕜 C]

/-- Tensor product of scalar endomorphisms: `(s • 𝟙) ⊗ (t • 𝟙) = (s t) • 𝟙`. -/
theorem smul_id_tensorHom_smul_id (s t : 𝕜) (X Y : C) :
    (s • 𝟙 X) ⊗ₘ (t • 𝟙 Y) = (s * t) • 𝟙 (X ⊗ Y) := by
  rw [tensorHom_def, MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
    id_whiskerRight, whiskerLeft_id, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul]

/-- The scalars of a monoidal endotransformation of `𝟭 C` are multiplicative along fusion
channels: if `η` acts on `X`, `Y`, `Z` by `s`, `t`, `u` and there is a nonzero morphism
`Z ⟶ X ⊗ Y`, then `s * t = u`. -/
theorem mul_eq_of_hom_ne_zero (η : 𝟭 C ⟶ 𝟭 C) [NatTrans.IsMonoidal η] {X Y Z : C}
    {s t u : 𝕜} (hX : η.app X = s • 𝟙 X) (hY : η.app Y = t • 𝟙 Y)
    (hZ : η.app Z = u • 𝟙 Z) (f : Z ⟶ X ⊗ Y) (hf : f ≠ 0) : s * t = u := by
  have h2 : η.app (X ⊗ Y) = (s * t) • 𝟙 (X ⊗ Y) := by
    rw [app_tensor η X Y, hX, hY]
    exact smul_id_tensorHom_smul_id 𝕜 s t X Y
  have h := η.naturality f
  rw [h2, hZ] at h
  have hnat : f ≫ ((s * t) • 𝟙 (X ⊗ Y)) = (u • 𝟙 Z) ≫ f := h
  rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] at hnat
  exact smul_left_injective 𝕜 hf hnat

end Linear

end MonoidalAutomorphism

open MonoidalAutomorphism

section HI

variable (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜] [Preadditive C] [Linear 𝕜 C] [HasKernels C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pivotal uniqueness, categorical form (lines 4109–4115): let `X i` be simple objects with
finite-dimensional endomorphisms, indexed by the six simples of a based ring `R` with
`IsHIRing R a ρ ρ₁ ρ₂ m`, such that every nonzero fusion coefficient `N_{ij}^l` is
witnessed by a nonzero morphism `X l ⟶ X i ⊗ X j`.  Then every monoidal automorphism of
the identity functor is the identity on each `X i`.  (Schur gives scalars `t_i ∈ 𝕜ˣ`,
multiplicative along fusion channels by `mul_eq_of_hom_ne_zero`, hence trivial by
`IsHIRing.pivotal_unique`.) -/
theorem Fusion.IsHIRing.monoidalAut_app_eq_id {R : Fusion.BasedRing ι} {a ρ ρ₁ ρ₂ : ι}
    {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m) (X : ι → C) [∀ i, Simple (X i)]
    [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    (η : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal η.hom] (i : ι) :
    η.hom.app (X i) = 𝟙 (X i) := by
  choose t ht using fun i => exists_unit_smul_id 𝕜 η (X i)
  have h1 := H.pivotal_unique t (fun i j l hl => by
    obtain ⟨f, hf⟩ := hN i j l hl
    exact Units.ext (by
      rw [Units.val_mul]
      exact mul_eq_of_hom_ne_zero 𝕜 η.hom (ht i) (ht j) (ht l) f hf))
  rw [ht i, h1 i, Units.val_one, one_smul]

/-- If moreover every object of `C` is a finite direct sum of the `X i` (semisimplicity,
with the `X i` a complete list of simples), every monoidal automorphism of the identity
functor is the identity. -/
theorem Fusion.IsHIRing.monoidalAut_eq_refl [HasFiniteBiproducts C] {R : Fusion.BasedRing ι}
    {a ρ ρ₁ ρ₂ : ι} {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m) (X : ι → C)
    [∀ i, Simple (X i)] [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    (hss : ∀ Y : C, ∃ (n : ℕ) (k : Fin n → ι), Nonempty (Y ≅ ⨁ fun j => X (k j)))
    (η : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal η.hom] : η = Iso.refl (𝟭 C) := by
  refine Iso.ext (NatTrans.ext (funext fun Y => ?_))
  obtain ⟨n, k, ⟨e⟩⟩ := hss Y
  exact app_eq_id_of_iso_biproduct η.hom (fun j => X (k j))
    (fun j => H.monoidalAut_app_eq_id 𝕜 X hN η (k j)) e

/-- Uniqueness of monoidal natural isomorphisms out of the identity functor on the simples
of the rank-six ring: for any lax monoidal `F : C ⥤ C`, two monoidal natural isomorphisms
`p q : 𝟭 C ≅ F` agree on each `X i`.  With `F` the double-dual functor these are pivotal
structures (EGNO, Def. 4.7.8), so this is pivotal uniqueness (lines 4109–4115); the ratio
`p ≪≫ q.symm` is a monoidal automorphism of `𝟭 C`. -/
theorem Fusion.IsHIRing.monoidalIso_app_eq {R : Fusion.BasedRing ι} {a ρ ρ₁ ρ₂ : ι}
    {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m) (X : ι → C) [∀ i, Simple (X i)]
    [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    {F : C ⥤ C} [F.LaxMonoidal] (p q : 𝟭 C ≅ F) [NatTrans.IsMonoidal p.hom]
    [NatTrans.IsMonoidal q.hom] (i : ι) : p.hom.app (X i) = q.hom.app (X i) := by
  have : NatTrans.IsMonoidal (p ≪≫ q.symm).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (p.hom ≫ q.inv))
  have h := H.monoidalAut_app_eq_id 𝕜 X hN (p ≪≫ q.symm) i
  have h' : p.hom.app (X i) ≫ q.inv.app (X i) = 𝟙 _ := h
  calc p.hom.app (X i) = (p.hom.app (X i) ≫ q.inv.app (X i)) ≫ q.hom.app (X i) := by simp
    _ = q.hom.app (X i) := by rw [h', Category.id_comp]

/-- Two monoidal natural isomorphisms `p q : 𝟭 C ≅ F` are equal when every object is a finite
direct sum of the `X i`.  For `F` the double dual: a categorification of the rank-six ring
has at most one pivotal structure. -/
theorem Fusion.IsHIRing.monoidalIso_eq [HasFiniteBiproducts C] {R : Fusion.BasedRing ι}
    {a ρ ρ₁ ρ₂ : ι} {m : ℕ} (H : Fusion.IsHIRing R a ρ ρ₁ ρ₂ m) (X : ι → C)
    [∀ i, Simple (X i)] [∀ i, FiniteDimensional 𝕜 (X i ⟶ X i)]
    (hN : ∀ i j l, R.N i j l ≠ 0 → ∃ f : X l ⟶ X i ⊗ X j, f ≠ 0)
    (hss : ∀ Y : C, ∃ (n : ℕ) (k : Fin n → ι), Nonempty (Y ≅ ⨁ fun j => X (k j)))
    {F : C ⥤ C} [F.LaxMonoidal] (p q : 𝟭 C ≅ F) [NatTrans.IsMonoidal p.hom]
    [NatTrans.IsMonoidal q.hom] : p = q := by
  have : NatTrans.IsMonoidal (p ≪≫ q.symm).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (p.hom ≫ q.inv))
  have h := H.monoidalAut_eq_refl 𝕜 X hN hss (p ≪≫ q.symm)
  have h' : p.hom ≫ q.inv = 𝟙 (𝟭 C) := congrArg Iso.hom h
  refine Iso.ext ?_
  calc p.hom = (p.hom ≫ q.inv) ≫ q.hom := by simp
    _ = q.hom := by rw [h', Category.id_comp]

end HI

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.MonoidalAutomorphism.isMonoidal_iff
#print axioms HaagerupIzumi.C8.MonoidalAutomorphism.exists_unit_smul_id
#print axioms HaagerupIzumi.C8.MonoidalAutomorphism.mul_eq_of_hom_ne_zero
#print axioms HaagerupIzumi.C8.MonoidalAutomorphism.app_eq_id_of_iso_biproduct
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.monoidalAut_app_eq_id
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.monoidalAut_eq_refl
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.monoidalIso_app_eq
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.monoidalIso_eq
