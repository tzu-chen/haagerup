module

public import HaagerupIzumi.C8.Category.LminusEnvelope

@[expose] public section

/-! # Monoidal comparison on the homogeneous objects of `L₋`

The braided monoidal functor `a ↦ S (a, -a)` of `Lminus_braided_vec` (from the symmetric
discrete `ℤ/3`, i.e. the homogeneous lines `δ_a` of the untwisted `Vec_{ℤ/3}`) lands in the
additive closure `LminusClosure S`, and it is braided monoidal **for the monoidal structure of
`LminusClosure S`** (`lminusClosure_isMonoidal`) and its inherited braiding.  This is the
monoidal comparison between the untwisted `Vec_{ℤ/3}` and the additive closure of `L₋` on the
degree-homogeneous rank-one objects.

* `liftCoreMonoidal`, `liftBraided`: a (braided) monoidal functor `F : D ⥤ C` whose values lie in
  a monoidal full subcategory `P` lifts to a (braided) monoidal functor `D ⥤ P` with the same
  tensorator and unit (generic).
* `Lminus_closure_braided_functor`: under `hSchur`, `hfusion`, `hunitS` and **[external]** `hθ`,
  there is a braided monoidal functor `G : Discrete (Multiplicative (ZMod 3)) ⥤ LminusClosure S`
  (source with Mathlib's braiding, symmetric by `discreteSymmetric`; target with the monoidal
  structure of `lminusClosure_isMonoidal`, symmetric by `lminusClosureSymmetric`) with
  `G (a) = S (a, -a)` and tensorator the trivializing isomorphisms `φ'`.

The extension to general graded objects (finite direct sums of the lines, matrices of scalars)
is proved elsewhere:
* `GrMat.Lminus_graded_braided_equivalence` (`Category/GradedMat.lean`), with the distributivity
  isomorphisms compatible with `φ'` componentwise (`GrMat.ι_μHom`);
* `Lminus_vec_braided_equivalence` (`Category/GradedMatMonoidal.lean`): a braided monoidal
  equivalence `Vec_{ℤ/3} ≃ LminusClosure S`;
* composed with free induction, `untwisted_vec_equivalence_of_separable`
  (`Category/UntwistedVecEquivalence.lean`). -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Limits Module

universe v u

namespace RightMod

section Generic

variable {D : Type*} [Category D] [MonoidalCategory D] {C : Type u} [Category.{v} C]
  [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal] (F : D ⥤ C)
  (hF : ∀ X, P (F.obj X))

/-- A monoidal functor with values in a monoidal full subcategory lifts to it. -/
@[simps]
noncomputable def liftCoreMonoidal (h : F.CoreMonoidal) : (P.lift F hF).CoreMonoidal where
  εIso := P.isoMk h.εIso
  μIso X Y := P.isoMk (h.μIso X Y)
  μIso_hom_natural_left f X' := by
    apply ObjectProperty.hom_ext
    exact h.μIso_hom_natural_left f X'
  μIso_hom_natural_right X' f := by
    apply ObjectProperty.hom_ext
    exact h.μIso_hom_natural_right X' f
  associativity X Y Z := by
    apply ObjectProperty.hom_ext
    exact h.associativity X Y Z
  left_unitality X := by
    apply ObjectProperty.hom_ext
    exact h.left_unitality X
  right_unitality X := by
    apply ObjectProperty.hom_ext
    exact h.right_unitality X

/-- A braided functor with values in a monoidal full subcategory lifts to a braided functor
(the subcategory carrying the inherited braiding). -/
@[instance_reducible]
noncomputable def liftBraided [BraidedCategory D] [BraidedCategory C] (h : F.CoreMonoidal)
    (hβ : ∀ X Y, (h.μIso X Y).hom ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ (h.μIso Y X).hom) :
    (P.lift F hF).Braided :=
  { (liftCoreMonoidal P F hF h).toMonoidal with
    braided := fun X Y => by
      apply ObjectProperty.hom_ext
      exact hβ X Y }

end Generic

section Lminus

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type*) [Field 𝕜]
  [Linear 𝕜 C] [MonoidalLinear 𝕜 C]

/-- **Monoidal comparison on the homogeneous lines**: a braided monoidal functor from the
symmetric discrete `ℤ/3` to the additive closure of `L₋` (with its own monoidal structure and
inherited braiding), sending `a` to `S (a, -a)`.  Inputs: `hSchur`, `hfusion`, `hunitS` and
**[external]** `hθ`. -/
theorem Lminus_closure_braided_functor (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) :
    haveI := lminusClosure_isMonoidal hfusion hunitS
    ∃ (G : Discrete (Multiplicative (ZMod 3)) ⥤ (LminusClosure S).FullSubcategory)
      (_ : G.Braided),
        ∀ a : ZMod 3, (G.obj (Discrete.mk (Multiplicative.ofAdd a))).obj = S (a, -a) := by
  have hM := lminusClosure_isMonoidal hfusion hunitS
  let S' : ZMod 3 → C := fun a => S (a, -a)
  have hEnd : ∀ a, finrank 𝕜 (S' a ⟶ S' a) = 1 := fun a => by
    show finrank 𝕜 (S (a, -a) ⟶ S (a, -a)) = 1
    rw [hSchur, if_pos rfl]
  let φ : ∀ a b : ZMod 3, S' a ⊗ S' b ≅ S' (a + b) := fun a b =>
    hfusion (a, -a) (b, -b) ≪≫ eqToIso (congrArg S (PointedCocycle.Lminus_add a b))
  obtain ⟨φ', hα, hβ⟩ := PointedCocycle.Lminus_untwisted_symmetric 𝕜 S' hEnd φ hθ
  let u : S' 0 ≅ 𝟙_ C := eqToIso (congrArg S (Prod.ext rfl neg_zero)) ≪≫ hunitS
  have hmem : ∀ X, LminusClosure S ((PointedCocycle.lminusFunctor S').obj X) := fun X =>
    ⟨1, fun _ => Multiplicative.toAdd X.as,
      ⟨(biproductUniqueIso (fun _ : Fin 1 =>
        S (Multiplicative.toAdd X.as, -Multiplicative.toAdd X.as))).symm⟩⟩
  refine ⟨(LminusClosure S).lift (PointedCocycle.lminusFunctor S') hmem,
    liftBraided (LminusClosure S) _ hmem
      (PointedCocycle.lminusCoreMonoidal 𝕜 S' hEnd φ' u hα) (fun X Y => ?_), fun a => rfl⟩
  show (φ' _ _).hom ≫ eqToHom (congrArg S' (add_comm (Multiplicative.toAdd X.as)
    (Multiplicative.toAdd Y.as))) = (β_ _ _).hom ≫ (φ' _ _).hom
  exact (hβ _ _).symm

end Lminus

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.liftCoreMonoidal
#print axioms HaagerupIzumi.C8.RightMod.liftBraided
#print axioms HaagerupIzumi.C8.RightMod.Lminus_closure_braided_functor
