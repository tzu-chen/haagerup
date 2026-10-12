module

public import HaagerupIzumi.C8.Category.LminusBraidedVec
public import HaagerupIzumi.C8.Category.FreeModuleMonoidalEquivalence
public import Mathlib.CategoryTheory.Preadditive.Mat

@[expose] public section

/-! # The additive closure of `L₋`: additive envelope and symmetric braiding

Continuation of `Category/LminusBraidedVec.lean` (the Tannakian step of `L_untwisted`, manuscript
`haagerup_c8_expanded.tex`, lines 3335–3337) at the level of the additive closure
`LminusClosure S` of the three invertibles `S (a, -a)` (`Category/FreeModuleEquivalence.lean`),
which is monoidal by `lminusClosure_isMonoidal` and braided by the braiding inherited from `C`
(Mathlib's `fullBraidedSubcategory`).

* **Additive envelope.**  `LminusSimple S` is the full subcategory of `C` on the objects
  `S (a, -a)`, a `𝕜`-linear category with `dim Hom(S (a,-a), S (b,-b)) = δ_{a,b}` (`hSchur`), i.e.
  the `𝕜`-linearization of the discrete `ℤ/3`.  `LminusEnvelope S = Mat_ (LminusSimple S)` is
  Mathlib's additive envelope of it (finite tuples of simples, matrices of morphisms).
  `envelopeFunctor S : LminusEnvelope S ⥤ LminusClosure S` (the biproduct realization,
  `Mat_.lift`) is **an equivalence of categories** (`envelopeFunctor_isEquivalence`): faithful
  and full because morphisms between biproducts are matrices (`biproduct.matrix`), essentially
  surjective by the definition of `LminusClosure`.  It is additive.
* **Symmetric braiding.**  `monodromy_natural`, `monodromy_biproduct`, `monodromy_of_iso`: the
  double braiding `β_{Y,X} ∘ β_{X,Y}` is natural and, if it is the identity on all pairs of
  summands, it is the identity on biproducts and on objects isomorphic to them.
  `lminusClosureSymmetric`: if the double braiding is trivial on the three simples, the
  inherited braiding on `LminusClosure S` is **symmetric** (`SymmetricCategory`).
* `Lminus_closure_symmetric_envelope`: under `hSchur`, `hfusion`, `hunitS` and **[external]**
  `hθ` (trivial self-braidings on `L₋`), the double braiding is trivial on the simples (from
  the trivialization `Lminus_untwisted_symmetric`), so `LminusClosure S` is a symmetric monoidal
  category, and it is equivalent (as a category) to the additive envelope of the
  `𝕜`-linearized discrete `ℤ/3`.

**Monoidal comparison** (proved elsewhere):
* the braided monoidal equivalence of the untwisted `Vec_{ℤ/3}` (graded matrices with the
  Kronecker tensor product) onto `LminusClosure S` is `GrMat.Lminus_graded_braided_equivalence`
  (`Category/GradedMat.lean`);
* with the canonical instances it is `Lminus_vec_braided_equivalence`
  (`Category/GradedMatMonoidal.lean`);
* composed with free induction it is `untwisted_vec_equivalence_of_separable`
  (`Category/UntwistedVecEquivalence.lean`).

`LminusEnvelope S` itself (Mathlib's `Mat_`) is not given a monoidal structure here.  The
envelope is built from the full subcategory of `C`, not from
`Discrete (Multiplicative (ZMod 3))` directly, because of the universe constraints of
`Free`/`Mat_.lift` (target in the same universes as the source).  The external input is `hθ`
(Huang's braiding on simple currents and `Weights.Lminus_symmetric_trivial_twists`). -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Limits Module

universe v u

namespace RightMod

section Envelope

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (S : ZMod 3 × ZMod 3 → C)

/-- The three simples of `L₋`, as a property of objects. -/
def LminusSimple : ObjectProperty C := fun X => ∃ a : ZMod 3, X = S (a, -a)

/-- The additive envelope of the linear category on the three simples of `L₋`. -/
abbrev LminusEnvelope := Mat_ (LminusSimple S).FullSubcategory

/-- The biproduct realization of the envelope in `C`. -/
noncomputable def envelopeToC : LminusEnvelope S ⥤ C := Mat_.lift (LminusSimple S).ι

theorem envelopeToC_obj (M : LminusEnvelope S) :
    (envelopeToC S).obj M = ⨁ fun i => (M.X i).obj := rfl

theorem envelopeToC_map {M N : LminusEnvelope S} (f : M ⟶ N) :
    (envelopeToC S).map f = biproduct.matrix fun i j => (f i j).hom := rfl

theorem envelopeToC_mem (M : LminusEnvelope S) : LminusClosure S ((envelopeToC S).obj M) := by
  choose a ha using fun i => (M.X i).property
  let e := Fintype.equivFin M.ι
  refine ⟨Fintype.card M.ι, fun j => a (e.symm j), ⟨?_⟩⟩
  exact biproduct.whiskerEquiv e (fun i => eqToIso (by
    simp only [Equiv.symm_apply_apply]
    exact (ha i).symm))

instance : (envelopeToC S).Faithful where
  map_injective {M N} f g h := by
    apply Mat_.hom_ext
    intro i j
    apply ObjectProperty.hom_ext
    have := congrArg (fun k => biproduct.components k i j) h
    simpa only [envelopeToC_map, biproduct.matrix_components] using this

instance : (envelopeToC S).Full where
  map_surjective {M N} g := by
    refine ⟨fun i j => ObjectProperty.homMk
      (biproduct.components (f := fun i => (M.X i).obj) (g := fun j => (N.X j).obj) g i j), ?_⟩
    exact biproduct.components_matrix g

/-- The realization of the envelope as the additive closure of `L₋`. -/
noncomputable def envelopeFunctor : LminusEnvelope S ⥤ (LminusClosure S).FullSubcategory :=
  (LminusClosure S).lift (envelopeToC S) (envelopeToC_mem S)

/-- **The additive closure of `L₋` is the additive envelope of its simples.** -/
theorem envelopeFunctor_isEquivalence : (envelopeFunctor S).IsEquivalence := by
  have hfaith : (envelopeFunctor S ⋙ (LminusClosure S).ι).Faithful :=
    (inferInstance : (envelopeToC S).Faithful)
  have hfull : (envelopeFunctor S ⋙ (LminusClosure S).ι).Full :=
    (inferInstance : (envelopeToC S).Full)
  refine
    { faithful := Functor.Faithful.of_comp _ (LminusClosure S).ι
      full := Functor.Full.of_comp_faithful _ (LminusClosure S).ι
      essSurj := ⟨fun Y => ?_⟩ }
  obtain ⟨n, a, ⟨e⟩⟩ := Y.property
  refine ⟨⟨Fin n, fun j => ⟨S (a j, -a j), a j, rfl⟩⟩, ⟨(LminusClosure S).isoMk e.symm⟩⟩

end Envelope

section Symmetric

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]

/-- Naturality of the double braiding. -/
@[reassoc]
theorem monodromy_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (β_ X' Y').hom ≫ (β_ Y' X').hom = (β_ X Y).hom ≫ (β_ Y X).hom ≫ (f ⊗ₘ g) := by
  rw [BraidedCategory.braiding_naturality_assoc, BraidedCategory.braiding_naturality]

/-- A double braiding trivial on all pairs of summands is trivial on biproducts. -/
theorem monodromy_biproduct {J K : Type} [Fintype J] [Fintype K] (f : J → C) (g : K → C)
    (h : ∀ j k, (β_ (f j) (g k)).hom ≫ (β_ (g k) (f j)).hom = 𝟙 _) :
    (β_ (⨁ f) (⨁ g)).hom ≫ (β_ (⨁ g) (⨁ f)).hom = 𝟙 _ := by
  have htot : 𝟙 ((⨁ f) ⊗ (⨁ g)) = ∑ j, ∑ k,
      (biproduct.π f j ⊗ₘ biproduct.π g k) ≫ (biproduct.ι f j ⊗ₘ biproduct.ι g k) := by
    rw [← MonoidalCategory.id_tensorHom_id, ← biproduct.total, ← biproduct.total,
      sum_tensor]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tensor_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  calc (β_ (⨁ f) (⨁ g)).hom ≫ (β_ (⨁ g) (⨁ f)).hom
      = ((β_ (⨁ f) (⨁ g)).hom ≫ (β_ (⨁ g) (⨁ f)).hom) ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = ∑ j, ∑ k, (biproduct.π f j ⊗ₘ biproduct.π g k) ≫
          ((β_ (f j) (g k)).hom ≫ (β_ (g k) (f j)).hom) ≫
            (biproduct.ι f j ⊗ₘ biproduct.ι g k) := by
        rw [htot, Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Category.assoc]
        rw [← monodromy_natural_assoc]
    _ = ∑ j, ∑ k,
          (biproduct.π f j ⊗ₘ biproduct.π g k) ≫ (biproduct.ι f j ⊗ₘ biproduct.ι g k) := by
        simp only [h, Category.id_comp]
    _ = 𝟙 _ := htot.symm

/-- A double braiding that is trivial after an isomorphism is trivial. -/
theorem monodromy_of_iso {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : (β_ X' Y').hom ≫ (β_ Y' X').hom = 𝟙 _) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ := by
  have := monodromy_natural eX.hom eY.hom
  rw [h, Category.comp_id] at this
  rw [← cancel_mono (eX.hom ⊗ₘ eY.hom), Category.assoc, ← this, Category.id_comp]

variable (S : ZMod 3 × ZMod 3 → C)

/-- The double braiding is trivial on the additive closure of `L₋` if it is trivial on its
simples. -/
theorem monodromy_lminusClosure
    (hmono : ∀ a b : ZMod 3,
      (β_ (S (a, -a)) (S (b, -b))).hom ≫ (β_ (S (b, -b)) (S (a, -a))).hom = 𝟙 _)
    {X Y : C} (hX : LminusClosure S X) (hY : LminusClosure S Y) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ := by
  obtain ⟨n, a, ⟨eX⟩⟩ := hX
  obtain ⟨m, b, ⟨eY⟩⟩ := hY
  exact monodromy_of_iso eX eY (monodromy_biproduct _ _ fun j k => hmono (a j) (b k))

/-- **The inherited braiding on the additive closure of `L₋` is symmetric**, given trivial
double braidings on the simples. -/
@[instance_reducible]
noncomputable def lminusClosureSymmetric [(LminusClosure S).IsMonoidal]
    (hmono : ∀ a b : ZMod 3,
      (β_ (S (a, -a)) (S (b, -b))).hom ≫ (β_ (S (b, -b)) (S (a, -a))).hom = 𝟙 _) :
    SymmetricCategory (LminusClosure S).FullSubcategory where
  toBraidedCategory := inferInstance
  symmetry X Y := by
    apply ObjectProperty.hom_ext
    exact monodromy_lminusClosure S hmono X.property Y.property

end Symmetric

section Main

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type*) [Field 𝕜]
  [Linear 𝕜 C] [MonoidalLinear 𝕜 C]

/-- Trivial self-braidings on `L₋` give trivial double braidings on all pairs of simples
(via the trivialization of `Lminus_untwisted_symmetric`). -/
theorem Lminus_monodromy (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) (a b : ZMod 3) :
    (β_ (S (a, -a)) (S (b, -b))).hom ≫ (β_ (S (b, -b)) (S (a, -a))).hom = 𝟙 _ := by
  let S' : ZMod 3 → C := fun a => S (a, -a)
  have hEnd : ∀ a, finrank 𝕜 (S' a ⟶ S' a) = 1 := fun a => by
    show finrank 𝕜 (S (a, -a) ⟶ S (a, -a)) = 1
    rw [hSchur, if_pos rfl]
  let φ : ∀ a b : ZMod 3, S' a ⊗ S' b ≅ S' (a + b) := fun a b =>
    hfusion (a, -a) (b, -b) ≪≫ eqToIso (congrArg S (PointedCocycle.Lminus_add a b))
  obtain ⟨φ', -, hβ⟩ := PointedCocycle.Lminus_untwisted_symmetric 𝕜 S' hEnd φ hθ
  have h1 := hβ a b
  have h2 := hβ b a
  rw [← cancel_mono (φ' a b).hom, Category.assoc, h2, ← Category.assoc, h1, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The additive closure of `L₋` is a symmetric monoidal category equivalent to the additive
envelope of the linearized discrete `ℤ/3`.**  Under `hSchur`, `hfusion`, `hunitS` and
**[external]** `hθ`: (i) `LminusClosure S` is monoidal (`lminusClosure_isMonoidal`) and its
inherited braiding is symmetric (`lminusClosureSymmetric`); (ii) `envelopeFunctor S` is an
equivalence from `Mat_` of the linear category on the three simples, whose Hom spaces have
dimension `δ_{a,b}`. -/
theorem Lminus_closure_symmetric_envelope (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) :
    haveI := lminusClosure_isMonoidal hfusion hunitS
    (∀ X Y : (LminusClosure S).FullSubcategory, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _) ∧
      Nonempty (SymmetricCategory (LminusClosure S).FullSubcategory) ∧
      (envelopeFunctor S).IsEquivalence ∧
      ∀ a b : ZMod 3, finrank 𝕜 (S (a, -a) ⟶ S (b, -b)) = if a = b then 1 else 0 := by
  have hmono := Lminus_monodromy 𝕜 S hSchur hfusion hθ
  have hM := lminusClosure_isMonoidal hfusion hunitS
  have hdim : ∀ a b : ZMod 3, finrank 𝕜 (S (a, -a) ⟶ S (b, -b)) = if a = b then 1 else 0 := by
    intro a b
    rw [hSchur]
    by_cases h : a = b
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun h' => h (congrArg Prod.fst h')), if_neg h]
  exact ⟨fun X Y => by
      apply ObjectProperty.hom_ext
      exact monodromy_lminusClosure S hmono X.property Y.property,
    ⟨lminusClosureSymmetric S hmono⟩, envelopeFunctor_isEquivalence S, hdim⟩

end Main

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.envelopeFunctor_isEquivalence
#print axioms HaagerupIzumi.C8.RightMod.monodromy_biproduct
#print axioms HaagerupIzumi.C8.RightMod.lminusClosureSymmetric
#print axioms HaagerupIzumi.C8.RightMod.Lminus_monodromy
#print axioms HaagerupIzumi.C8.RightMod.Lminus_closure_symmetric_envelope
