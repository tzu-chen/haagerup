module

public import HaagerupIzumi.C8.Category.TwistedGroupAlgebraOfMul
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-! # Induction from the additive closure of `L₋` is an equivalence onto `𝒞_{H/B}`

The conclusion of the identification step of `L_untwisted` (manuscript
`haagerup_c8_expanded.tex`, lines 3345–3348): "Thus induction identifies the entire
all-module category for `H/B` with this untwisted pointed category."

* `map_bijective_of_iso`: bijectivity of `F.map` on Hom-sets is invariant under
  isomorphisms of the source and target objects.
* `LminusClosure S`: objects of `C` isomorphic to a finite direct sum of the three
  invertibles `S (a, -a)` of `L₋` (the additive closure of the pointed subcategory on `L₋`).
* `freeLminus A S = (LminusClosure S).ι ⋙ freeFunctor A`: free induction restricted to it.
* `freeLminus_isEquivalence`: **`freeLminus A S` is an equivalence of categories** onto the
  category `𝒞_A` of all right `A`-modules: faithful and full by
  `freeMap_bijective_Lminus_biproduct` (`Category/FreeModuleAdditive.lean`), essentially
  surjective by `free_essSurj_Lminus_of_mul_ne_zero` (`Category/TwistedGroupAlgebraOfMul.lean`).
  This is an equivalence of plain categories (`Functor.IsEquivalence`).

Hypotheses: those of `free_essSurj_Lminus_of_mul_ne_zero`: `hSchur`, `hfusion`, `hA` (the
pointed category `Rep(B)` and `H/B` as an object), `hmul` (the homogeneous components of the
multiplication of `H/B` are nonzero), `3 ≠ 0` in `𝕜`, `hss` (every object of `Rep(B)` is a
finite sum of the nine invertibles), `hsplit` (idempotents of sums of `L₋`-invertibles split
through sub-sums).  Not formalized: that the pointed subcategory on `L₋` is the untwisted
`Vec_{ℤ/3}` as a (braided) tensor category (Joyal–Street / Deligne; its quadratic form vanishes:
`Weights.Lminus_symmetric_trivial_twists`), and the embedding into `Rep(U)` and `𝓕`.  Also
not formalized: the monoidal (tensor) equivalence.  A monoidal structure is constructed only
on `freeFunctor A ⋙ toBimod A : C ⥤ (Bimod A A, ⊗_A)` (`Category/FreeModuleMonoidalFunctor.lean`),
under `BraidedCategory C`, `IsCommMonObj A.X` and coequalizers preserved by `X ⊗ -`,
`- ⊗ X`; there is no monoidal structure here on `LminusClosure S` or on `RightMod A`, and a
tensor structure on `LminusClosure S` would also need `S (0, 0) ≅ 𝟙_ C`. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module

universe v u

section General

variable {D : Type*} [Category D] {E : Type*} [Category E] (F : D ⥤ E)

/-- Bijectivity of `F.map` on `Hom(X', Y')` transfers to `Hom(X, Y)` along `X ≅ X'`,
`Y ≅ Y'`. -/
theorem map_bijective_of_iso {X X' Y Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : Function.Bijective (fun f : X' ⟶ Y' => F.map f)) :
    Function.Bijective (fun f : X ⟶ Y => F.map f) := by
  constructor
  · intro f g hfg
    have hfg' : F.map f = F.map g := hfg
    have h' : eX.inv ≫ f ≫ eY.hom = eX.inv ≫ g ≫ eY.hom := h.1 (by
      show F.map (eX.inv ≫ f ≫ eY.hom) = F.map (eX.inv ≫ g ≫ eY.hom)
      simp only [F.map_comp, hfg'])
    exact (cancel_mono eY.hom).1 ((cancel_epi eX.inv).1 h')
  · intro Φ
    obtain ⟨g, hg⟩ := h.2 (F.map eX.inv ≫ Φ ≫ F.map eY.hom)
    have hg' : F.map g = F.map eX.inv ≫ Φ ≫ F.map eY.hom := hg
    refine ⟨eX.hom ≫ g ≫ eY.inv, ?_⟩
    show F.map (eX.hom ≫ g ≫ eY.inv) = Φ
    rw [F.map_comp, F.map_comp, hg']
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, eX.hom_inv_id, F.map_id, Category.id_comp, ← F.map_comp,
      eY.hom_inv_id, F.map_id, Category.comp_id]

end General

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

/-- The additive closure of the three invertibles `S (a, -a)` of `L₋`. -/
def LminusClosure (S : ZMod 3 × ZMod 3 → C) [Preadditive C] [HasFiniteBiproducts C] :
    ObjectProperty C :=
  fun X => ∃ (n : ℕ) (a : Fin n → ZMod 3), Nonempty (X ≅ ⨁ fun j => S (a j, -a j))

/-- Free induction restricted to the additive closure of `L₋`. -/
def freeLminus [Preadditive C] [HasFiniteBiproducts C] (A : Mon C)
    (S : ZMod 3 × ZMod 3 → C) : (LminusClosure S).FullSubcategory ⥤ RightMod A :=
  (LminusClosure S).ι ⋙ freeFunctor A

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]
  {A : Mon C} {S : ZMod 3 × ZMod 3 → C}
  (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
  (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
  (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))

include hSchur hfusion hA in
/-- Free induction is bijective on Hom-sets between objects of the additive closure of `L₋`. -/
theorem freeFunctor_bijective_LminusClosure {X Y : C} (hX : LminusClosure S X)
    (hY : LminusClosure S Y) : Function.Bijective (fun f : X ⟶ Y => (freeFunctor A).map f) := by
  obtain ⟨n, a, ⟨eX⟩⟩ := hX
  obtain ⟨m, b, ⟨eY⟩⟩ := hY
  exact map_bijective_of_iso (freeFunctor A) eX eY
    (freeMap_bijective_Lminus_biproduct 𝕜 A S hSchur hfusion hA a b)

include hSchur hfusion in
/-- **Free induction identifies the additive closure of `L₋` with all `H/B`-modules**
(manuscript lines 3345–3348): `freeLminus A S` is an equivalence of categories. -/
theorem freeLminus_isEquivalence (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0)
    (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j)))
    (hsplit : ∀ (n : ℕ) (a : Fin n → ZMod 3)
      (e : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun j => S (a j, -a j))), e ≫ e = e →
        ∃ (m : ℕ) (b : Fin m → ZMod 3)
          (R : Retract (⨁ fun k => S (b k, -b k)) (⨁ fun j => S (a j, -a j))), R.r ≫ R.i = e) :
    (freeLminus A S).IsEquivalence where
  faithful := ⟨by
    intro X Y f g h
    apply ObjectProperty.hom_ext
    exact (freeFunctor_bijective_LminusClosure 𝕜 hSchur hfusion hA X.property Y.property).1 h⟩
  full := ⟨by
    intro X Y Φ
    obtain ⟨f, hf⟩ :=
      (freeFunctor_bijective_LminusClosure 𝕜 hSchur hfusion hA X.property Y.property).2 Φ
    exact ⟨ObjectProperty.homMk f, hf⟩⟩
  essSurj := ⟨by
    intro M
    obtain ⟨m, b, ⟨e⟩⟩ :=
      free_essSurj_Lminus_of_mul_ne_zero 𝕜 hSchur hfusion hA hmul h3 hss hsplit M
    exact ⟨⟨⨁ fun k => S (b k, -b k), m, b, ⟨Iso.refl _⟩⟩, ⟨e.symm⟩⟩⟩

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.map_bijective_of_iso
#print axioms HaagerupIzumi.C8.RightMod.freeFunctor_bijective_LminusClosure
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_isEquivalence
