module

public import HaagerupIzumi.C8.Category.FreeModuleUntwisted
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor

@[expose] public section

/-! # Additivity of free induction; full faithfulness on the additive closure of `L₋`

Part of the identification step of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`,
lines 3337–3348): free induction `x ↦ x ⊗ (H/B)` is fully faithful on the three simples of
`L₋` (`Category/FreeModuleUntwisted.lean`, `freeMap_bijective_Lminus`); here this is extended
to finite direct sums of them, which is what "induction identifies the entire all-module
category ... with this untwisted pointed category" uses on morphisms.

* `map_injective_biproduct`, `map_surjective_biproduct`, `map_bijective_biproduct`: for an
  additive functor `F` between preadditive categories, if `F.map` is injective (surjective)
  on `Hom(f j, g k)` for all summands, it is injective (surjective) on `Hom(⨁ f, ⨁ g)`.
  (Components `ι_j ≫ φ ≫ π_k`, and `F` applied to `∑ π_j ≫ ι_j = 𝟙`.)
* `RightMod.freeFunctor_additive`, `RightMod.freeFunctor_linear`: free induction
  `C ⥤ 𝒞_A` is additive, and `𝕜`-linear, for additive (linear) whiskering.
* `RightMod.freeMap_bijective_Lminus_biproduct`: for `x_j = (a_j, -a_j)` and
  `y_k = (b_k, -b_k)` in `L₋`, `f ↦ f ⊗ A` is a bijection
  `Hom(⨁ⱼ x_j, ⨁ₖ y_k) ≅ Hom_A((⨁ⱼ x_j) ⊗ A, (⨁ₖ y_k) ⊗ A)`: free induction is fully
  faithful on the additive closure of the three simples of `L₋`.

Hypotheses: those of `freeMap_bijective_Lminus` (`hSchur`, `hfusion`, `hA`: the structure
of the pointed category `Rep(B)` and of `H/B ≅ ⊕_{ℓ ∈ L₊} ℓ` as an object); no other
external-theorem or certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

section General

variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
  {E : Type*} [Category E] [Preadditive E] (F : D ⥤ E) [F.Additive]

omit [Preadditive E] [F.Additive] in
/-- An additive functor that is injective on the Hom-sets between the summands is injective
on the Hom-sets between the biproducts. -/
theorem map_injective_biproduct {J K : Type} [Finite J] [Finite K] (f : J → D) (g : K → D)
    (h : ∀ j k, Function.Injective (fun φ : f j ⟶ g k => F.map φ)) :
    Function.Injective (fun φ : ⨁ f ⟶ ⨁ g => F.map φ) := by
  intro φ ψ hφψ
  have hφψ' : F.map φ = F.map ψ := hφψ
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => h j k ?_
  show F.map ((biproduct.ι f j ≫ φ) ≫ biproduct.π g k) =
    F.map ((biproduct.ι f j ≫ ψ) ≫ biproduct.π g k)
  simp only [Functor.map_comp, hφψ']

/-- `F` applied to `∑ π_j ≫ ι_j = 𝟙`. -/
theorem map_biproduct_total {J : Type} [Fintype J] (f : J → D) :
    ∑ j, F.map (biproduct.π f j) ≫ F.map (biproduct.ι f j) = 𝟙 (F.obj (⨁ f)) := by
  have h := congrArg F.map (biproduct.total (f := f))
  simp only [Functor.map_sum, Functor.map_comp] at h
  exact h.trans (F.map_id _)

/-- An additive functor that is surjective on the Hom-sets between the summands is surjective
on the Hom-sets between the biproducts. -/
theorem map_surjective_biproduct {J K : Type} [Fintype J] [Fintype K] (f : J → D) (g : K → D)
    (h : ∀ j k, Function.Surjective (fun φ : f j ⟶ g k => F.map φ)) :
    Function.Surjective (fun φ : ⨁ f ⟶ ⨁ g => F.map φ) := by
  intro Φ
  choose φ hφ using fun j k => h j k (F.map (biproduct.ι f j) ≫ Φ ≫ F.map (biproduct.π g k))
  have hφ' : ∀ j k, F.map (φ j k) = F.map (biproduct.ι f j) ≫ Φ ≫ F.map (biproduct.π g k) :=
    hφ
  refine ⟨∑ j, ∑ k, biproduct.π f j ≫ φ j k ≫ biproduct.ι g k, ?_⟩
  show F.map (∑ j, ∑ k, biproduct.π f j ≫ φ j k ≫ biproduct.ι g k) = Φ
  calc F.map (∑ j, ∑ k, biproduct.π f j ≫ φ j k ≫ biproduct.ι g k)
      = ∑ j, ∑ k, F.map (biproduct.π f j) ≫
          (F.map (biproduct.ι f j) ≫ Φ ≫ F.map (biproduct.π g k)) ≫
            F.map (biproduct.ι g k) := by
        simp only [Functor.map_sum, Functor.map_comp, hφ']
    _ = (∑ j, F.map (biproduct.π f j) ≫ F.map (biproduct.ι f j)) ≫ Φ ≫
          (∑ k, F.map (biproduct.π g k) ≫ F.map (biproduct.ι g k)) := by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
        exact Finset.sum_comm
    _ = Φ := by
        rw [map_biproduct_total F f, map_biproduct_total F g, Category.id_comp,
          Category.comp_id]

/-- An additive functor that is bijective on the Hom-sets between the summands is bijective
on the Hom-sets between the biproducts. -/
theorem map_bijective_biproduct {J K : Type} [Fintype J] [Fintype K] (f : J → D) (g : K → D)
    (h : ∀ j k, Function.Bijective (fun φ : f j ⟶ g k => F.map φ)) :
    Function.Bijective (fun φ : ⨁ f ⟶ ⨁ g => F.map φ) :=
  ⟨map_injective_biproduct F f g fun j k => (h j k).1,
    map_surjective_biproduct F f g fun j k => (h j k).2⟩

end General

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section Additive

variable [Preadditive C] [MonoidalPreadditive C] (A : Mon C)

/-- **Free induction is additive**: `(f + g) ⊗ A = f ⊗ A + g ⊗ A`. -/
instance freeFunctor_additive : (freeFunctor A).Additive where
  map_add {X Y f g} := hom_ext (by
    show (f + g) ▷ A.X = f ▷ A.X + g ▷ A.X
    exact MonoidalPreadditive.add_whiskerRight f g)

/-- Free induction is `𝕜`-linear. -/
instance freeFunctor_linear (𝕜 : Type*) [Semiring 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C] :
    (freeFunctor A).Linear 𝕜 where
  map_smul {X Y} f r := hom_ext (by
    show (r • f) ▷ A.X = r • (f ▷ A.X)
    exact MonoidalLinear.smul_whiskerRight r f A.X)

end Additive

section Lminus

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]

/-- **Free induction is fully faithful on the additive closure of `L₋`** (manuscript
lines 3337–3348): for finite families `x_j = (a_j, -a_j)`, `y_k = (b_k, -b_k)` in `L₋`,
`f ↦ f ⊗ A` is a bijection `Hom(⨁ⱼ x_j, ⨁ₖ y_k) ≅ Hom_A((⨁ⱼ x_j) ⊗ A, (⨁ₖ y_k) ⊗ A)`. -/
theorem freeMap_bijective_Lminus_biproduct (A : Mon C) (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, Module.finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) {J K : Type} [Fintype J] [Fintype K]
    (a : J → ZMod 3) (b : K → ZMod 3) :
    Function.Bijective (fun φ : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun k => S (b k, -b k)) =>
      (freeFunctor A).map φ) :=
  map_bijective_biproduct (freeFunctor A) _ _ fun j k =>
    freeMap_bijective_Lminus 𝕜 A S hSchur hfusion hA (a j) (b k)

end Lminus

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.map_injective_biproduct
#print axioms HaagerupIzumi.C8.map_surjective_biproduct
#print axioms HaagerupIzumi.C8.map_bijective_biproduct
#print axioms HaagerupIzumi.C8.RightMod.freeFunctor_additive
#print axioms HaagerupIzumi.C8.RightMod.freeFunctor_linear
#print axioms HaagerupIzumi.C8.RightMod.freeMap_bijective_Lminus_biproduct
