module

public import HaagerupIzumi.C8.Category.FreeModuleTwistedSeparable

@[expose] public section

/-! # Every `H/B`-module is induced from the additive closure of `L₋`

The conclusion of the identification step of `L_untwisted` (manuscript
`haagerup_c8_expanded.tex`, lines 3345–3348): "Every free module is a direct sum of these three
simple modules, and separability makes every module a summand of a free module.  Thus
induction identifies the entire all-module category for `H/B` with this untwisted pointed
category."  On objects:

* `isoOfRetractsOfEq`: two retracts of the same object cutting out the same idempotent are
  isomorphic.
* `RightMod.free_essSurj_Lminus`: every right `A`-module `M` is isomorphic to the free module
  `(⊕ₖ (b_k, -b_k)) ⊗ A` on a finite direct sum of the three invertibles of `L₋`.  Proof: `M` is
  a retract of `M.X ⊗ A` (`retractFree_twisted`, the separability section of
  `Category/FreeModuleTwistedSeparable.lean`); `M.X ≅ ⊕ⱼ S v_j` and
  `(⊕ⱼ S v_j) ⊗ A ≅ (⊕ⱼ S (a_j, -a_j)) ⊗ A` (`free_biproduct_iso_Lminus`); the idempotent
  of `(⊕ⱼ S (a_j, -a_j)) ⊗ A` cutting out `M` is induced from an idempotent `e'` of
  `⊕ⱼ S (a_j, -a_j)` (`freeMap_bijective_Lminus_biproduct`, full faithfulness), which splits
  in `C` through a sub-sum `⊕ₖ S (b_k, -b_k)`; free induction carries this splitting to one of
  the module idempotent.

Together with `freeMap_bijective_Lminus_biproduct` (`Category/FreeModuleAdditive.lean`) this
says that free induction, restricted to the additive closure of the three invertibles of
`L₋`, is fully faithful and essentially surjective onto `𝒞_A`: an equivalence of plain
categories (`freeLminus_isEquivalence`, `Category/FreeModuleEquivalence.lean`).  Not formalized:
the monoidal (tensor) equivalence.  A monoidal structure exists only on
`freeFunctor A ⋙ toBimod A` (`Category/FreeModuleMonoidalFunctor.lean`, under
`BraidedCategory C`, `IsCommMonObj A.X` and coequalizers preserved by `X ⊗ -`, `- ⊗ X`); there
is none here on `LminusClosure S` or `RightMod A`, and one would also need `S (0, 0) ≅ 𝟙_ C`.

Hypotheses (structural facts about `Rep(B)` and `H/B`, phrased as such; none is the
conclusion): `hSchur`, `hfusion`, `hA` as in `Category/FreeModuleUntwisted.lean`;
`D : TwistedGroupAlgebra hA` (the multiplication of `H/B` maps `S (c,c) ⊗ S (d,d)`
isomorphically onto `S (c+d, c+d)`); `3 ≠ 0` in `𝕜`; `hss` (every object of `C` is a finite
direct sum of the nine invertibles: `Rep(B)` is semisimple and pointed); `hsplit` (every
idempotent of a finite direct sum of invertibles of `L₋` splits through a sub-sum: the
Krull–Schmidt property of the semisimple category `Rep(B)`).  Not formalized: the facts
behind these hypotheses, the Tannakian identification of the pointed category on `L₋` with
`Vec_{ℤ/3}`, and the embedding into `Rep(U)` (manuscript lines 3335–3337, 3349–3352). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

section General

variable {D : Type*} [Category D]

/-- Two retracts `M`, `N` of `P` with the same idempotent `r ≫ i` of `P` are isomorphic. -/
def isoOfRetractsOfEq {M N P : D} (R₁ : Retract M P) (R₂ : Retract N P)
    (h : R₁.r ≫ R₁.i = R₂.r ≫ R₂.i) : M ≅ N where
  hom := R₁.i ≫ R₂.r
  inv := R₂.i ≫ R₁.r
  hom_inv_id := by
    simp only [Category.assoc]
    rw [← reassoc_of% h, Retract.retract_assoc, Retract.retract]
  inv_hom_id := by
    simp only [Category.assoc]
    rw [reassoc_of% h, Retract.retract_assoc, Retract.retract]

end General

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

/-- Free induction preserves composition, in the form `freeMap A (f ≫ g) = ...`. -/
theorem freeMap_comp (A : Mon C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    freeMap A (f ≫ g) = freeMap A f ≫ freeMap A g :=
  hom_ext (by
    show (f ≫ g) ▷ A.X = f ▷ A.X ≫ g ▷ A.X
    exact MonoidalCategory.comp_whiskerRight f g A.X)

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]

/-- **Every `H/B`-module is induced from `L₋`** (manuscript lines 3345–3348): every right
`A`-module is isomorphic to the free module on a finite direct sum of the three invertibles
`S (b, -b)` of `L₋`. -/
theorem free_essSurj_Lminus (A : Mon C) (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, Module.finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    {hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)} (D : TwistedGroupAlgebra hA)
    (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j)))
    (hsplit : ∀ (n : ℕ) (a : Fin n → ZMod 3)
      (e : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun j => S (a j, -a j))), e ≫ e = e →
        ∃ (m : ℕ) (b : Fin m → ZMod 3)
          (R : Retract (⨁ fun k => S (b k, -b k)) (⨁ fun j => S (a j, -a j))), R.r ≫ R.i = e)
    (M : RightMod A) :
    ∃ (m : ℕ) (b : Fin m → ZMod 3), Nonempty (M ≅ free A (⨁ fun k => S (b k, -b k))) := by
  -- `M` is a retract of a free module on a sum of invertibles of `L₋`.
  obtain ⟨n, v, ⟨eX⟩⟩ := hss M.X
  obtain ⟨a, ⟨eL⟩⟩ := free_biproduct_iso_Lminus A S hfusion D v
  obtain ⟨R0⟩ := retractFree_Lplus 𝕜 D h3 M
  let R1 : Retract M (free A (⨁ fun j => S (a j, -a j))) :=
    R0.trans (Retract.ofIso ((freeFunctor A).mapIso eX ≪≫ eL))
  -- Its idempotent is induced from an idempotent of the sum in `C`.
  have hbij := freeMap_bijective_Lminus_biproduct 𝕜 A S hSchur hfusion hA a a
  obtain ⟨e', he'⟩ := hbij.2 (R1.r ≫ R1.i)
  have he'' : freeMap A e' = R1.r ≫ R1.i := he'
  have hidem : e' ≫ e' = e' := by
    apply hbij.1
    show freeMap A (e' ≫ e') = freeMap A e'
    rw [freeMap_comp, he'', Category.assoc, R1.retract_assoc]
  -- Split it in `C`, and induce the splitting.
  obtain ⟨m, b, R2, hR2⟩ := hsplit n a e' hidem
  refine ⟨m, b, ⟨isoOfRetractsOfEq R1 (R2.map (freeFunctor A)) ?_⟩⟩
  exact he''.symm.trans ((congrArg (freeMap A) hR2.symm).trans (freeMap_comp A R2.r R2.i))

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.isoOfRetractsOfEq
#print axioms HaagerupIzumi.C8.RightMod.freeMap_comp
#print axioms HaagerupIzumi.C8.RightMod.free_essSurj_Lminus
