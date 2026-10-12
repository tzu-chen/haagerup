module

public import HaagerupIzumi.C8.Fusion.FusionAlgebra
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# `End(𝟙 ⊕ X ⊕ 2Y) ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (Schur), and the `FusionAlgebraIso` of line 3799

Line 3799 of `c8_expanded_20260929/haagerup_c8_expanded.tex`: *"the composition algebra of
`End_𝒞(H)` is the complex fusion algebra [BJ, Cor. 3.4]; with `H = 𝟙 ⊕ X ⊕ 2Y` it is
`ℂ ⊕ ℂ ⊕ M₂(ℂ)`."*  The second clause is a manuscript step; this file proves it.

In a `ℂ`-linear preadditive category with binary biproducts:

* `endBiprodOrth A B`: if `Hom(A, B) = 0 = Hom(B, A)`, then `End(A ⊞ B) ≃ₐ[ℂ] End A × End B`;
* `endScalar A`: if `dim End A = 1` (Schur), then `End A ≃ₐ[ℂ] ℂ`;
* `endBiprodSelf Y`: `End(Y ⊞ Y) ≃ₐ[ℂ] M₂(End Y)` (the column convention: the `(a, b)` entry is
  the component from the `b`-th to the `a`-th summand, so composition is matrix multiplication);
* `endHIso P₀ X Y`: for `P₀, X, Y` with one-dimensional endomorphism spaces and vanishing Hom
  spaces between distinct ones, `End(P₀ ⊞ (X ⊞ (Y ⊞ Y))) ≃ₐ[ℂ] ℂ × ℂ × M₂(ℂ)` (`CCM2`);
* `endHIsoOfSimple`: the same for simple, pairwise non-isomorphic `P₀, X, Y` in a category with
  kernels and finite-dimensional Hom spaces, from Mathlib's Schur lemma
  (`finrank_endomorphism_simple_eq_one`, `finrank_hom_simple_simple_eq_zero_of_not_iso`);
* `fusionAlgebraIsoOfSchur`: with the **[external] Bischoff–Jones identification**
  `K₀(𝓕) ⊗ ℂ ≅ End_𝒞(H)` (`BJIso`, Corollary 3.4) and an isomorphism `H ≅ P₀ ⊞ (X ⊞ (Y ⊞ Y))`
  (the restriction `H↓U = 𝟙 ⊕ X ⊕ 2Y` at rank six), the `FusionAlgebraIso` of
  `Fusion/FusionAlgebra.lean`, the hypothesis `hΨ` of `rank6_ring_of_fusionAlgebraIso`.
-/

namespace HaagerupIzumi.C8.Fusion

open CategoryTheory CategoryTheory.Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasBinaryBiproducts C]

omit [Linear ℂ C] [HasBinaryBiproducts C] in
/-- Addition in `End X` is addition of morphisms. -/
theorem end_add_eq {X : C} (φ ψ : End X) :
    φ + ψ = @HAdd.hAdd (X ⟶ X) (X ⟶ X) (X ⟶ X) _ φ ψ := rfl

omit [HasBinaryBiproducts C] in
/-- The scalars of `End X` are the multiples of `𝟙 X`. -/
theorem algebraMap_end_eq {X : C} (c : ℂ) :
    algebraMap ℂ (End X) c = @HSMul.hSMul ℂ (X ⟶ X) (X ⟶ X) _ c (𝟙 X) := rfl

omit [Linear ℂ C] in
/-- Insert `𝟙 = fst ≫ inl + snd ≫ inr` between `g` and `h`. -/
theorem comp_biprod_decomp {P Q X Y : C} (g : P ⟶ X ⊞ Y) (h : X ⊞ Y ⟶ Q) :
    g ≫ h = (g ≫ biprod.fst) ≫ biprod.inl ≫ h + (g ≫ biprod.snd) ≫ biprod.inr ≫ h := by
  calc g ≫ h = g ≫ 𝟙 _ ≫ h := by rw [Category.id_comp]
    _ = g ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ h := by rw [biprod.total]
    _ = _ := by simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]

omit [Linear ℂ C] in
/-- The components of a composite of endomorphisms of `X ⊞ Y`. -/
theorem entry_mul {X Y P Q : C} (ι : P ⟶ X ⊞ Y) (π : X ⊞ Y ⟶ Q) (φ ψ : X ⊞ Y ⟶ X ⊞ Y) :
    ι ≫ (ψ ≫ φ) ≫ π = (ι ≫ ψ ≫ biprod.fst) ≫ (biprod.inl ≫ φ ≫ π) +
      (ι ≫ ψ ≫ biprod.snd) ≫ (biprod.inr ≫ φ ≫ π) := by
  have h := comp_biprod_decomp (ι ≫ ψ) (φ ≫ π)
  simp only [Category.assoc] at h ⊢
  exact h

omit [Linear ℂ C] in
theorem subsingleton_hom_biprod {P A B : C} (hA : Subsingleton (P ⟶ A))
    (hB : Subsingleton (P ⟶ B)) : Subsingleton (P ⟶ A ⊞ B) :=
  ⟨fun _ _ => biprod.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

omit [Linear ℂ C] in
theorem subsingleton_biprod_hom {P A B : C} (hA : Subsingleton (A ⟶ P))
    (hB : Subsingleton (B ⟶ P)) : Subsingleton (A ⊞ B ⟶ P) :=
  ⟨fun _ _ => biprod.hom_ext' _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- **`End(A ⊞ B) ≅ End A × End B` when `Hom(A, B) = 0 = Hom(B, A)`.** -/
noncomputable def endBiprodOrth (A B : C) [hAB : Subsingleton (A ⟶ B)]
    [hBA : Subsingleton (B ⟶ A)] : End (A ⊞ B) ≃ₐ[ℂ] End A × End B where
  toFun φ := (biprod.inl ≫ φ ≫ biprod.fst, biprod.inr ≫ φ ≫ biprod.snd)
  invFun p := biprod.map p.1 p.2
  left_inv φ := by
    show biprod.map (biprod.inl ≫ φ ≫ biprod.fst) (biprod.inr ≫ φ ≫ biprod.snd) = φ
    ext <;> simp <;> exact Subsingleton.elim _ _
  right_inv p := Prod.ext (by simp) (by simp)
  map_mul' φ ψ := by
    refine Prod.ext ?_ ?_
    · show biprod.inl ≫ (ψ ≫ φ) ≫ biprod.fst =
        (biprod.inl ≫ ψ ≫ biprod.fst) ≫ (biprod.inl ≫ φ ≫ biprod.fst)
      rw [entry_mul, Subsingleton.elim (biprod.inl ≫ ψ ≫ biprod.snd) 0, zero_comp, add_zero]
    · show biprod.inr ≫ (ψ ≫ φ) ≫ biprod.snd =
        (biprod.inr ≫ ψ ≫ biprod.snd) ≫ (biprod.inr ≫ φ ≫ biprod.snd)
      rw [entry_mul, Subsingleton.elim (biprod.inr ≫ ψ ≫ biprod.fst) 0, zero_comp, zero_add]
  map_add' φ ψ := Prod.ext (by simp [end_add_eq, Preadditive.add_comp, Preadditive.comp_add])
    (by simp [end_add_eq, Preadditive.add_comp, Preadditive.comp_add])
  commutes' c := Prod.ext (by simp [algebraMap_end_eq]) (by simp [algebraMap_end_eq])

omit [HasBinaryBiproducts C] in
/-- `𝟙 ≠ 0` on an object with one-dimensional endomorphism space. -/
theorem id_ne_zero_of_finrank_one {A : C} (h1 : finrank ℂ (A ⟶ A) = 1) : 𝟙 A ≠ 0 := by
  intro h0
  have : Subsingleton (A ⟶ A) :=
    ⟨fun f g => by rw [← Category.comp_id f, ← Category.comp_id g, h0, Limits.comp_zero,
      Limits.comp_zero]⟩
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

/-- **Schur: `End A ≅ ℂ`** when `dim End A = 1`. -/
noncomputable def endScalar (A : C) (h1 : finrank ℂ (A ⟶ A) = 1) : End A ≃ₐ[ℂ] ℂ :=
  haveI : Nontrivial (End A) := nontrivial_of_ne (1 : End A) 0 (id_ne_zero_of_finrank_one h1)
  (AlgEquiv.ofBijective (Algebra.ofId ℂ (End A))
    ⟨(algebraMap ℂ (End A)).injective, fun f => by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 A)
        (id_ne_zero_of_finrank_one h1)).mp h1 f
      exact ⟨c, by rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]; exact hc⟩⟩).symm

/-- **`End(Y ⊞ Y) ≅ M₂(End Y)`**: the `(a, b)` entry is the component from the `b`-th to the
`a`-th summand. -/
noncomputable def endBiprodSelf (Y : C) : End (Y ⊞ Y) ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) (End Y) where
  toFun φ := !![biprod.inl ≫ φ ≫ biprod.fst, biprod.inr ≫ φ ≫ biprod.fst;
    biprod.inl ≫ φ ≫ biprod.snd, biprod.inr ≫ φ ≫ biprod.snd]
  invFun M := Biprod.ofComponents (M 0 0) (M 1 0) (M 0 1) (M 1 1)
  left_inv φ := by
    show Biprod.ofComponents (biprod.inl ≫ φ ≫ biprod.fst) (biprod.inl ≫ φ ≫ biprod.snd)
      (biprod.inr ≫ φ ≫ biprod.fst) (biprod.inr ≫ φ ≫ biprod.snd) = φ
    exact Biprod.ofComponents_eq φ
  right_inv M := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  map_mul' φ ψ := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases a <;> fin_cases b
    · exact entry_mul biprod.inl biprod.fst φ ψ
    · exact entry_mul biprod.inr biprod.fst φ ψ
    · exact entry_mul biprod.inl biprod.snd φ ψ
    · exact entry_mul biprod.inr biprod.snd φ ψ
  map_add' φ ψ := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [end_add_eq, Preadditive.add_comp, Preadditive.comp_add]
  commutes' c := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.algebraMap_matrix_apply, algebraMap_end_eq]

/-- **`End(P₀ ⊞ (X ⊞ (Y ⊞ Y))) ≅ ℂ × ℂ × M₂(ℂ)`** (line 3799, `H = 𝟙 ⊕ X ⊕ 2Y`), for objects with
one-dimensional endomorphism spaces and zero Hom spaces between distinct ones (Schur). -/
noncomputable def endHIso (P₀ X Y : C) (h0 : finrank ℂ (P₀ ⟶ P₀) = 1)
    (hX : finrank ℂ (X ⟶ X) = 1) (hY : finrank ℂ (Y ⟶ Y) = 1)
    (h0X : Subsingleton (P₀ ⟶ X)) (hX0 : Subsingleton (X ⟶ P₀))
    (h0Y : Subsingleton (P₀ ⟶ Y)) (hY0 : Subsingleton (Y ⟶ P₀))
    (hXY : Subsingleton (X ⟶ Y)) (hYX : Subsingleton (Y ⟶ X)) :
    End (P₀ ⊞ (X ⊞ (Y ⊞ Y))) ≃ₐ[ℂ] CCM2 :=
  haveI : Subsingleton (X ⟶ Y ⊞ Y) := subsingleton_hom_biprod hXY hXY
  haveI : Subsingleton (Y ⊞ Y ⟶ X) := subsingleton_biprod_hom hYX hYX
  haveI : Subsingleton (P₀ ⟶ X ⊞ (Y ⊞ Y)) :=
    subsingleton_hom_biprod h0X (subsingleton_hom_biprod h0Y h0Y)
  haveI : Subsingleton (X ⊞ (Y ⊞ Y) ⟶ P₀) :=
    subsingleton_biprod_hom hX0 (subsingleton_biprod_hom hY0 hY0)
  (endBiprodOrth P₀ (X ⊞ (Y ⊞ Y))).trans ((endScalar P₀ h0).prodCongr
    ((endBiprodOrth X (Y ⊞ Y)).trans ((endScalar X hX).prodCongr
      ((endBiprodSelf Y).trans (endScalar Y hY).mapMatrix))))

section Schur

variable [HasKernels C] [∀ A B : C, FiniteDimensional ℂ (A ⟶ B)]

omit [HasBinaryBiproducts C] in
theorem subsingleton_hom_of_not_iso {A B : C} [Simple A] [Simple B] (h : (A ≅ B) → False) :
    Subsingleton (A ⟶ B) :=
  Module.finrank_zero_iff.mp (finrank_hom_simple_simple_eq_zero_of_not_iso ℂ h)

/-- **Schur's lemma version**: for simple, pairwise non-isomorphic `P₀, X, Y`,
`End(P₀ ⊞ (X ⊞ (Y ⊞ Y))) ≅ ℂ × ℂ × M₂(ℂ)` as `ℂ`-algebras. -/
noncomputable def endHIsoOfSimple (P₀ X Y : C) [Simple P₀] [Simple X] [Simple Y]
    (h0X : (P₀ ≅ X) → False) (h0Y : (P₀ ≅ Y) → False) (hXY : (X ≅ Y) → False) :
    End (P₀ ⊞ (X ⊞ (Y ⊞ Y))) ≃ₐ[ℂ] CCM2 :=
  endHIso P₀ X Y (finrank_endomorphism_simple_eq_one ℂ P₀) (finrank_endomorphism_simple_eq_one ℂ X)
    (finrank_endomorphism_simple_eq_one ℂ Y) (subsingleton_hom_of_not_iso h0X)
    (subsingleton_hom_of_not_iso fun e => h0X e.symm) (subsingleton_hom_of_not_iso h0Y)
    (subsingleton_hom_of_not_iso fun e => h0Y e.symm) (subsingleton_hom_of_not_iso hXY)
    (subsingleton_hom_of_not_iso fun e => hXY e.symm)

end Schur

/-- Conjugation by an isomorphism `H ≅ H'` as an isomorphism of `ℂ`-algebras `End H ≅ End H'`. -/
noncomputable def conjAlg {H H' : C} (e : H ≅ H') : End H ≃ₐ[ℂ] End H' where
  toFun f := e.inv ≫ f ≫ e.hom
  invFun g := e.hom ≫ g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_mul' f g := by
    show e.inv ≫ (g ≫ f) ≫ e.hom = (e.inv ≫ g ≫ e.hom) ≫ (e.inv ≫ f ≫ e.hom)
    simp
  map_add' f g := by simp [end_add_eq, Preadditive.add_comp, Preadditive.comp_add]
  commutes' c := by simp [algebraMap_end_eq]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[external] Bischoff–Jones, Corollary 3.4** (with Lemma 3.1): for the canonical Lagrangian
algebra `H = I(𝟙)` of `𝒞 ≃ Z(𝓕)`, the complexified fusion algebra `K₀(𝓕) ⊗ ℂ` (coefficient
vectors `ι → ℂ` with the fusion product `BasedRing.mul`) is isomorphic, as a unital `ℂ`-algebra,
to `End_𝒞(H)` with composition (`f * g = f ∘ g`). -/
structure BJIso (R : BasedRing ι) (H : C) where
  Φ : (ι → ℂ) ≃ₗ[ℂ] End H
  map_mul : ∀ x y, Φ (R.mul x y) = Φ x * Φ y
  map_one : Φ (Pi.single R.unit 1) = 1

/-- **The `FusionAlgebraIso` of line 3799** from the external Bischoff–Jones identification and
the decomposition `H ≅ P₀ ⊞ (X ⊞ (Y ⊞ Y))` (`H↓U = 𝟙 ⊕ X ⊕ 2Y`), with the Schur data of
`P₀ = 𝟙, X, Y`. -/
noncomputable def fusionAlgebraIsoOfSchur (R : BasedRing ι) {H : C} (P₀ X Y : C)
    (bj : BJIso R H) (e : H ≅ P₀ ⊞ (X ⊞ (Y ⊞ Y))) (h0 : finrank ℂ (P₀ ⟶ P₀) = 1)
    (hX : finrank ℂ (X ⟶ X) = 1) (hY : finrank ℂ (Y ⟶ Y) = 1)
    (h0X : Subsingleton (P₀ ⟶ X)) (hX0 : Subsingleton (X ⟶ P₀))
    (h0Y : Subsingleton (P₀ ⟶ Y)) (hY0 : Subsingleton (Y ⟶ P₀))
    (hXY : Subsingleton (X ⟶ Y)) (hYX : Subsingleton (Y ⟶ X)) : FusionAlgebraIso R where
  Φ := bj.Φ.trans
    ((conjAlg e).trans (endHIso P₀ X Y h0 hX hY h0X hX0 h0Y hY0 hXY hYX)).toLinearEquiv
  map_mul x y := by
    simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, bj.map_mul, map_mul]
  map_one := by
    simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, bj.map_one, map_one]

/-- The same, for simple pairwise non-isomorphic `P₀ = 𝟙, X, Y` (Mathlib's Schur lemma). -/
noncomputable def fusionAlgebraIsoOfSimple [HasKernels C] [∀ A B : C, FiniteDimensional ℂ (A ⟶ B)]
    (R : BasedRing ι) {H : C} (P₀ X Y : C) [Simple P₀] [Simple X] [Simple Y]
    (bj : BJIso R H) (e : H ≅ P₀ ⊞ (X ⊞ (Y ⊞ Y)))
    (h0X : (P₀ ≅ X) → False) (h0Y : (P₀ ≅ Y) → False) (hXY : (X ≅ Y) → False) :
    FusionAlgebraIso R :=
  fusionAlgebraIsoOfSchur R P₀ X Y bj e (finrank_endomorphism_simple_eq_one ℂ P₀)
    (finrank_endomorphism_simple_eq_one ℂ X) (finrank_endomorphism_simple_eq_one ℂ Y)
    (subsingleton_hom_of_not_iso h0X) (subsingleton_hom_of_not_iso fun e => h0X e.symm)
    (subsingleton_hom_of_not_iso h0Y) (subsingleton_hom_of_not_iso fun e => h0Y e.symm)
    (subsingleton_hom_of_not_iso hXY) (subsingleton_hom_of_not_iso fun e => hXY e.symm)

#print axioms endBiprodOrth
#print axioms endScalar
#print axioms endBiprodSelf
#print axioms endHIso
#print axioms endHIsoOfSimple
#print axioms fusionAlgebraIsoOfSchur
#print axioms fusionAlgebraIsoOfSimple

end HaagerupIzumi.C8.Fusion
