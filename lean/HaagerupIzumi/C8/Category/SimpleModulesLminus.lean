module

public import HaagerupIzumi.C8.Category.FreeModuleEquivalence
public import Mathlib.CategoryTheory.Simple

@[expose] public section

/-! # The count `9/3 = 3`: the simple `Q₊`-modules are the three free modules on `L₋`

Categorical step of Proposition `clm:analytic-net-count` (manuscript `haagerup_c8_expanded.tex`,
lines 4383–4406; the same argument is the identification step of `L_untwisted`, lines
3337–3348): "The target has dimension `9/3 = 3`, so these three distinct invertible images
exhaust its simple objects."  Instead of the dimension count we use the equivalence of
`Category/FreeModuleEquivalence.lean`: every module is a free module on a finite direct sum
of the three invertibles of `L₋`, and free induction is fully faithful there.  With
`F_a = free A (S (a, -a))` (`a ∈ ℤ/3`) and Mathlib's `Simple` in the preadditive category
`𝒞_A = RightMod A`:

* `finrank_end_free_Lminus`, `free_Lminus_id_ne_zero`: `End_A(F_a)` is one-dimensional.
* `free_Lminus_iso_iff`: `F_a ≅ F_b ↔ a = b` (pairwise non-isomorphic: `Hom_A(F_a, F_b) = 0`
  for `a ≠ b`).
* `simple_free_Lminus`: each `F_a` is simple (a nonzero mono `Y ⟶ F_a` is split by a free
  map, by full faithfulness and Schur on the summands).
* `simple_iso_free_Lminus`: every simple module is isomorphic to some `F_a` (it is a free
  module on a nonempty sum of `L₋`-invertibles, and the inclusion of one summand is a
  nonzero split mono).
* `netCount_simple_modules`: **the simple `Q₊`-modules are exactly the three free modules
  `F_a`, pairwise non-isomorphic**: every `F_a` is simple, `F_a ≅ F_b ↔ a = b`, and every
  simple module is isomorphic to `F_a` for exactly one `a ∈ ℤ/3` (`ZMod.card 3 = 3`).

Hypotheses: those of `freeLminus_isEquivalence` (`Category/FreeModuleEquivalence.lean`):
`hSchur`, `hfusion`, `hA` (the pointed category `Rep(B)` and `H/B = Q₊` as an object), `hmul`
(the homogeneous components of the multiplication of `Q₊` are nonzero), `3 ≠ 0` in `𝕜`, `hss`
(every object is a finite sum of the nine invertibles), `hsplit` (idempotents of sums of
`L₋`-invertibles split through sub-sums).  No certificate inputs.  Not formalized: the embedding
into `𝓕_net`.  For the tensor structure: free induction is a monoidal equivalence onto `𝒞_A`
(`Category/FreeModuleMonoidalEquivalence.lean`).

Status of the Tannakian step for `L₋` (4 October 2026): the abelian 3-cocycle of the pointed
braided category on the invertibles `S (a, -a)` is constructed in `Category/PointedCocycle.lean`
(`pentagon_scalar`, `hexagon_forward_scalar`, `hexagon_reverse_scalar`) and trivialized in
`Category/PointedCocycleZ3.lean` (`Lminus_untwisted_symmetric`); the resulting braided monoidal
functor from the symmetric discrete `ℤ/3` is `Lminus_braided_vec`
(`Category/LminusBraidedVec.lean`), and into `LminusClosure S` with its own monoidal structure
and inherited braiding it is `Lminus_closure_braided_functor`
(`Category/LminusClosureFunctor.lean`); `LminusClosure S` is symmetric and equivalent, as a
category, to the additive envelope of its simples (`Category/LminusEnvelope.lean`).  Remaining
external: `hθ` (the self-braiding of each invertible of `L₋` in `Rep(B)` is trivial).  The monoidal comparison on general graded objects is
`GrMat.Lminus_graded_braided_equivalence` and `Lminus_vec_braided_equivalence`
(`Category/GradedMat.lean`, `Category/GradedMatMonoidal.lean`).  Composed with free induction it is
`untwisted_vec_equivalence_of_separable` (`Category/UntwistedVecEquivalence.lean`). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]
  {A : Mon C} {S : ZMod 3 × ZMod 3 → C}
  (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
  (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
  (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))

section Schur

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] in
include hSchur in
/-- A nonzero endomorphism of an invertible `S v` is an isomorphism (`End(S v) = 𝕜`). -/
theorem isIso_of_ne_zero_self (v : ZMod 3 × ZMod 3) (φ : S v ⟶ S v) (hφ : φ ≠ 0) : IsIso φ := by
  have h1 : finrank 𝕜 (S v ⟶ S v) = 1 := by rw [hSchur, if_pos rfl]
  have hid : (𝟙 (S v) : S v ⟶ S v) ≠ 0 := id_ne_zero_of_finrank_eq_one 𝕜 h1
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 (S v)) hid).1 h1 φ
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hφ ht.symm
  refine ⟨⟨t⁻¹ • 𝟙 (S v), ?_, ?_⟩⟩
  · rw [← ht, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
      mul_inv_cancel₀ ht0, one_smul]
  · rw [← ht, Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul,
      inv_mul_cancel₀ ht0, one_smul]

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] in
include hSchur in
/-- A nonzero morphism `S (c, -c) ⟶ S (a, -a)` forces `c = a`. -/
theorem eq_of_hom_ne_zero {c a : ZMod 3} (φ : S (c, -c) ⟶ S (a, -a)) (hφ : φ ≠ 0) : c = a := by
  by_contra hne
  have h0 : finrank 𝕜 (S (c, -c) ⟶ S (a, -a)) = 0 := by
    rw [hSchur, if_neg]
    intro h
    exact hne (congrArg Prod.fst h)
  have : Subsingleton (S (c, -c) ⟶ S (a, -a)) := Module.finrank_zero_iff.1 h0
  exact hφ (Subsingleton.elim _ _)

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] in
include hSchur in
/-- A nonzero morphism between invertibles of `L₋` is an isomorphism. -/
theorem isIso_of_hom_ne_zero {c a : ZMod 3} (φ : S (c, -c) ⟶ S (a, -a)) (hφ : φ ≠ 0) :
    IsIso φ := by
  have hca := eq_of_hom_ne_zero 𝕜 hSchur φ hφ
  subst hca
  exact isIso_of_ne_zero_self 𝕜 hSchur _ φ hφ

end Schur

section FreeLminus

omit [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] in
/-- Free induction preserves identities. -/
theorem freeMap_id' (X : C) : freeMap A (𝟙 X) = 𝟙 (free A X) :=
  hom_ext (by
    show 𝟙 X ▷ A.X = 𝟙 (X ⊗ A.X)
    exact MonoidalCategory.id_whiskerRight X A.X)

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] in
/-- Free induction preserves zero morphisms. -/
theorem freeMap_zero (X Y : C) : freeMap A (0 : X ⟶ Y) = 0 :=
  hom_ext (by
    show (0 : X ⟶ Y) ▷ A.X = 0
    exact MonoidalPreadditive.zero_whiskerRight)

include hSchur hfusion hA in
/-- `End_A(F_a)` is one-dimensional. -/
theorem finrank_end_free_Lminus (a : ZMod 3) :
    finrank 𝕜 (free A (S (a, -a)) ⟶ free A (S (a, -a))) = 1 := by
  rw [finrank_hom_free_Lminus 𝕜 A S hSchur hfusion hA, if_pos rfl]

include hSchur hfusion hA in
theorem free_Lminus_id_ne_zero (a : ZMod 3) : (𝟙 (free A (S (a, -a))) : _ ⟶ _) ≠ 0 :=
  id_ne_zero_of_finrank_eq_one 𝕜 (finrank_end_free_Lminus 𝕜 hSchur hfusion hA a)

include hSchur hfusion hA in
/-- `Hom_A(F_a, F_b) = 0` for `a ≠ b`. -/
theorem free_Lminus_hom_eq_zero {a b : ZMod 3} (hab : a ≠ b)
    (f : free A (S (a, -a)) ⟶ free A (S (b, -b))) : f = 0 := by
  have h0 : finrank 𝕜 (free A (S (a, -a)) ⟶ free A (S (b, -b))) = 0 := by
    rw [finrank_hom_free_Lminus 𝕜 A S hSchur hfusion hA, if_neg hab]
  have : FiniteDimensional 𝕜 (free A (S (a, -a)) ⟶ free A (S (b, -b))) :=
    LinearEquiv.finiteDimensional (freeHomLinearEquiv 𝕜 A _ _).symm
  have : Subsingleton (free A (S (a, -a)) ⟶ free A (S (b, -b))) := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

include hSchur hfusion hA in
/-- **The three free modules on `L₋` are pairwise non-isomorphic**: `F_a ≅ F_b ↔ a = b`. -/
theorem free_Lminus_iso_iff (a b : ZMod 3) :
    Nonempty (free A (S (a, -a)) ≅ free A (S (b, -b))) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    by_contra hab
    apply free_Lminus_id_ne_zero 𝕜 hSchur hfusion hA a
    rw [← e.hom_inv_id, free_Lminus_hom_eq_zero 𝕜 hSchur hfusion hA hab e.hom, zero_comp]
  · rintro rfl
    exact ⟨Iso.refl _⟩

omit [MonoidalCategory C] [MonoidalPreadditive C] in
/-- `S (a, -a)` lies in the additive closure of `L₋`. -/
theorem single_mem_LminusClosure (a : ZMod 3) : LminusClosure S (S (a, -a)) :=
  ⟨1, fun _ => a, ⟨(biproductUniqueIso (fun _ : Fin 1 => S (a, -a))).symm⟩⟩

variable (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
  (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
    Nonempty (X ≅ ⨁ fun j => S (v j)))
  (hsplit : ∀ (n : ℕ) (a : Fin n → ZMod 3)
    (e : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun j => S (a j, -a j))), e ≫ e = e →
      ∃ (m : ℕ) (b : Fin m → ZMod 3)
        (R : Retract (⨁ fun k => S (b k, -b k)) (⨁ fun j => S (a j, -a j))), R.r ≫ R.i = e)

include hSchur hfusion hmul h3 hss hsplit in
/-- **Each `F_a = S (a, -a) ⊗ A` is a simple `A`-module.** -/
theorem simple_free_Lminus (a : ZMod 3) : Simple (free A (S (a, -a))) := by
  refine ⟨fun {Y} f _ => ⟨fun hiso h0 => ?_, fun hne => ?_⟩⟩
  · apply free_Lminus_id_ne_zero 𝕜 hSchur hfusion hA a
    calc 𝟙 _ = inv f ≫ f := (IsIso.inv_hom_id f).symm
      _ = inv f ≫ 0 := congrArg (fun k => inv f ≫ k) h0
      _ = 0 := comp_zero
  · obtain ⟨m, b, ⟨e⟩⟩ :=
      free_essSurj_Lminus_of_mul_ne_zero 𝕜 hSchur hfusion hA hmul h3 hss hsplit Y
    obtain ⟨g, hg⟩ := (freeFunctor_bijective_LminusClosure 𝕜 hSchur hfusion hA
      ⟨m, b, ⟨Iso.refl _⟩⟩ (single_mem_LminusClosure a)).2 (e.inv ≫ f)
    have hg' : (freeFunctor A).map g = e.inv ≫ f := hg
    have hg0 : g ≠ 0 := by
      intro h
      apply hne
      have : e.inv ≫ f = 0 := by
        rw [← hg', h]
        exact Functor.map_zero _ _ _
      rw [← Category.id_comp f, ← e.hom_inv_id, Category.assoc, this, comp_zero]
    obtain ⟨k, hk⟩ : ∃ k, biproduct.ι (fun k => S (b k, -b k)) k ≫ g ≠ 0 := by
      by_contra hall
      apply hg0
      refine biproduct.hom_ext' _ _ fun k => ?_
      rw [comp_zero]
      by_contra hk
      exact hall ⟨k, hk⟩
    have hiso := isIso_of_hom_ne_zero 𝕜 hSchur _ hk
    let r : S (a, -a) ⟶ ⨁ fun k => S (b k, -b k) :=
      inv (biproduct.ι (fun k => S (b k, -b k)) k ≫ g) ≫ biproduct.ι (fun k => S (b k, -b k)) k
    have hr : r ≫ g = 𝟙 _ := by simp only [r, Category.assoc, IsIso.inv_hom_id]
    have hg'' : freeMap A g = e.inv ≫ f := hg
    have hsec : freeMap A r ≫ (e.inv ≫ f) = 𝟙 _ := by
      rw [← hg'', ← freeMap_comp, hr, freeMap_id']
    have hmono : Mono (e.inv ≫ f) := mono_comp _ _
    have hret : (e.inv ≫ f) ≫ freeMap A r = 𝟙 _ := by
      apply (cancel_mono (e.inv ≫ f)).1
      rw [Category.assoc (e.inv ≫ f) (freeMap A r) (e.inv ≫ f), hsec, Category.comp_id,
        Category.id_comp]
    have : IsIso (e.inv ≫ f) := ⟨⟨freeMap A r, hret, hsec⟩⟩
    have : f = e.hom ≫ (e.inv ≫ f) := by rw [Iso.hom_inv_id_assoc]
    rw [this]
    infer_instance

include hSchur hfusion hmul h3 hss hsplit in
/-- **Every simple `A`-module is isomorphic to some `F_a`.** -/
theorem simple_iso_free_Lminus (M : RightMod A) [Simple M] :
    ∃ a : ZMod 3, Nonempty (M ≅ free A (S (a, -a))) := by
  obtain ⟨m, b, ⟨e⟩⟩ :=
    free_essSurj_Lminus_of_mul_ne_zero 𝕜 hSchur hfusion hA hmul h3 hss hsplit M
  obtain _ | k := m
  · exfalso
    apply id_nonzero M
    have h0 : 𝟙 (⨁ fun j => S (b j, -b j)) = 0 :=
      biproduct.hom_ext' _ _ fun j => Fin.elim0 j
    have h1 : 𝟙 (free A (⨁ fun j => S (b j, -b j))) = 0 := by
      rw [← freeMap_id', h0, freeMap_zero]
    rw [← e.hom_inv_id, ← Category.id_comp e.inv, h1, zero_comp, comp_zero]
  · have hιπ : freeMap A (biproduct.ι (fun j => S (b j, -b j)) 0) ≫
        freeMap A (biproduct.π (fun j => S (b j, -b j)) 0) = 𝟙 _ := by
      rw [← freeMap_comp, biproduct.ι_π_self, freeMap_id']
    have hsplit' : (freeMap A (biproduct.ι (fun j => S (b j, -b j)) 0) ≫ e.inv) ≫
        (e.hom ≫ freeMap A (biproduct.π (fun j => S (b j, -b j)) 0)) = 𝟙 _ := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hιπ]
    have : IsSplitMono (freeMap A (biproduct.ι (fun j => S (b j, -b j)) 0) ≫ e.inv) :=
      IsSplitMono.mk' ⟨_, hsplit'⟩
    have hne : freeMap A (biproduct.ι (fun j => S (b j, -b j)) 0) ≫ e.inv ≠ 0 := by
      intro h
      apply free_Lminus_id_ne_zero 𝕜 hSchur hfusion hA (b 0)
      rw [← hsplit', h, zero_comp]
    have := isIso_of_mono_of_nonzero hne
    exact ⟨b 0, ⟨(asIso (freeMap A (biproduct.ι (fun j => S (b j, -b j)) 0) ≫ e.inv)).symm⟩⟩

include hSchur hfusion hmul h3 hss hsplit in
/-- **The count `9/3 = 3`** (Proposition `clm:analytic-net-count`, lines 4383–4406; `L_untwisted`,
lines 3337–3348): the simple modules over `Q₊ = H/B` are exactly the three free modules
`F_a = S (a, -a) ⊗ Q₊` on the invertibles of `L₋`, and these are pairwise non-isomorphic.
That is: every `F_a` is simple, `F_a ≅ F_b ↔ a = b`, and every simple module is isomorphic to
`F_a` for exactly one `a ∈ ℤ/3`. -/
theorem netCount_simple_modules :
    (∀ a : ZMod 3, Simple (free A (S (a, -a)))) ∧
      (∀ a b : ZMod 3, Nonempty (free A (S (a, -a)) ≅ free A (S (b, -b))) ↔ a = b) ∧
      ∀ M : RightMod A, Simple M → ∃! a : ZMod 3, Nonempty (M ≅ free A (S (a, -a))) := by
  refine ⟨simple_free_Lminus 𝕜 hSchur hfusion hA hmul h3 hss hsplit,
    free_Lminus_iso_iff 𝕜 hSchur hfusion hA, fun M hM => ?_⟩
  obtain ⟨a, ⟨e⟩⟩ := simple_iso_free_Lminus 𝕜 hSchur hfusion hA hmul h3 hss hsplit M
  refine ⟨a, ⟨e⟩, fun b ⟨e'⟩ => ?_⟩
  exact ((free_Lminus_iso_iff 𝕜 hSchur hfusion hA b a).1 ⟨e'.symm ≪≫ e⟩)

/-- There are exactly three classes: `ℤ/3` has three elements. -/
theorem card_Lminus : Fintype.card (ZMod 3) = 3 := ZMod.card 3

end FreeLminus

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.isIso_of_hom_ne_zero
#print axioms HaagerupIzumi.C8.RightMod.free_Lminus_iso_iff
#print axioms HaagerupIzumi.C8.RightMod.simple_free_Lminus
#print axioms HaagerupIzumi.C8.RightMod.simple_iso_free_Lminus
#print axioms HaagerupIzumi.C8.RightMod.netCount_simple_modules
#print axioms HaagerupIzumi.C8.RightMod.card_Lminus
