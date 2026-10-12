module

public import HaagerupIzumi.C8.Category.NondegFromSeparable
public import HaagerupIzumi.C8.Category.FreeModuleMonoidalEquivalence

@[expose] public section

/-! # The `L_untwisted` identification from categorical hypotheses on `Rep(B)` and `H/B`

Collects the identification step of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`,
lines 3335–3352) and the count `9/3 = 3` of Proposition `clm:analytic-net-count`
(lines 4383–4406) under hypotheses that are structural statements about the pointed category
`Rep(B)` and the algebra `A = H/B`, with no VOA input:

* `hSchur`: the nine invertibles `S v` (`v ∈ (ℤ/3)²`) have `dim Hom(S v, S w) = δ_{v,w}`;
* `hfusion`: `S v ⊗ S w ≅ S (v + w)`; `hunitS`: `S (0, 0) ≅ 𝟙_ C`;
* `hA`: `A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` as an object (`H/B` is supported on `L₊`);
* `hS`: a separability section of `A` (`H/B` is a connected étale, hence separable, algebra;
  the section must be supplied from outside, e.g. from the Q-system structure of `H/B`:
  `twistedSeparabilitySection` presupposes `hmul` and so cannot be used to derive `hnondeg`);
* `3 ≠ 0` in `𝕜`; `hss`: every object is a finite sum of the `S v`; `IsIdempotentComplete C`
  (true in every abelian category).

* `hunit_of_unitS`: the unit of `A` factors through `S (0, 0)` (`Hom(𝟙, S (c, c)) = 0` for
  `c ≠ 0`, by `hSchur` and `hunitS`).
* `netCount_simple_modules_of_separable`: the simple `A`-modules are exactly the three free
  modules `S (a, -a) ⊗ A`, pairwise non-isomorphic.
* `freeLminus_monoidalEquivalence_of_separable` (braided `C`, commutative `A`, coequalizers
  preserved by `X ⊗ -`, `- ⊗ X`): free induction is a monoidal equivalence from the additive
  closure of `L₋` onto the module category `𝒞_A ⊂ (Bimod A A, ⊗_A)`.

What remains external: the facts behind the hypotheses (the structure of `Rep(B)` as a pointed
fusion category with fusion group `(ℤ/3)²`, the support of `H/B`, its separability).

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

section Unit

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] {A : Mon C} {S : ZMod 3 × ZMod 3 → C}

/-- **The unit of `A` lies in `S (0, 0)`**: with `S (0, 0) ≅ 𝟙_ C`, `Hom(𝟙_ C, S (c, c)) = 0`
for `c ≠ 0`. -/
theorem hunit_of_unitS (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hunitS : S (0, 0) ≅ 𝟙_ C) (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) :
    ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0 := by
  refine ⟨η[A.X] ≫ summandProj hA 0, ?_⟩
  have hzero : ∀ c : ZMod 3, c ≠ 0 → η[A.X] ≫ summandProj hA c = 0 := by
    intro c hc
    have h0 : finrank 𝕜 (𝟙_ C ⟶ S (c, c)) = 0 := by
      rw [(Linear.homCongr 𝕜 hunitS.symm (Iso.refl (S (c, c)))).finrank_eq, hSchur, if_neg]
      intro h
      exact hc (congrArg Prod.fst h).symm
    have : Subsingleton (𝟙_ C ⟶ S (c, c)) := Module.finrank_zero_iff.1 h0
    exact Subsingleton.elim _ _
  calc η[A.X] = η[A.X] ≫ ∑ c, summandProj hA c ≫ summandIncl hA c := by
        rw [summand_total, Category.comp_id]
    _ = ∑ c, (η[A.X] ≫ summandProj hA c) ≫ summandIncl hA c := by
        rw [Preadditive.comp_sum]
        simp only [Category.assoc]
    _ = (η[A.X] ≫ summandProj hA 0) ≫ summandIncl hA 0 := by
        refine Finset.sum_eq_single 0 (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ _) h)
        rw [hzero c hc, zero_comp]

variable [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [IsIdempotentComplete C]

/-- **The count `9/3 = 3` from categorical hypotheses**: the simple modules over a separable
`A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` are exactly the three free modules `S (a, -a) ⊗ A`, pairwise
non-isomorphic. -/
theorem netCount_simple_modules_of_separable
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (hS : SeparabilitySection A) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (∀ a : ZMod 3, Simple (free A (S (a, -a)))) ∧
      (∀ a b : ZMod 3, Nonempty (free A (S (a, -a)) ≅ free A (S (b, -b))) ↔ a = b) ∧
      ∀ M : RightMod A, Simple M → ∃! a : ZMod 3, Nonempty (M ≅ free A (S (a, -a))) :=
  netCount_simple_modules_separable 𝕜 hSchur hfusion hA hS
    (hunit_of_unitS 𝕜 hSchur hunitS hA) hunitS h3 hss

/-- Free induction from the additive closure of `L₋` is an equivalence onto `RightMod A`,
from categorical hypotheses. -/
theorem freeLminus_isEquivalence_of_separable
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (hS : SeparabilitySection A) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (freeLminus A S).IsEquivalence :=
  freeLminus_isEquivalence_separable 𝕜 hSchur hfusion hA hS
    (hunit_of_unitS 𝕜 hSchur hunitS hA) hunitS h3 hss

end Unit

section MonoidalEquivalence

variable [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : Mon C) [IsCommMonObj A.X] [MonoidalPreadditive C]
  (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [IsIdempotentComplete C] {S : ZMod 3 × ZMod 3 → C}

attribute [local instance] bimodMonoidal

/-- **Free `H/B`-module induction is a monoidal equivalence** (manuscript lines 3335–3352)
from categorical hypotheses: the additive closure of `L₋` (monoidal by `hfusion`, `hunitS`) is
monoidally equivalent, by free induction, to the module category `𝒞_A ⊂ (Bimod A A, ⊗_A)`. -/
theorem freeLminus_monoidalEquivalence_of_separable
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (hS : SeparabilitySection A) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    haveI := lminusClosure_isMonoidal hfusion hunitS
    ∃ (e : (LminusClosure S).FullSubcategory ≌ (toBimod A).essImage.FullSubcategory)
      (h : e.functor.Monoidal),
        (letI := h; letI := e.inverseMonoidal; e.IsMonoidal) ∧
          e.functor ⋙ (toBimod A).essImage.ι = freeLminus A S ⋙ toBimod A := by
  have := lminusClosure_isMonoidal hfusion hunitS
  have hE := freeLminus_isEquivalence_of_separable 𝕜 hSchur hfusion hunitS hA hS h3 hss
  exact ⟨freeLminusMonoidalEquivalence A S hE,
    freeLminusMonoidalEquivalence_functorMonoidal A S hE,
    freeLminusMonoidalEquivalence_isMonoidal A S hE, rfl⟩

end MonoidalEquivalence

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.hunit_of_unitS
#print axioms HaagerupIzumi.C8.RightMod.netCount_simple_modules_of_separable
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_isEquivalence_of_separable
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_monoidalEquivalence_of_separable
