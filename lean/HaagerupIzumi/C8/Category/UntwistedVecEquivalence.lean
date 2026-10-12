module

public import HaagerupIzumi.C8.Category.GradedMatMonoidal
public import HaagerupIzumi.C8.Category.UntwistedFromSeparable

@[expose] public section

/-! # `L_untwisted`: the category of `H/B`-modules is the untwisted `Vec_{ℤ/3}`

Composition of the two comparisons:

* `Lminus_vec_braided_equivalence` (`Category/GradedMatMonoidal.lean`): the realization of
  finite-dimensional `ℤ/3`-graded spaces (`GrMat (ℤ/3) 𝕜`, with its canonical untwisted
  symmetric structure: Kronecker tensor product, trivial associator, swap braiding) lifts to a
  braided monoidal equivalence onto the additive closure `LminusClosure S` of `L₋`;
* `freeLminus_monoidalEquivalence_of_separable` (`Category/UntwistedFromSeparable.lean`): free
  induction `X ↦ X ⊗ A` is a monoidal equivalence from `LminusClosure S` onto the module
  category `𝒞_A ⊂ (Bimod A A, ⊗_A)` (the essential image of `toBimod A`).

`untwisted_vec_equivalence_of_separable`: **the category `𝒞_A` of all `A = H/B`-modules is
monoidally equivalent to the untwisted `Vec_{ℤ/3}`** (manuscript, `L_untwisted`, lines
3335–3352), the functor being `X ↦ (⨁_{i ∈ X.I} S (deg i, -deg i)) ⊗ A`.  The braided part
is recorded on the `Vec_{ℤ/3} ≃ LminusClosure S` leg; `𝒞_A` carries no braiding in this
formalization (a braiding exists only on local modules), so the composite is stated as a
monoidal equivalence, the source being symmetric (`GrMat.instSymmetricCategory`).

Hypotheses: those of `freeLminus_monoidalEquivalence_of_separable` (pointed structure `hSchur`,
`hfusion`, `hunitS`; support `hA`; separability section `hS`; `3 ≠ 0`; `hss`; braided `C` with
coequalizers preserved by `X ⊗ -` and `- ⊗ X`; commutative `A`; finite-dimensional Hom spaces;
`IsIdempotentComplete C`) and **[external]** `hθ` (trivial self-braidings on `L₋`). -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module RightMod

universe v u

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence whose functor is monoidal is a monoidal equivalence for the inverse's
`Equivalence.inverseMonoidal` structure (Mathlib's `example` after
`Equivalence.inverseMonoidal`, stated as a lemma). -/
theorem equivalence_isMonoidal_inverseMonoidal {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂] (E : D₁ ≌ D₂) (h : E.functor.Monoidal) :
    letI := h
    letI := E.inverseMonoidal
    E.IsMonoidal := by
  let := h
  let := E.inverseMonoidal
  infer_instance

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
  [HasFiniteBiproducts C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : Mon C) [IsCommMonObj A.X] [MonoidalPreadditive C]
  (𝕜 : Type) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [IsIdempotentComplete C]

attribute [local instance] bimodMonoidal

/-- **`L_untwisted`: the module category of `H/B` is monoidally equivalent to the untwisted
`Vec_{ℤ/3}`.**  There are a functor `G : Discrete (ℤ/3) ⥤ C` with `G (a) = S (a, -a)` and an
equivalence `E : GrMat (ℤ/3) 𝕜 ≌ 𝒞_A` (`𝒞_A` = essential image of `toBimod A` in
`(Bimod A A, ⊗_A)`) such that

* `E.functor` is monoidal and `E` is a monoidal equivalence (`Equivalence.IsMonoidal`, inverse
  with `Equivalence.inverseMonoidal`), the source carrying the canonical untwisted symmetric
  structure (`GrMat.instMonoidalCategory`, `GrMat.instSymmetricCategory`).  The
  `E.IsMonoidal` conjunct is automatic given `h`
  (`equivalence_isMonoidal_inverseMonoidal`); it is recorded for citation;
* `E.functor` is realization followed by free induction:
  `E.functor ⋙ 𝒞_A.ι = (LminusClosure S).lift (real G) _ ⋙ freeLminus A S ⋙ toBimod A`;
* its first leg `(LminusClosure S).lift (real G) _ : GrMat (ℤ/3) 𝕜 ⥤ LminusClosure S` is a
  braided monoidal functor (target with the monoidal structure of `lminusClosure_isMonoidal` and
  the inherited braiding).

Inputs: `hSchur`, `hfusion`, `hunitS`, `hA`, `hS`, `h3`, `hss` and **[external]** `hθ`. -/
theorem untwisted_vec_equivalence_of_separable (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (hS : SeparabilitySection A) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j)))
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) :
    haveI := lminusClosure_isMonoidal hfusion hunitS
    ∃ (G : Discrete (Multiplicative (ZMod 3)) ⥤ C)
      (hmem : ∀ X : GrMat (Multiplicative (ZMod 3)) 𝕜, LminusClosure S ((GrMat.real G).obj X))
      (E : GrMat (Multiplicative (ZMod 3)) 𝕜 ≌ (toBimod A).essImage.FullSubcategory)
      (h : E.functor.Monoidal),
      (∀ a : ZMod 3, G.obj ⟨Multiplicative.ofAdd a⟩ = S (a, -a)) ∧
      (letI := h; letI := E.inverseMonoidal; E.IsMonoidal) ∧
      E.functor ⋙ (toBimod A).essImage.ι =
        (LminusClosure S).lift (GrMat.real G) hmem ⋙ freeLminus A S ⋙ toBimod A ∧
      Nonempty ((LminusClosure S).lift (GrMat.real G) hmem).Braided := by
  have := lminusClosure_isMonoidal hfusion hunitS
  obtain ⟨e, he, -, hfun⟩ :=
    freeLminus_monoidalEquivalence_of_separable A 𝕜 hSchur hfusion hunitS hA hS h3 hss
  obtain ⟨G, hmem, hobj, ⟨hbr⟩, hEq⟩ :=
    Lminus_vec_braided_equivalence 𝕜 S hSchur hfusion hunitS hθ
  let F := (LminusClosure S).lift (GrMat.real G) hmem
  let e₁ : GrMat (Multiplicative (ZMod 3)) 𝕜 ≌ (LminusClosure S).FullSubcategory :=
    F.asEquivalence
  let h₁ : e₁.functor.Monoidal := hbr.toMonoidal
  let h : (e₁.trans e).functor.Monoidal := inferInstanceAs (e₁.functor ⋙ e.functor).Monoidal
  refine ⟨G, hmem, e₁.trans e, h, hobj, ?_, ?_, ⟨hbr⟩⟩
  · exact equivalence_isMonoidal_inverseMonoidal (e₁.trans e) h
  · show e₁.functor ⋙ (e.functor ⋙ (toBimod A).essImage.ι) = _
    rw [hfun]
    rfl

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.equivalence_isMonoidal_inverseMonoidal
#print axioms HaagerupIzumi.C8.untwisted_vec_equivalence_of_separable
