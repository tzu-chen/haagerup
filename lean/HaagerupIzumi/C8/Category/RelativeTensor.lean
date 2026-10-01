module

public import HaagerupIzumi.C8.Category.BraidedModules

@[expose] public section

/-! # The relation `l = r ∘ c_{A,X}` is closed under relative tensor products

Continuation of `HaagerupIzumi.C8.Category.BraidedModules`, for the second paragraph of
the proof of Lemma `lem:analytic-unitary-all-modules` (manuscript
`haagerup_c8_expanded.tex`, lines 4900–4934): "The relative tensor product is obtained by
splitting the separability idempotent on `M ⊗ N`.  Its induced left and right actions again
satisfy this relation, by the same hexagon identity and the balancing relation. ... its unit
is `A`."

We use Mathlib's relative tensor product of bimodules `Bimod.tensorBimod`, the coequalizer
of `r_M ▷ N` and `α ≫ M ◁ l_N`.  This needs coequalizers in `C` and tensoring on either
side preserving them; these are explicit typeclass hypotheses.  In the manuscript's
semisimple setting the coequalizer is the image of the separability idempotent, a split
coequalizer; that identification is not formalized here.

* `tensorBimod_relation`: if `M` and `N` satisfy `actLeft = c_{A,X} ≫ actRight`, so does
  `M ⊗_A N` (hexagon identity and the balancing relation `coequalizer.condition`).
* `tensorBimod_mem_essImage`: the relative tensor product of two right modules lies in the
  essential image of `toBimod`.
* `tensorBimod_mem_essImage_of_mem`: the essential image of `toBimod` (the full subcategory
  of bimodules with `actLeft = c_{A,X} ≫ actRight`) is closed under `⊗_A`.
* `regular_relation`, `regular_mem_essImage`: the unit bimodule `A` satisfies the relation
  (commutativity of `A`), so it lies in that subcategory.

No external-theorem or certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The unit bimodule `A` satisfies `actLeft = c_{A,A} ≫ actRight`; this is the
commutativity of `A`. -/
theorem regular_relation (A : Mon C) [IsCommMonObj A.X] :
    (Bimod.regular A).actLeft =
      (β_ A.X (Bimod.regular A).X).hom ≫ (Bimod.regular A).actRight :=
  (IsCommMonObj.mul_comm A.X).symm

/-- The unit bimodule `A` lies in the essential image of `toBimod`. -/
theorem regular_mem_essImage (A : Mon C) [IsCommMonObj A.X] :
    (toBimod A).essImage (Bimod.regular A) :=
  (mem_essImage_toBimod_iff A _).2 (regular_relation A)

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The relation `actLeft = c_{A,X} ≫ actRight` passes to the relative tensor product
`M ⊗_A N` (hexagon identity and balancing relation). -/
theorem tensorBimod_relation (A : Mon C) {M N : Bimod A A}
    (hM : M.actLeft = (β_ A.X M.X).hom ≫ M.actRight)
    (hN : N.actLeft = (β_ A.X N.X).hom ≫ N.actRight) :
    (M.tensorBimod N).actLeft =
      (β_ A.X (M.tensorBimod N).X).hom ≫ (M.tensorBimod N).actRight := by
  refine (cancel_epi ((tensorLeft A.X).map (coequalizer.π _ _))).1 ?_
  dsimp [Bimod.TensorBimod.X]
  rw [Bimod.TensorBimod.whiskerLeft_π_actLeft M N,
    BraidedCategory.braiding_naturality_right_assoc, Bimod.TensorBimod.π_tensor_id_actRight M N,
    hM, BraidedCategory.braiding_tensor_right_hom]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
  rw [coequalizer.condition, ← MonoidalCategory.whiskerLeft_comp_assoc, ← hN]
  simp only [Category.assoc]

/-- The relative tensor product of two right modules (viewed as bimodules through the
braiding) is again in the essential image of `toBimod`. -/
theorem tensorBimod_mem_essImage (A : Mon C) [IsCommMonObj A.X] (M N : RightMod A) :
    (toBimod A).essImage (((toBimod A).obj M).tensorBimod ((toBimod A).obj N)) :=
  (mem_essImage_toBimod_iff A _).2
    (tensorBimod_relation A (toBimod_obj_actLeft A M) (toBimod_obj_actLeft A N))

/-- The full subcategory of `A`-bimodules satisfying `actLeft = c_{A,X} ≫ actRight` (the
essential image of `toBimod`) is closed under the relative tensor product. -/
theorem tensorBimod_mem_essImage_of_mem (A : Mon C) [IsCommMonObj A.X] {B B' : Bimod A A}
    (hB : (toBimod A).essImage B) (hB' : (toBimod A).essImage B') :
    (toBimod A).essImage (B.tensorBimod B') :=
  (mem_essImage_toBimod_iff A _).2
    (tensorBimod_relation A ((mem_essImage_toBimod_iff A B).1 hB)
      ((mem_essImage_toBimod_iff A B').1 hB'))

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.regular_relation
#print axioms HaagerupIzumi.C8.tensorBimod_relation
#print axioms HaagerupIzumi.C8.tensorBimod_mem_essImage
#print axioms HaagerupIzumi.C8.tensorBimod_mem_essImage_of_mem
#print axioms HaagerupIzumi.C8.regular_mem_essImage
