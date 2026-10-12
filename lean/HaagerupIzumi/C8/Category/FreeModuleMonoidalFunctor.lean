module

public import HaagerupIzumi.C8.Category.FreeModuleMonoidal
public import Mathlib.CategoryTheory.Bicategory.End

@[expose] public section

/-! # Free induction is a monoidal functor `C ⥤ (Bimod A A, ⊗_A)`

"Free `H/B`-module induction is tensor" (manuscript `haagerup_c8_expanded.tex`, lines
3337–3338), assembled.  For a commutative algebra `A` in a braided monoidal category `C`:

* `bimodMonoidal A : MonoidalCategory (Bimod A A)`: `A`-bimodules with the relative tensor
  product `⊗_A`, i.e. the endomorphisms of `A` in Mathlib's bicategory of algebras and
  bimodules (`EndMonoidal A` for `Bimod.monBicategory`).  A definition, not an instance
  (`Mon C` already carries the category structure of monoid morphisms).
* `freeCoreMonoidal A : (freeFunctor A ⋙ toBimod A).CoreMonoidal`: free induction
  `X ↦ X ⊗ A` is a (strong) monoidal functor, with tensorator `freeTensorIso` and unit
  `(freeUnitIso A)⁻¹`; the axioms are `freeTensorIso_natural_left/right`,
  `freeTensorIso_associativity`, `freeTensorIso_leftUnitality/rightUnitality`.
  `freeMonoidal A` is the resulting `Functor.Monoidal` structure.

Hypotheses: those of `Category/FreeModuleTensor.lean`.  No external-theorem or certificate
inputs.  The essential image and full faithfulness of induction from the additive closure of
`L₋` are treated without the monoidal structure in `Category/FreeModuleEssSurj.lean`,
`Category/FreeModuleEquivalence.lean` (`freeLminus_isEquivalence`, an equivalence of plain
categories) and `Category/SimpleModulesLminus.lean`.  Not formalized here: a monoidal
structure on `RightMod A` or on the additive closure of `L₋`, hence the monoidal (tensor)
equivalence (which would also need `S (0, 0) ≅ 𝟙_ C`), and the identification of the pointed
subcategory on `L₋` with `Vec_{ℤ/3}` (Tannakian argument). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- `(Bimod A A, ⊗_A)`: the monoidal category of `A`-bimodules under the relative tensor
product (endomorphisms of `A` in `Bimod.monBicategory`). -/
@[instance_reducible]
noncomputable def bimodMonoidal (A : Mon C) : MonoidalCategory (Bimod A A) :=
  letI : Bicategory (Mon C) := Bimod.monBicategory
  inferInstanceAs (MonoidalCategory (EndMonoidal A))

variable [BraidedCategory C] (A : Mon C) [IsCommMonObj A.X]

/-- **Free induction is a monoidal functor** `C ⥤ (Bimod A A, ⊗_A)` (manuscript
lines 3337–3338). -/
noncomputable def freeCoreMonoidal :
    letI := bimodMonoidal A
    (freeFunctor A ⋙ toBimod A).CoreMonoidal :=
  letI := bimodMonoidal A
  { εIso := (freeUnitIso A).symm
    μIso := fun X Y => freeTensorIso A X Y
    μIso_hom_natural_left := fun {X _} f X' => freeTensorIso_natural_left A X X' f
    μIso_hom_natural_right := fun {X _} X' f => freeTensorIso_natural_right A X' X f
    associativity := fun X Y Z => freeTensorIso_associativity A X Y Z
    left_unitality := fun X => freeTensorIso_leftUnitality A X
    right_unitality := fun X => freeTensorIso_rightUnitality A X }

/-- Free induction as a `Functor.Monoidal` structure for `(Bimod A A, ⊗_A)`. -/
@[instance_reducible]
noncomputable def freeMonoidal :
    letI := bimodMonoidal A
    (freeFunctor A ⋙ toBimod A).Monoidal :=
  letI := bimodMonoidal A
  (freeCoreMonoidal A).toMonoidal

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.bimodMonoidal
#print axioms HaagerupIzumi.C8.RightMod.freeCoreMonoidal
#print axioms HaagerupIzumi.C8.RightMod.freeMonoidal
