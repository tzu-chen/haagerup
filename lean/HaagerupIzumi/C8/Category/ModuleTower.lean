module

public import HaagerupIzumi.C8.Category.FreeModuleMonoidalFunctor

@[expose] public section

/-! # The module tower: `H`-modules over `B`-bimodules are `(H, B)`-bimodules

Generic core of the forgetful embedding of manuscript `haagerup_c8_expanded.tex`, lines
3349–3352 ("Viewing these modules in `Rep(U)` forgets only the locality condition for the
intermediate algebra `B`; it preserves `H`-module morphisms and relative tensor products").  Let
`f : B ⟶ H` be a morphism of monoid objects (`IsMonHom f`) in a monoidal category `C` with
coequalizers preserved by `X ⊗ -` and `- ⊗ X` (Mathlib's relative tensor product
`Bimod.tensorBimod`).  No braiding or commutativity is needed.

**(1) `H` is a monoid in `(Bimod B B, ⊗_B)`.**
* `resBimod f : Bimod B B`: `H` with `b · h · b' = f(b) h f(b')`.
* `mulBimod f : H ⊗_B H ⟶ H` (the multiplication descends, `π_mulX`) and
  `unitBimod f : B ⟶ H` (`f` itself) are bimodule maps.
* `one_mul_core`, `mul_one_core`, `mul_assoc_core`: the monoid axioms with Mathlib's bimodule
  unitors and associator.  `monObj f`: the resulting `MonObj` in `(Bimod B B, ⊗_B)`
  (`RightMod.bimodMonoidal B`).

**(2) Modules.**  `TowerMod f`: left modules over this monoid, unfolded (a `B`-bimodule `N` with
a bimodule map `smul : H ⊗_B N ⟶ N` and the unit/associativity axioms), with their morphisms.
* `TowerMod.act`, `restrict_act`: the underlying action `H ⊗ N ⟶ N`, whose restriction along
  `f` is the given left `B`-action.
* `TowerMod.forget : TowerMod f ⥤ Bimod H B`: the `(H, B)`-bimodule in `C` (left action `act`,
  right action the `B`-action), on morphisms the identity of the underlying maps.
* `forget_faithful`, `forget_full`, and `forget_isEquivalence`: **`forget` is an equivalence of
  categories**.  The inverse construction `ofBimodHB` restricts the left action to `B`
  (`restrictBimod`) and descends it to `H ⊗_B M` (`smulOf`).

**(3) Relative tensor products.**
* `restrictRight`, `restrictLeft`: restriction of one side of a bimodule along `f`.
* `tensorComparison f M N : M_B ⊗_B N_B ⟶ M ⊗_H N`, with `π_tensorComparison` and
  `tensorComparison_epi`: the relative tensor product over `H` is a quotient of the one over
  `B`.
* `Category/ModuleTowerTensor.lean` shows that it is exactly the coequalizer of the tower pair
  `(M_B ⊗_B H) ⊗_B N_B ⇉ M_B ⊗_B N_B`, i.e. the relative tensor product over the monoid `H` of
  `(Bimod B B, ⊗_B)` computed in `C`.

In the application `C = Rep(U)`, `B` is the intermediate algebra and `H` the extension.  The
modules there are *right* modules (manuscript line 3244).  So the application needs the mirror
construction: right modules over `H` in `(Bimod B B, ⊗_B)` versus `(B, H)`-bimodules in `C`.  It
is the same argument with the sides exchanged and is not formalized here.  For commutative `B` in
braided `C`, right `B`-modules are `B`-bimodules through the braiding (`RightMod.toBimod`,
`Category/BraidedModules.lean`), and `H/B`-modules in `Rep(B)` are the tower modules whose
underlying `B`-module is local.

Not formalized:
* the mirror construction and that specialization;
* the comparison of `(Bimod B B, ⊗_B)` with `Rep(B)` (local modules);
* the packaging of `forget` as a monoidal functor.

The tensorator data in coequalizer form, with naturality, unit and associativity coherence, is
in `Category/ModuleTowerMonoidal.lean`.

No external-theorem or certificate inputs. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ModuleTower

section Res

variable {B H : Mon C} (f : B.X ⟶ H.X) [IsMonHom f]

/-- `H` as a `B`-bimodule through `f`. -/
@[simps]
def resBimod : Bimod B B where
  X := H.X
  actLeft := f ▷ H.X ≫ μ[H.X]
  one_actLeft := by
    rw [← comp_whiskerRight_assoc, IsMonHom.one_hom, MonObj.one_mul]
  left_assoc := by
    rw [← comp_whiskerRight_assoc, IsMonHom.mul_hom, comp_whiskerRight_assoc,
      MonObj.mul_assoc, tensorHom_def', comp_whiskerRight_assoc,
      associator_naturality_left_assoc, associator_naturality_middle_assoc,
      whiskerLeft_comp_assoc]
    conv_rhs => rw [whisker_exchange_assoc]
  actRight := H.X ◁ f ≫ μ[H.X]
  actRight_one := by
    rw [← whiskerLeft_comp_assoc, IsMonHom.one_hom, MonObj.mul_one]
  right_assoc := by
    rw [← whiskerLeft_comp_assoc, IsMonHom.mul_hom, whiskerLeft_comp_assoc,
      MonObj.mul_assoc_flip, MonoidalCategory.tensorHom_def, whiskerLeft_comp_assoc,
      associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc]
    conv_rhs => rw [comp_whiskerRight_assoc, ← whisker_exchange_assoc]
  middle_assoc := by
    rw [comp_whiskerRight_assoc, ← whisker_exchange_assoc, MonObj.mul_assoc,
      associator_naturality_right_assoc, associator_naturality_left_assoc,
      whiskerLeft_comp_assoc, whisker_exchange_assoc, whisker_exchange_assoc]

end Res


section Pi

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(φ ⊗_S Q)(m ⊗ q) = φ(m) ⊗ q`. -/
@[reassoc]
theorem π_whiskerRight_hom {R S T : Mon C} {M₁ M₂ : Bimod R S} (φ : M₁ ⟶ M₂) (Q : Bimod S T) :
    coequalizer.π (M₁.actRight ▷ Q.X) ((α_ M₁.X S.X Q.X).hom ≫ M₁.X ◁ Q.actLeft) ≫
        (Bimod.whiskerRight φ Q).hom =
      φ.hom ▷ Q.X ≫
        coequalizer.π (M₂.actRight ▷ Q.X) ((α_ M₂.X S.X Q.X).hom ≫ M₂.X ◁ Q.actLeft) := by
  rw [Bimod.whiskerRight_hom]
  try dsimp only [Bimod.tensorBimod_X, Bimod.TensorBimod.X]
  rw [ι_colimMap, parallelPairHom_app_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(M ⊗_S φ)(m ⊗ q) = m ⊗ φ(q)`. -/
@[reassoc]
theorem π_whiskerLeft_hom {R S T : Mon C} (M : Bimod R S) {Q₁ Q₂ : Bimod S T} (φ : Q₁ ⟶ Q₂) :
    coequalizer.π (M.actRight ▷ Q₁.X) ((α_ M.X S.X Q₁.X).hom ≫ M.X ◁ Q₁.actLeft) ≫
        (Bimod.whiskerLeft M φ).hom =
      M.X ◁ φ.hom ≫
        coequalizer.π (M.actRight ▷ Q₂.X) ((α_ M.X S.X Q₂.X).hom ≫ M.X ◁ Q₂.actLeft) := by
  rw [Bimod.whiskerLeft_hom]
  try dsimp only [Bimod.tensorBimod_X, Bimod.TensorBimod.X]
  rw [ι_colimMap, parallelPairHom_app_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator of `⊗` on generators, first step. -/
@[reassoc]
theorem π_associatorBimod_hom {R S T U : Mon C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U) :
    coequalizer.π ((P.tensorBimod Q).actRight ▷ L.X)
        ((α_ (P.tensorBimod Q).X T.X L.X).hom ≫ (P.tensorBimod Q).X ◁ L.actLeft) ≫
        (Bimod.associatorBimod P Q L).hom.hom = Bimod.AssociatorBimod.homAux P Q L :=
  coequalizer.π_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator on generators: `((p ⊗ q) ⊗ l) ↦ p ⊗ (q ⊗ l)`. -/
@[reassoc]
theorem π_whiskerRight_homAux {R S T U : Mon C} (P : Bimod R S) (Q : Bimod S T)
    (L : Bimod T U) :
    (coequalizer.π (P.actRight ▷ Q.X) ((α_ P.X S.X Q.X).hom ≫ P.X ◁ Q.actLeft) ▷ L.X) ≫
        Bimod.AssociatorBimod.homAux P Q L =
      (α_ P.X Q.X L.X).hom ≫
        P.X ◁ coequalizer.π (Q.actRight ▷ L.X) ((α_ Q.X T.X L.X).hom ≫ Q.X ◁ L.actLeft) ≫
          coequalizer.π (P.actRight ▷ (Q.tensorBimod L).X)
            ((α_ P.X S.X (Q.tensorBimod L).X).hom ≫ P.X ◁ (Q.tensorBimod L).actLeft) :=
  π_tensor_id_preserves_coequalizer_inv_desc _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The left unitor on generators: `r ⊗ p ↦ r · p`. -/
@[reassoc]
theorem π_leftUnitorBimod_hom {R S : Mon C} (P : Bimod R S) :
    coequalizer.π ((Bimod.regular R).actRight ▷ P.X)
        ((α_ (Bimod.regular R).X R.X P.X).hom ≫ (Bimod.regular R).X ◁ P.actLeft) ≫
        (Bimod.leftUnitorBimod P).hom.hom = P.actLeft :=
  coequalizer.π_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right unitor on generators: `p ⊗ s ↦ p · s`. -/
@[reassoc]
theorem π_rightUnitorBimod_hom {R S : Mon C} (P : Bimod R S) :
    coequalizer.π (P.actRight ▷ (Bimod.regular S).X)
        ((α_ P.X S.X (Bimod.regular S).X).hom ≫ P.X ◁ (Bimod.regular S).actLeft) ≫
        (Bimod.rightUnitorBimod P).hom.hom = P.actRight :=
  coequalizer.π_desc _ _

end Pi

section Monoid

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {B H : Mon C} (f : B.X ⟶ H.X) [IsMonHom f]

/-- The multiplication of `H` descends to `H ⊗_B H`. -/
noncomputable def mulX : ((resBimod f).tensorBimod (resBimod f)).X ⟶ H.X :=
  coequalizer.desc μ[H.X] (by
    show (H.X ◁ f ≫ μ[H.X]) ▷ H.X ≫ μ[H.X] =
      ((α_ H.X B.X H.X).hom ≫ H.X ◁ (f ▷ H.X ≫ μ[H.X])) ≫ μ[H.X]
    rw [comp_whiskerRight_assoc, MonObj.mul_assoc, associator_naturality_middle_assoc,
      Category.assoc, whiskerLeft_comp_assoc])

@[reassoc]
theorem π_mulX :
    coequalizer.π ((resBimod f).actRight ▷ (resBimod f).X)
        ((α_ (resBimod f).X B.X (resBimod f).X).hom ≫ (resBimod f).X ◁ (resBimod f).actLeft) ≫
        mulX f = μ[H.X] :=
  coequalizer.π_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The multiplication `H ⊗_B H ⟶ H`** as a map of `B`-bimodules. -/
noncomputable def mulBimod : (resBimod f).tensorBimod (resBimod f) ⟶ resBimod f where
  hom := mulX f
  left_act_hom := by
    refine (cancel_epi ((tensorLeft B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [curriedTensor_obj_map, Bimod.tensorBimod_actLeft]
    rw [reassoc_of% Bimod.TensorBimod.whiskerLeft_π_actLeft, π_mulX, ← whiskerLeft_comp_assoc,
      π_mulX]
    show (α_ B.X H.X H.X).inv ≫ (f ▷ H.X ≫ μ[H.X]) ▷ H.X ≫ μ[H.X] =
      B.X ◁ μ[H.X] ≫ f ▷ H.X ≫ μ[H.X]
    rw [comp_whiskerRight_assoc, MonObj.mul_assoc, associator_naturality_left_assoc,
      Iso.inv_hom_id_assoc, whisker_exchange_assoc]
  right_act_hom := by
    refine (cancel_epi ((tensorRight B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.tensorBimod_actRight]
    rw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight, π_mulX, ← comp_whiskerRight_assoc,
      π_mulX]
    show (α_ H.X H.X B.X).hom ≫ H.X ◁ (H.X ◁ f ≫ μ[H.X]) ≫ μ[H.X] =
      μ[H.X] ▷ B.X ≫ H.X ◁ f ≫ μ[H.X]
    rw [whiskerLeft_comp_assoc]
    conv_rhs => rw [← whisker_exchange_assoc, MonObj.mul_assoc, associator_naturality_right_assoc]

theorem mulBimod_hom : (mulBimod f).hom = mulX f := rfl

/-- **The unit `B ⟶ H`** (that is, `f`) as a map of `B`-bimodules. -/
def unitBimod : Bimod.regular B ⟶ resBimod f where
  hom := f
  left_act_hom := by
    show μ[B.X] ≫ f = B.X ◁ f ≫ f ▷ H.X ≫ μ[H.X]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc]
  right_act_hom := by
    show μ[B.X] ≫ f = f ▷ B.X ≫ H.X ◁ f ≫ μ[H.X]
    rw [IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc]

theorem unitBimod_hom : (unitBimod f).hom = f := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left unit axiom of `H` in `(Bimod B B, ⊗_B)`. -/
theorem one_mul_core :
    Bimod.whiskerRight (unitBimod f) (resBimod f) ≫ mulBimod f =
      (Bimod.leftUnitorBimod (resBimod f)).hom := by
  apply Bimod.hom_ext
  apply coequalizer.hom_ext
  rw [Bimod.comp_hom', π_whiskerRight_hom_assoc, π_leftUnitorBimod_hom, mulBimod_hom, π_mulX,
    unitBimod_hom]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right unit axiom of `H` in `(Bimod B B, ⊗_B)`. -/
theorem mul_one_core :
    Bimod.whiskerLeft (resBimod f) (unitBimod f) ≫ mulBimod f =
      (Bimod.rightUnitorBimod (resBimod f)).hom := by
  apply Bimod.hom_ext
  apply coequalizer.hom_ext
  rw [Bimod.comp_hom', π_whiskerLeft_hom_assoc, π_rightUnitorBimod_hom, mulBimod_hom, π_mulX,
    unitBimod_hom]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Associativity of `H` in `(Bimod B B, ⊗_B)`. -/
theorem mul_assoc_core :
    Bimod.whiskerRight (mulBimod f) (resBimod f) ≫ mulBimod f =
      (Bimod.associatorBimod (resBimod f) (resBimod f) (resBimod f)).hom ≫
        Bimod.whiskerLeft (resBimod f) (mulBimod f) ≫ mulBimod f := by
  apply Bimod.hom_ext
  apply coequalizer.hom_ext
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.comp_hom']
  rw [π_whiskerRight_hom_assoc, ← MonoidalCategory.comp_whiskerRight_assoc, mulBimod_hom,
    π_mulX, π_associatorBimod_hom_assoc, π_whiskerRight_homAux_assoc,
    π_whiskerLeft_hom_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, mulBimod_hom, π_mulX]
  exact MonObj.mul_assoc H.X

/-- **`H` is a monoid object of `(Bimod B B, ⊗_B)`.** -/
@[instance_reducible]
noncomputable def monObj :
    letI := RightMod.bimodMonoidal B
    MonObj (resBimod f) :=
  letI := RightMod.bimodMonoidal B
  { one := unitBimod f
    mul := mulBimod f
    one_mul := one_mul_core f
    mul_one := mul_one_core f
    mul_assoc := mul_assoc_core f }

end Monoid

section Tower

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {B H : Mon C} (f : B.X ⟶ H.X) [IsMonHom f]

/-- **Left modules over the monoid `H` of `(Bimod B B, ⊗_B)`** (`monObj f`), unfolded: a
`B`-bimodule `N` with a bimodule map `smul : H ⊗_B N ⟶ N` satisfying the unit and
associativity axioms of a left module object (Mathlib's `ModObj` axioms for `monObj f`, written
with the bimodule whiskerings, unitor and associator). -/
structure TowerMod where
  /-- The underlying `B`-bimodule. -/
  N : Bimod B B
  /-- The action `H ⊗_B N ⟶ N`. -/
  smul : (resBimod f).tensorBimod N ⟶ N
  one_smul : Bimod.whiskerRight (unitBimod f) N ≫ smul = (Bimod.leftUnitorBimod N).hom
  mul_smul : Bimod.whiskerRight (mulBimod f) N ≫ smul =
    (Bimod.associatorBimod (resBimod f) (resBimod f) N).hom ≫
      Bimod.whiskerLeft (resBimod f) smul ≫ smul

namespace TowerMod

variable {f}

/-- Morphisms of tower modules: bimodule maps commuting with the actions. -/
@[ext]
structure Hom (M M' : TowerMod f) where
  /-- The underlying bimodule map. -/
  hom : M.N ⟶ M'.N
  smul_hom : M.smul ≫ hom = Bimod.whiskerLeft (resBimod f) hom ≫ M'.smul

instance : Category (TowerMod f) where
  Hom := Hom
  id M := ⟨𝟙 _, by rw [Category.comp_id, Bimod.whiskerLeft_id_bimod, Category.id_comp]⟩
  comp g g' := ⟨g.hom ≫ g'.hom, by
    rw [← Category.assoc, g.smul_hom, Category.assoc, g'.smul_hom, ← Category.assoc,
      ← Bimod.whiskerLeft_comp_bimod]⟩

theorem hom_ext' {M M' : TowerMod f} {g g' : M ⟶ M'} (h : Hom.hom g = Hom.hom g') : g = g' :=
  Hom.ext h

/-- The left `H`-action `H ⊗ N ⟶ N` underlying a tower module: `h ⊗ n ↦ smul(π(h ⊗ n))`. -/
noncomputable def act (M : TowerMod f) : H.X ⊗ M.N.X ⟶ M.N.X :=
  coequalizer.π ((resBimod f).actRight ▷ M.N.X)
      ((α_ (resBimod f).X B.X M.N.X).hom ≫ (resBimod f).X ◁ M.N.actLeft) ≫ M.smul.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `B`-action of a tower module is the restriction of its `H`-action. -/
theorem restrict_act (M : TowerMod f) : f ▷ M.N.X ≫ act M = M.N.actLeft := by
  have h := congrArg (fun φ => coequalizer.π ((Bimod.regular B).actRight ▷ M.N.X)
      ((α_ (Bimod.regular B).X B.X M.N.X).hom ≫ (Bimod.regular B).X ◁ M.N.actLeft) ≫
        Bimod.Hom.hom φ) M.one_smul
  simp only [Bimod.comp_hom'] at h
  rw [π_whiskerRight_hom_assoc, π_leftUnitorBimod_hom, unitBimod_hom] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the `H`-action. -/
theorem act_assoc (M : TowerMod f) :
    μ[H.X] ▷ M.N.X ≫ act M = (α_ H.X H.X M.N.X).hom ≫ H.X ◁ act M ≫ act M := by
  have h := congrArg (fun φ => (coequalizer.π ((resBimod f).actRight ▷ (resBimod f).X)
      ((α_ (resBimod f).X B.X (resBimod f).X).hom ≫ (resBimod f).X ◁ (resBimod f).actLeft) ▷
        M.N.X) ≫ coequalizer.π (((resBimod f).tensorBimod (resBimod f)).actRight ▷ M.N.X)
      ((α_ ((resBimod f).tensorBimod (resBimod f)).X B.X M.N.X).hom ≫
        ((resBimod f).tensorBimod (resBimod f)).X ◁ M.N.actLeft) ≫ Bimod.Hom.hom φ) M.mul_smul
  simp only [Bimod.comp_hom'] at h
  rw [π_whiskerRight_hom_assoc, ← MonoidalCategory.comp_whiskerRight_assoc, mulBimod_hom,
    π_mulX, π_associatorBimod_hom_assoc, π_whiskerRight_homAux_assoc,
    π_whiskerLeft_hom_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `H`-action commutes with the right `B`-action. -/
theorem act_middle (M : TowerMod f) :
    act M ▷ B.X ≫ M.N.actRight = (α_ H.X M.N.X B.X).hom ≫ H.X ◁ M.N.actRight ≫ act M := by
  have h := M.smul.right_act_hom
  rw [Bimod.tensorBimod_actRight] at h
  rw [act, comp_whiskerRight_assoc, ← h,
    reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight]
  rfl

/-- The `(H, B)`-bimodule underlying a tower module. -/
noncomputable def toBimodHB (M : TowerMod f) : Bimod H B where
  X := M.N.X
  actLeft := act M
  one_actLeft := by
    rw [← IsMonHom.one_hom f, comp_whiskerRight_assoc, restrict_act, M.N.one_actLeft]
  left_assoc := act_assoc M
  actRight := M.N.actRight
  actRight_one := M.N.actRight_one
  right_assoc := M.N.right_assoc
  middle_assoc := act_middle M

theorem toBimodHB_actLeft (M : TowerMod f) : (toBimodHB M).actLeft = act M := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The forgetful functor of the tower**: a left module over `H` in `(Bimod B B, ⊗_B)` is an
`(H, B)`-bimodule in `C`, with the same morphisms. -/
noncomputable def forget : TowerMod f ⥤ Bimod H B where
  obj := toBimodHB
  map {M M'} g :=
    { hom := (Hom.hom g).hom
      left_act_hom := by
        have h := congrArg Bimod.Hom.hom (Hom.smul_hom g)
        simp only [Bimod.comp_hom'] at h
        show (coequalizer.π _ _ ≫ M.smul.hom) ≫ (Hom.hom g).hom =
          H.X ◁ (Hom.hom g).hom ≫ coequalizer.π _ _ ≫ M'.smul.hom
        rw [Category.assoc, h, π_whiskerLeft_hom_assoc]
        rfl
      right_act_hom := (Hom.hom g).right_act_hom }
  map_id M := by
    apply Bimod.hom_ext
    rfl
  map_comp g g' := by
    apply Bimod.hom_ext
    rfl

/-- `forget` is faithful. -/
theorem forget_faithful : (forget (f := f)).Faithful where
  map_injective {M M'} g g' h := by
    have h' := congrArg Bimod.Hom.hom h
    exact hom_ext' (Bimod.hom_ext _ _ h')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `forget` is full: an `(H, B)`-bimodule map between tower modules is a map of tower
modules (it commutes with the left `B`-actions, which are restrictions of the `H`-actions,
and with `smul`, since `H ⊗ N ⟶ H ⊗_B N` is epi). -/
theorem forget_full : (forget (f := f)).Full where
  map_surjective {M M'} φ := by
    have hφ : act M ≫ φ.hom = H.X ◁ φ.hom ≫ act M' := φ.left_act_hom
    let ψ : M.N ⟶ M'.N :=
      { hom := φ.hom
        left_act_hom := by
          rw [← restrict_act M, ← restrict_act M', Category.assoc, hφ, whisker_exchange_assoc]
        right_act_hom := φ.right_act_hom }
    refine ⟨⟨ψ, ?_⟩, ?_⟩
    · apply Bimod.hom_ext
      apply coequalizer.hom_ext
      rw [Bimod.comp_hom', Bimod.comp_hom', π_whiskerLeft_hom_assoc]
      exact (Category.assoc _ _ _).symm.trans (hφ.trans rfl)
    · apply Bimod.hom_ext
      rfl

section EssSurj

/-- The `B`-bimodule underlying an `(H, B)`-bimodule: the left action restricted along `f`
(the case `T = B` of `restrictLeft`). -/
def restrictBimod (M : Bimod H B) : Bimod B B where
  X := M.X
  actLeft := f ▷ M.X ≫ M.actLeft
  one_actLeft := by
    rw [← comp_whiskerRight_assoc, IsMonHom.one_hom, M.one_actLeft]
  left_assoc := by
    rw [← comp_whiskerRight_assoc, IsMonHom.mul_hom, comp_whiskerRight_assoc,
      M.left_assoc, tensorHom_def', comp_whiskerRight_assoc,
      associator_naturality_left_assoc, associator_naturality_middle_assoc,
      whiskerLeft_comp_assoc]
    conv_rhs => rw [whisker_exchange_assoc]
  actRight := M.actRight
  actRight_one := M.actRight_one
  right_assoc := M.right_assoc
  middle_assoc := by
    rw [comp_whiskerRight_assoc, M.middle_assoc, associator_naturality_left_assoc,
      whisker_exchange_assoc]

/-- The left `H`-action of an `(H, B)`-bimodule descends to `H ⊗_B M`. -/
noncomputable def descAct (M : Bimod H B) :
    ((resBimod f).tensorBimod (restrictBimod (f := f) M)).X ⟶ M.X :=
  coequalizer.desc M.actLeft (by
    show (H.X ◁ f ≫ μ[H.X]) ▷ M.X ≫ M.actLeft =
      ((α_ H.X B.X M.X).hom ≫ H.X ◁ (f ▷ M.X ≫ M.actLeft)) ≫ M.actLeft
    rw [comp_whiskerRight_assoc, M.left_assoc, associator_naturality_middle_assoc,
      Category.assoc, whiskerLeft_comp_assoc])

@[reassoc]
theorem π_descAct (M : Bimod H B) :
    coequalizer.π ((resBimod f).actRight ▷ (restrictBimod (f := f) M).X)
        ((α_ (resBimod f).X B.X (restrictBimod (f := f) M).X).hom ≫
          (resBimod f).X ◁ (restrictBimod (f := f) M).actLeft) ≫ descAct M = M.actLeft :=
  coequalizer.π_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The descended action as a map of `B`-bimodules. -/
noncomputable def smulOf (M : Bimod H B) :
    (resBimod f).tensorBimod (restrictBimod (f := f) M) ⟶ restrictBimod (f := f) M where
  hom := descAct M
  left_act_hom := by
    refine (cancel_epi ((tensorLeft B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [curriedTensor_obj_map, Bimod.tensorBimod_actLeft]
    rw [reassoc_of% Bimod.TensorBimod.whiskerLeft_π_actLeft, π_descAct,
      ← whiskerLeft_comp_assoc, π_descAct]
    show (α_ B.X H.X M.X).inv ≫ (f ▷ H.X ≫ μ[H.X]) ▷ M.X ≫ M.actLeft =
      B.X ◁ M.actLeft ≫ f ▷ M.X ≫ M.actLeft
    rw [comp_whiskerRight_assoc, M.left_assoc, associator_naturality_left_assoc,
      Iso.inv_hom_id_assoc, whisker_exchange_assoc]
  right_act_hom := by
    refine (cancel_epi ((tensorRight B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.tensorBimod_actRight]
    rw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight, π_descAct,
      ← comp_whiskerRight_assoc, π_descAct]
    exact M.middle_assoc.symm

theorem smulOf_hom (M : Bimod H B) : (smulOf (f := f) M).hom = descAct M := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An `(H, B)`-bimodule as a tower module. -/
noncomputable def ofBimodHB (M : Bimod H B) : TowerMod f where
  N := restrictBimod M
  smul := smulOf M
  one_smul := by
    apply Bimod.hom_ext
    apply coequalizer.hom_ext
    rw [Bimod.comp_hom', π_whiskerRight_hom_assoc, π_leftUnitorBimod_hom, smulOf_hom,
      π_descAct, unitBimod_hom]
    rfl
  mul_smul := by
    apply Bimod.hom_ext
    apply coequalizer.hom_ext
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    simp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.comp_hom']
    rw [π_whiskerRight_hom_assoc, ← MonoidalCategory.comp_whiskerRight_assoc, mulBimod_hom,
      π_mulX, smulOf_hom, π_descAct, π_associatorBimod_hom_assoc, π_whiskerRight_homAux_assoc,
      π_whiskerLeft_hom_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, smulOf_hom,
      π_descAct]
    exact M.left_assoc

/-- `forget (ofBimodHB M) ≅ M` (the identity of the underlying object). -/
noncomputable def forgetOfBimodHBIso (M : Bimod H B) : forget.obj (ofBimodHB (f := f) M) ≅ M :=
  Bimod.isoOfIso (Iso.refl M.X)
    (by
      show (coequalizer.π _ _ ≫ descAct M) ≫ 𝟙 M.X = H.X ◁ 𝟙 M.X ≫ M.actLeft
      rw [π_descAct]
      exact (Category.comp_id _).trans
        (by rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]))
    (by
      show M.actRight ≫ 𝟙 M.X = 𝟙 M.X ▷ B.X ≫ M.actRight
      exact (Category.comp_id _).trans
        (by rw [MonoidalCategory.id_whiskerRight, Category.id_comp]))

/-- **The module tower**: left modules over the monoid `H` of `(Bimod B B, ⊗_B)` are the same
as `(H, B)`-bimodules in `C`; the forgetful functor is an equivalence of categories. -/
theorem forget_isEquivalence : (forget (f := f)).IsEquivalence :=
  { faithful := forget_faithful
    full := forget_full
    essSurj := ⟨fun M => ⟨ofBimodHB M, ⟨forgetOfBimodHBIso M⟩⟩⟩ }

end EssSurj

end TowerMod

end Tower

section TensorComparison

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {B H : Mon C} (f : B.X ⟶ H.X) [IsMonHom f]

/-- Restriction of the right action of an `(R, H)`-bimodule along `f`. -/
def restrictRight {R : Mon C} (M : Bimod R H) : Bimod R B where
  X := M.X
  actLeft := M.actLeft
  one_actLeft := M.one_actLeft
  left_assoc := M.left_assoc
  actRight := M.X ◁ f ≫ M.actRight
  actRight_one := by
    rw [← whiskerLeft_comp_assoc, IsMonHom.one_hom, M.actRight_one]
  right_assoc := by
    rw [← whiskerLeft_comp_assoc, IsMonHom.mul_hom, whiskerLeft_comp_assoc, M.right_assoc,
      MonoidalCategory.tensorHom_def, whiskerLeft_comp_assoc,
      associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc]
    conv_rhs => rw [comp_whiskerRight_assoc, ← whisker_exchange_assoc]
  middle_assoc := by
    rw [← whisker_exchange_assoc, M.middle_assoc, associator_naturality_right_assoc,
      whiskerLeft_comp_assoc]

/-- Restriction of the left action of an `(H, T)`-bimodule along `f`. -/
def restrictLeft {T : Mon C} (N : Bimod H T) : Bimod B T where
  X := N.X
  actLeft := f ▷ N.X ≫ N.actLeft
  one_actLeft := by
    rw [← comp_whiskerRight_assoc, IsMonHom.one_hom, N.one_actLeft]
  left_assoc := by
    rw [← comp_whiskerRight_assoc, IsMonHom.mul_hom, comp_whiskerRight_assoc,
      N.left_assoc, tensorHom_def', comp_whiskerRight_assoc,
      associator_naturality_left_assoc, associator_naturality_middle_assoc,
      whiskerLeft_comp_assoc]
    conv_rhs => rw [whisker_exchange_assoc]
  actRight := N.actRight
  actRight_one := N.actRight_one
  right_assoc := N.right_assoc
  middle_assoc := by
    rw [comp_whiskerRight_assoc, N.middle_assoc, associator_naturality_left_assoc,
      whisker_exchange_assoc]

/-- **`⊗_H` is a quotient of `⊗_B`**: the canonical map `M ⊗_B N ⟶ M ⊗_H N` (the
`H`-balancing relation implies the `B`-balancing relation, `B` acting through `f`). -/
noncomputable def tensorComparison {R T : Mon C} (M : Bimod R H) (N : Bimod H T) :
    ((restrictRight f M).tensorBimod (restrictLeft f N)).X ⟶ (M.tensorBimod N).X :=
  coequalizer.desc (coequalizer.π (M.actRight ▷ N.X) ((α_ M.X H.X N.X).hom ≫ M.X ◁ N.actLeft))
    (by
      show (M.X ◁ f ≫ M.actRight) ▷ N.X ≫ coequalizer.π _ _ =
        ((α_ M.X B.X N.X).hom ≫ M.X ◁ (f ▷ N.X ≫ N.actLeft)) ≫ coequalizer.π _ _
      rw [comp_whiskerRight_assoc, coequalizer.condition]
      simp only [Category.assoc]
      rw [associator_naturality_middle_assoc, whiskerLeft_comp_assoc])

/-- `π_B ≫ tensorComparison = π_H`. -/
@[reassoc]
theorem π_tensorComparison {R T : Mon C} (M : Bimod R H) (N : Bimod H T) :
    coequalizer.π ((restrictRight f M).actRight ▷ (restrictLeft f N).X)
        ((α_ (restrictRight f M).X B.X (restrictLeft f N).X).hom ≫
          (restrictRight f M).X ◁ (restrictLeft f N).actLeft) ≫ tensorComparison f M N =
      coequalizer.π (M.actRight ▷ N.X) ((α_ M.X H.X N.X).hom ≫ M.X ◁ N.actLeft) :=
  coequalizer.π_desc _ _

/-- The comparison `M ⊗_B N ⟶ M ⊗_H N` is an epimorphism. -/
theorem tensorComparison_epi {R T : Mon C} (M : Bimod R H) (N : Bimod H T) :
    Epi (tensorComparison f M N) :=
  ⟨fun g h e => coequalizer.hom_ext (by
    have h1 := π_tensorComparison_assoc f M N g
    have h2 := π_tensorComparison_assoc f M N h
    exact h1.symm.trans ((Category.assoc _ _ _).trans ((congrArg (CategoryStruct.comp _) e).trans
      ((Category.assoc _ _ _).symm.trans h2))))⟩

end TensorComparison

end ModuleTower

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ModuleTower.resBimod
#print axioms HaagerupIzumi.C8.ModuleTower.mulBimod
#print axioms HaagerupIzumi.C8.ModuleTower.monObj
#print axioms HaagerupIzumi.C8.ModuleTower.TowerMod.forget
#print axioms HaagerupIzumi.C8.ModuleTower.TowerMod.forget_faithful
#print axioms HaagerupIzumi.C8.ModuleTower.TowerMod.forget_full
#print axioms HaagerupIzumi.C8.ModuleTower.TowerMod.forget_isEquivalence
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_epi
