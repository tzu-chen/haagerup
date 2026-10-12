module

public import HaagerupIzumi.C8.Category.ModuleTower

@[expose] public section

/-! # The module tower and relative tensor products

Continuation of `Category/ModuleTower.lean` (manuscript lines 3349–3352: the forgetful
embedding "preserves ... relative tensor products").  For a monoid morphism `f : B ⟶ H`, an
`(R, H)`-bimodule `M` and an `(H, T)`-bimodule `N`, restrict to `M_B` (right `B`-action) and
`N_B` (left `B`-action).  Then:

* `rightActBimod`, `leftActBimod`: the `H`-actions descend to bimodule maps
  `M_B ⊗_B H ⟶ M_B` and `H ⊗_B N_B ⟶ N_B`;
* `towerPair₁`, `towerPair₂ : (M_B ⊗_B H) ⊗_B N_B ⇉ M_B ⊗_B N_B` (act on the left factor,
  resp. associate and act on the right factor): the pair whose coequalizer is the relative
  tensor product over the monoid `H` of `(Bimod B B, ⊗_B)`, computed in `C`;
* `tensorComparison_isColimit`: **`M ⊗_H N` (Mathlib's relative tensor product over `H` in
  `C`) is the coequalizer of this pair**, with projection `tensorComparison f M N`.  That is,
  the relative tensor product computed in the tower (first over `B`, then over `H`) agrees with
  the one computed directly over `H`.

No external-theorem or certificate inputs. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ModuleTower

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {B H : Mon C} (f : B.X ⟶ H.X) [IsMonHom f] {R T : Mon C}

theorem actRight_whiskerRight_actRight (M : Bimod R H) :
    M.actRight ▷ H.X ≫ M.actRight = (α_ M.X H.X H.X).hom ≫ M.X ◁ μ[H.X] ≫ M.actRight := by
  rw [M.right_assoc, Iso.hom_inv_id_assoc]

/-- The right `H`-action of `M` descended to `M_B ⊗_B H`. -/
noncomputable def descActR (M : Bimod R H) :
    ((restrictRight f M).tensorBimod (resBimod f)).X ⟶ M.X :=
  coequalizer.desc M.actRight (by
    show (M.X ◁ f ≫ M.actRight) ▷ H.X ≫ M.actRight =
      ((α_ M.X B.X H.X).hom ≫ M.X ◁ (f ▷ H.X ≫ μ[H.X])) ≫ M.actRight
    rw [comp_whiskerRight_assoc, actRight_whiskerRight_actRight,
      associator_naturality_middle_assoc, Category.assoc, whiskerLeft_comp_assoc])

@[reassoc]
theorem π_descActR (M : Bimod R H) :
    coequalizer.π ((restrictRight f M).actRight ▷ (resBimod f).X)
        ((α_ (restrictRight f M).X B.X (resBimod f).X).hom ≫
          (restrictRight f M).X ◁ (resBimod f).actLeft) ≫ descActR f M = M.actRight :=
  coequalizer.π_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The descended right action as a map of `(R, B)`-bimodules. -/
noncomputable def rightActBimod (M : Bimod R H) :
    (restrictRight f M).tensorBimod (resBimod f) ⟶ restrictRight f M where
  hom := descActR f M
  left_act_hom := by
    refine (cancel_epi ((tensorLeft R.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [curriedTensor_obj_map, Bimod.tensorBimod_actLeft]
    rw [reassoc_of% Bimod.TensorBimod.whiskerLeft_π_actLeft, π_descActR,
      ← whiskerLeft_comp_assoc, π_descActR]
    show (α_ R.X M.X H.X).inv ≫ M.actLeft ▷ H.X ≫ M.actRight = R.X ◁ M.actRight ≫ M.actLeft
    rw [M.middle_assoc, Iso.inv_hom_id_assoc]
  right_act_hom := by
    refine (cancel_epi ((tensorRight B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.tensorBimod_actRight]
    rw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight, π_descActR,
      ← comp_whiskerRight_assoc, π_descActR]
    show (α_ M.X H.X B.X).hom ≫ M.X ◁ (H.X ◁ f ≫ μ[H.X]) ≫ M.actRight =
      M.actRight ▷ B.X ≫ M.X ◁ f ≫ M.actRight
    rw [whiskerLeft_comp_assoc]
    conv_rhs => rw [← whisker_exchange_assoc, actRight_whiskerRight_actRight,
      associator_naturality_right_assoc]

theorem rightActBimod_hom (M : Bimod R H) : (rightActBimod f M).hom = descActR f M := rfl

/-- The left `H`-action of `N` descended to `H ⊗_B N_B`. -/
noncomputable def descActL (N : Bimod H T) :
    ((resBimod f).tensorBimod (restrictLeft f N)).X ⟶ N.X :=
  coequalizer.desc N.actLeft (by
    show (H.X ◁ f ≫ μ[H.X]) ▷ N.X ≫ N.actLeft =
      ((α_ H.X B.X N.X).hom ≫ H.X ◁ (f ▷ N.X ≫ N.actLeft)) ≫ N.actLeft
    rw [comp_whiskerRight_assoc, N.left_assoc, associator_naturality_middle_assoc,
      Category.assoc, whiskerLeft_comp_assoc])

@[reassoc]
theorem π_descActL (N : Bimod H T) :
    coequalizer.π ((resBimod f).actRight ▷ (restrictLeft f N).X)
        ((α_ (resBimod f).X B.X (restrictLeft f N).X).hom ≫
          (resBimod f).X ◁ (restrictLeft f N).actLeft) ≫ descActL f N = N.actLeft :=
  coequalizer.π_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The descended left action as a map of `(B, T)`-bimodules. -/
noncomputable def leftActBimod (N : Bimod H T) :
    (resBimod f).tensorBimod (restrictLeft f N) ⟶ restrictLeft f N where
  hom := descActL f N
  left_act_hom := by
    refine (cancel_epi ((tensorLeft B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [curriedTensor_obj_map, Bimod.tensorBimod_actLeft]
    rw [reassoc_of% Bimod.TensorBimod.whiskerLeft_π_actLeft, π_descActL,
      ← whiskerLeft_comp_assoc, π_descActL]
    show (α_ B.X H.X N.X).inv ≫ (f ▷ H.X ≫ μ[H.X]) ▷ N.X ≫ N.actLeft =
      B.X ◁ N.actLeft ≫ f ▷ N.X ≫ N.actLeft
    rw [comp_whiskerRight_assoc, N.left_assoc, associator_naturality_left_assoc,
      Iso.inv_hom_id_assoc, whisker_exchange_assoc]
  right_act_hom := by
    refine (cancel_epi ((tensorRight T.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.tensorBimod_actRight]
    rw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight, π_descActL,
      ← comp_whiskerRight_assoc, π_descActL]
    exact N.middle_assoc.symm

theorem leftActBimod_hom (N : Bimod H T) : (leftActBimod f N).hom = descActL f N := rfl

/-- Act on the left factor: `(m ⊗ h) ⊗ n ↦ m h ⊗ n`. -/
noncomputable def towerPair₁ (M : Bimod R H) (N : Bimod H T) :
    (((restrictRight f M).tensorBimod (resBimod f)).tensorBimod (restrictLeft f N)).X ⟶
      ((restrictRight f M).tensorBimod (restrictLeft f N)).X :=
  (Bimod.whiskerRight (rightActBimod f M) (restrictLeft f N)).hom

/-- Associate and act on the right factor: `(m ⊗ h) ⊗ n ↦ m ⊗ h n`. -/
noncomputable def towerPair₂ (M : Bimod R H) (N : Bimod H T) :
    (((restrictRight f M).tensorBimod (resBimod f)).tensorBimod (restrictLeft f N)).X ⟶
      ((restrictRight f M).tensorBimod (restrictLeft f N)).X :=
  (Bimod.associatorBimod (restrictRight f M) (resBimod f) (restrictLeft f N)).hom.hom ≫
    (Bimod.whiskerLeft (restrictRight f M) (leftActBimod f N)).hom

/-- The projection `M ⊗ N ⟶ M_B ⊗_B N_B`. -/
noncomputable abbrev πB (M : Bimod R H) (N : Bimod H T) :
    M.X ⊗ N.X ⟶ ((restrictRight f M).tensorBimod (restrictLeft f N)).X :=
  coequalizer.π ((restrictRight f M).actRight ▷ (restrictLeft f N).X)
    ((α_ (restrictRight f M).X B.X (restrictLeft f N).X).hom ≫
      (restrictRight f M).X ◁ (restrictLeft f N).actLeft)

/-- The projection `M ⊗ H ⟶ M_B ⊗_B H`. -/
noncomputable abbrev πMH (M : Bimod R H) :
    M.X ⊗ H.X ⟶ ((restrictRight f M).tensorBimod (resBimod f)).X :=
  coequalizer.π ((restrictRight f M).actRight ▷ (resBimod f).X)
    ((α_ (restrictRight f M).X B.X (resBimod f).X).hom ≫
      (restrictRight f M).X ◁ (resBimod f).actLeft)

/-- The projection `(M_B ⊗_B H) ⊗ N ⟶ (M_B ⊗_B H) ⊗_B N_B`. -/
noncomputable abbrev πMHN (M : Bimod R H) (N : Bimod H T) :
    ((restrictRight f M).tensorBimod (resBimod f)).X ⊗ N.X ⟶
      (((restrictRight f M).tensorBimod (resBimod f)).tensorBimod (restrictLeft f N)).X :=
  coequalizer.π (((restrictRight f M).tensorBimod (resBimod f)).actRight ▷
      (restrictLeft f N).X)
    ((α_ ((restrictRight f M).tensorBimod (resBimod f)).X B.X (restrictLeft f N).X).hom ≫
      ((restrictRight f M).tensorBimod (resBimod f)).X ◁ (restrictLeft f N).actLeft)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `towerPair₁` on generators: `(m ⊗ h) ⊗ n ↦ m h ⊗ n`. -/
@[reassoc]
theorem gen_pair₁ (M : Bimod R H) (N : Bimod H T) :
    πMH f M ▷ (restrictLeft f N).X ≫ πMHN f M N ≫ towerPair₁ f M N =
      M.actRight ▷ (restrictLeft f N).X ≫ πB f M N := by
  rw [towerPair₁, π_whiskerRight_hom, ← comp_whiskerRight_assoc, rightActBimod_hom, π_descActR]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `towerPair₂` on generators: `(m ⊗ h) ⊗ n ↦ m ⊗ h n`. -/
@[reassoc]
theorem gen_pair₂ (M : Bimod R H) (N : Bimod H T) :
    πMH f M ▷ (restrictLeft f N).X ≫ πMHN f M N ≫ towerPair₂ f M N =
      (α_ (restrictRight f M).X (resBimod f).X (restrictLeft f N).X).hom ≫
        (restrictRight f M).X ◁ N.actLeft ≫ πB f M N := by
  rw [towerPair₂, π_associatorBimod_hom_assoc, π_whiskerRight_homAux_assoc, π_whiskerLeft_hom,
    ← whiskerLeft_comp_assoc, leftActBimod_hom, π_descActL]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison map coequalizes the tower pair. -/
theorem tensorComparison_condition (M : Bimod R H) (N : Bimod H T) :
    towerPair₁ f M N ≫ tensorComparison f M N = towerPair₂ f M N ≫ tensorComparison f M N := by
  apply coequalizer.hom_ext
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  rw [gen_pair₁_assoc, gen_pair₂_assoc, π_tensorComparison]
  exact (coequalizer.condition _ _).trans (Category.assoc _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The relative tensor product over `H` computed in the tower**: `M ⊗_H N` (Mathlib's, over
`H` in `C`), with the comparison `M_B ⊗_B N_B ⟶ M ⊗_H N`, is a coequalizer of the tower pair
`(M_B ⊗_B H) ⊗_B N_B ⇉ M_B ⊗_B N_B`. -/
noncomputable def tensorComparisonIsColimit (M : Bimod R H) (N : Bimod H T) :
    IsColimit (Cofork.ofπ (tensorComparison f M N) (tensorComparison_condition f M N)) :=
  Cofork.IsColimit.mk' _ fun s => by
    have hbal : (M.actRight ▷ N.X) ≫ πB f M N ≫ s.π =
        ((α_ M.X H.X N.X).hom ≫ M.X ◁ N.actLeft) ≫ πB f M N ≫ s.π := by
      have h := congrArg (fun k => πMH f M ▷ (restrictLeft f N).X ≫ πMHN f M N ≫ k)
        s.condition
      rw [gen_pair₁_assoc, gen_pair₂_assoc] at h
      exact h.trans (Category.assoc _ _ _).symm
    refine ⟨coequalizer.desc (πB f M N ≫ s.π) hbal, ?_, fun {m} hm => ?_⟩
    · apply coequalizer.hom_ext
      calc _ = (πB f M N ≫ tensorComparison f M N) ≫
            coequalizer.desc (πB f M N ≫ s.π) hbal := (Category.assoc _ _ _).symm
        _ = _ := by rw [π_tensorComparison, coequalizer.π_desc]
    · refine coequalizer.hom_ext (f := M.actRight ▷ N.X)
        (g := (α_ M.X H.X N.X).hom ≫ M.X ◁ N.actLeft) (k := m) ?_
      rw [coequalizer.π_desc, ← hm, ← Category.assoc]
      exact (congrArg (· ≫ m) (π_tensorComparison f M N)).symm

end ModuleTower

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ModuleTower.rightActBimod
#print axioms HaagerupIzumi.C8.ModuleTower.leftActBimod
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_condition
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparisonIsColimit
