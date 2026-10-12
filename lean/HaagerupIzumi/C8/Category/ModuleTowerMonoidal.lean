module

public import HaagerupIzumi.C8.Category.ModuleTowerTensor

@[expose] public section

/-! # The tower comparison of relative tensor products: naturality, unit, associativity

Continuation of `Category/ModuleTower.lean` and `Category/ModuleTowerTensor.lean`: the coherence
of the comparison `q_{M,N} = tensorComparison f M N : M_B ⊗_B N_B ⟶ M ⊗_H N` (the projection that
exhibits `M ⊗_H N` as the coequalizer of the tower pair, `tensorComparisonIsColimit`).  This is
the tensorator data of the forgetful functor of the tower, in coequalizer form.

* `restrictRightHom`, `restrictLeftHom`: restriction of bimodule maps along `f`.
* `tensorComparison_whiskerRight`, `tensorComparison_whiskerLeft`: **naturality** of `q` in
  each variable: `q_{M,N} ≫ (φ ⊗_H N) = (φ_B ⊗_B N_B) ≫ q_{M',N}`, and likewise on the right.
* `tensorComparison_leftUnitor`, `tensorComparison_rightUnitor`: **unit compatibility**.  For the
  unit bimodule `H`, `q_{H,N}` followed by the unitor `H ⊗_H N ≅ N` is the descended action
  `H ⊗_B N_B ⟶ N` (`descActL`), and likewise on the right.
* `qRight`, `qLeft`: `q` as maps of bimodules, `M_B ⊗_B N_{BB} ⟶ (M ⊗_H N)_B` and
  `N_{BB} ⊗_B P_B ⟶ (N ⊗_H P)_B`, where `N_{BB}` is `N` restricted on both sides.
* `tensorComparison_assoc`: **associativity coherence**,
  `α^B ≫ (M_B ⊗_B q_{N,P}) ≫ q_{M,N⊗P} = (q_{M,N} ⊗_B P_B) ≫ q_{M⊗N,P} ≫ α^H`.

What is not formalized, and why: the packaging as a `Functor.Monoidal`.  Its source would be the
category of `H`-bimodules in `(Bimod B B, ⊗_B)` with the relative tensor product over the monoid
`H`.  That needs coequalizers in `Bimod B B` preserved by `⊗_B`, which Mathlib does not provide.
So the tensorator is stated through the comparison maps and their coherence above.
(`TowerMod f` consists of left modules only, which carry no tensor product.)
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

/-- Restriction of a map of `(R, H)`-bimodules along `f`. -/
def restrictRightHom {M M' : Bimod R H} (φ : M ⟶ M') : restrictRight f M ⟶ restrictRight f M' where
  hom := φ.hom
  left_act_hom := φ.left_act_hom
  right_act_hom := by
    show (M.X ◁ f ≫ M.actRight) ≫ φ.hom = φ.hom ▷ B.X ≫ M'.X ◁ f ≫ M'.actRight
    rw [Category.assoc, φ.right_act_hom, ← whisker_exchange_assoc]

/-- Restriction of a map of `(H, T)`-bimodules along `f`. -/
def restrictLeftHom {N N' : Bimod H T} (ψ : N ⟶ N') : restrictLeft f N ⟶ restrictLeft f N' where
  hom := ψ.hom
  left_act_hom := by
    show (f ▷ N.X ≫ N.actLeft) ≫ ψ.hom = B.X ◁ ψ.hom ≫ f ▷ N'.X ≫ N'.actLeft
    rw [Category.assoc, ψ.left_act_hom, whisker_exchange_assoc]
  right_act_hom := ψ.right_act_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the comparison in the left variable. -/
theorem tensorComparison_whiskerRight {M M' : Bimod R H} (φ : M ⟶ M') (N : Bimod H T) :
    tensorComparison f M N ≫ (Bimod.whiskerRight φ N).hom =
      (Bimod.whiskerRight (restrictRightHom f φ) (restrictLeft f N)).hom ≫
        tensorComparison f M' N := by
  apply coequalizer.hom_ext
  have h1 := π_tensorComparison f M N
  have h2 := π_tensorComparison f M' N
  calc _ = (πB f M N ≫ tensorComparison f M N) ≫ (Bimod.whiskerRight φ N).hom :=
        (Category.assoc _ _ _).symm
    _ = φ.hom ▷ N.X ≫ coequalizer.π (M'.actRight ▷ N.X)
          ((α_ M'.X H.X N.X).hom ≫ M'.X ◁ N.actLeft) := by
        rw [h1, π_whiskerRight_hom]
    _ = _ := by
        rw [π_whiskerRight_hom_assoc]
        exact (congrArg (φ.hom ▷ N.X ≫ ·) h2).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the comparison in the right variable. -/
theorem tensorComparison_whiskerLeft (M : Bimod R H) {N N' : Bimod H T} (ψ : N ⟶ N') :
    tensorComparison f M N ≫ (Bimod.whiskerLeft M ψ).hom =
      (Bimod.whiskerLeft (restrictRight f M) (restrictLeftHom f ψ)).hom ≫
        tensorComparison f M N' := by
  apply coequalizer.hom_ext
  have h1 := π_tensorComparison f M N
  have h2 := π_tensorComparison f M N'
  calc _ = (πB f M N ≫ tensorComparison f M N) ≫ (Bimod.whiskerLeft M ψ).hom :=
        (Category.assoc _ _ _).symm
    _ = M.X ◁ ψ.hom ≫ coequalizer.π (M.actRight ▷ N'.X)
          ((α_ M.X H.X N'.X).hom ≫ M.X ◁ N'.actLeft) := by
        rw [h1, π_whiskerLeft_hom]
    _ = _ := by
        rw [π_whiskerLeft_hom_assoc]
        exact (congrArg (M.X ◁ ψ.hom ≫ ·) h2).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left unit compatibility: `q_{H,N}` followed by the left unitor `H ⊗_H N ≅ N` is the
descended action `H ⊗_B N_B ⟶ N`. -/
theorem tensorComparison_leftUnitor (N : Bimod H T) :
    tensorComparison f (Bimod.regular H) N ≫ (Bimod.leftUnitorBimod N).hom.hom =
      descActL f N := by
  apply coequalizer.hom_ext
  have h1 := π_tensorComparison f (Bimod.regular H) N
  calc _ = (πB f (Bimod.regular H) N ≫ tensorComparison f (Bimod.regular H) N) ≫
          (Bimod.leftUnitorBimod N).hom.hom := (Category.assoc _ _ _).symm
    _ = N.actLeft := by rw [h1, π_leftUnitorBimod_hom]
    _ = _ := (π_descActL f N).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right unit compatibility: `q_{M,H}` followed by the right unitor `M ⊗_H H ≅ M` is the
descended action `M_B ⊗_B H ⟶ M`. -/
theorem tensorComparison_rightUnitor (M : Bimod R H) :
    tensorComparison f M (Bimod.regular H) ≫ (Bimod.rightUnitorBimod M).hom.hom =
      descActR f M := by
  apply coequalizer.hom_ext
  have h1 := π_tensorComparison f M (Bimod.regular H)
  calc _ = (πB f M (Bimod.regular H) ≫ tensorComparison f M (Bimod.regular H)) ≫
          (Bimod.rightUnitorBimod M).hom.hom := (Category.assoc _ _ _).symm
    _ = M.actRight := by rw [h1, π_rightUnitorBimod_hom]
    _ = _ := (π_descActR f M).symm


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `q_{M,N}` as a map of `(R, B)`-bimodules `M_B ⊗_B N_{BB} ⟶ (M ⊗_H N)_B`. -/
noncomputable def qRight (M : Bimod R H) (N : Bimod H H) :
    (restrictRight f M).tensorBimod (restrictLeft f (restrictRight f N)) ⟶
      restrictRight f (M.tensorBimod N) where
  hom := tensorComparison f M N
  left_act_hom := by
    refine (cancel_epi ((tensorLeft R.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [curriedTensor_obj_map, Bimod.tensorBimod_actLeft]
    rw [reassoc_of% Bimod.TensorBimod.whiskerLeft_π_actLeft, ← whiskerLeft_comp_assoc]
    show (α_ R.X M.X N.X).inv ≫ M.actLeft ▷ N.X ≫ πB f M N ≫ tensorComparison f M N =
      R.X ◁ (πB f M N ≫ tensorComparison f M N) ≫ (M.tensorBimod N).actLeft
    rw [π_tensorComparison, Bimod.tensorBimod_actLeft, Bimod.TensorBimod.whiskerLeft_π_actLeft]
  right_act_hom := by
    refine (cancel_epi ((tensorRight B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.tensorBimod_actRight]
    rw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight, ← comp_whiskerRight_assoc]
    show (α_ M.X N.X B.X).hom ≫ M.X ◁ (N.X ◁ f ≫ N.actRight) ≫ πB f M N ≫
        tensorComparison f M N =
      (πB f M N ≫ tensorComparison f M N) ▷ B.X ≫ (M.tensorBimod N).X ◁ f ≫
        (M.tensorBimod N).actRight
    rw [π_tensorComparison, whiskerLeft_comp_assoc]
    conv_rhs => rw [← whisker_exchange_assoc, Bimod.tensorBimod_actRight,
      Bimod.TensorBimod.π_tensor_id_actRight, associator_naturality_right_assoc]

theorem qRight_hom (M : Bimod R H) (N : Bimod H H) :
    (qRight f M N).hom = tensorComparison f M N := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `q_{N,P}` as a map of `(B, T)`-bimodules `N_{BB} ⊗_B P_B ⟶ (N ⊗_H P)_B`. -/
noncomputable def qLeft (N : Bimod H H) (P : Bimod H T) :
    (restrictLeft f (restrictRight f N)).tensorBimod (restrictLeft f P) ⟶
      restrictLeft f (N.tensorBimod P) where
  hom := tensorComparison f N P
  left_act_hom := by
    refine (cancel_epi ((tensorLeft B.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [curriedTensor_obj_map, Bimod.tensorBimod_actLeft]
    rw [reassoc_of% Bimod.TensorBimod.whiskerLeft_π_actLeft, ← whiskerLeft_comp_assoc]
    show (α_ B.X N.X P.X).inv ≫ (f ▷ N.X ≫ N.actLeft) ▷ P.X ≫ πB f N P ≫
        tensorComparison f N P =
      B.X ◁ (πB f N P ≫ tensorComparison f N P) ≫ f ▷ (N.tensorBimod P).X ≫
        (N.tensorBimod P).actLeft
    rw [π_tensorComparison, comp_whiskerRight_assoc]
    conv_rhs => rw [whisker_exchange_assoc, Bimod.tensorBimod_actLeft,
      Bimod.TensorBimod.whiskerLeft_π_actLeft, associator_inv_naturality_left_assoc]
  right_act_hom := by
    refine (cancel_epi ((tensorRight T.X).map (coequalizer.π _ _))).1 ?_
    dsimp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.tensorBimod_actRight]
    rw [reassoc_of% Bimod.TensorBimod.π_tensor_id_actRight, ← comp_whiskerRight_assoc]
    show (α_ N.X P.X T.X).hom ≫ N.X ◁ P.actRight ≫ πB f N P ≫ tensorComparison f N P =
      (πB f N P ≫ tensorComparison f N P) ▷ T.X ≫ (N.tensorBimod P).actRight
    rw [π_tensorComparison, Bimod.tensorBimod_actRight, Bimod.TensorBimod.π_tensor_id_actRight]

theorem qLeft_hom (N : Bimod H H) (P : Bimod H T) :
    (qLeft f N P).hom = tensorComparison f N P := rfl


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem π_qRight (M : Bimod R H) (N : Bimod H H) :
    coequalizer.π ((restrictRight f M).actRight ▷ (restrictLeft f (restrictRight f N)).X)
        ((α_ (restrictRight f M).X B.X (restrictLeft f (restrictRight f N)).X).hom ≫
          (restrictRight f M).X ◁ (restrictLeft f (restrictRight f N)).actLeft) ≫
        (qRight f M N).hom =
      coequalizer.π (M.actRight ▷ N.X) ((α_ M.X H.X N.X).hom ≫ M.X ◁ N.actLeft) :=
  π_tensorComparison f M N

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem π_qLeft (N : Bimod H H) (P : Bimod H T) :
    coequalizer.π ((restrictLeft f (restrictRight f N)).actRight ▷ (restrictLeft f P).X)
        ((α_ (restrictLeft f (restrictRight f N)).X B.X (restrictLeft f P).X).hom ≫
          (restrictLeft f (restrictRight f N)).X ◁ (restrictLeft f P).actLeft) ≫
        (qLeft f N P).hom =
      coequalizer.π (N.actRight ▷ P.X) ((α_ N.X H.X P.X).hom ≫ N.X ◁ P.actLeft) :=
  π_tensorComparison f N P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Associativity coherence of the comparison**: the two ways from
`(M_B ⊗_B N_{BB}) ⊗_B P_B` to `M ⊗_H (N ⊗_H P)` agree, i.e.
`α^B ≫ (M_B ⊗_B q_{N,P}) ≫ q_{M,N⊗P} = (q_{M,N} ⊗_B P_B) ≫ q_{M⊗N,P} ≫ α^H`. -/
theorem tensorComparison_assoc (M : Bimod R H) (N : Bimod H H) (P : Bimod H T) :
    (Bimod.associatorBimod (restrictRight f M) (restrictLeft f (restrictRight f N))
        (restrictLeft f P)).hom.hom ≫
      (Bimod.whiskerLeft (restrictRight f M) (qLeft f N P)).hom ≫
        tensorComparison f M (N.tensorBimod P) =
    (Bimod.whiskerRight (qRight f M N) (restrictLeft f P)).hom ≫
      tensorComparison f (M.tensorBimod N) P ≫ (Bimod.associatorBimod M N P).hom.hom := by
  apply coequalizer.hom_ext
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  rw [π_associatorBimod_hom_assoc, π_whiskerRight_homAux_assoc, π_whiskerLeft_hom_assoc,
    ← whiskerLeft_comp_assoc, π_qLeft, π_tensorComparison, π_whiskerRight_hom_assoc,
    ← comp_whiskerRight_assoc, π_qRight,
    reassoc_of% (π_tensorComparison f (M.tensorBimod N) P), π_associatorBimod_hom]
  exact (π_whiskerRight_homAux M N P).symm

end ModuleTower

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_whiskerRight
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_whiskerLeft
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_leftUnitor
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_rightUnitor
#print axioms HaagerupIzumi.C8.ModuleTower.qRight
#print axioms HaagerupIzumi.C8.ModuleTower.qLeft
#print axioms HaagerupIzumi.C8.ModuleTower.tensorComparison_assoc
