module

public import HaagerupIzumi.C8.Category.FreeModuleNaturality

@[expose] public section

/-! # Free induction is monoidal: unit and associativity coherence of the tensorator

Continuation of `Category/FreeModuleTensor.lean` and `Category/FreeModuleNaturality.lean`:
"Free `H/B`-module induction is tensor" (manuscript `haagerup_c8_expanded.tex`, lines
3337–3338).  For a commutative algebra `A` in a braided monoidal category `C`, write
`F X = X ⊗ A` (as an `A`-bimodule through `toBimod`), `μ_{X,Y} = freeTensorIso A X Y :
F X ⊗_A F Y ≅ F (X ⊗ Y)` and `ε = (freeUnitIso A)⁻¹ : A ≅ F 𝟙`.  The relative tensor
product, its unitors and associator are Mathlib's (`Bimod.tensorBimod`,
`Bimod.leftUnitorBimod`, `Bimod.rightUnitorBimod`, `Bimod.associatorBimod`: the bicategory
`Bimod.monBicategory`).

* `π_whiskerRight_hom`, `π_whiskerLeft_hom`, `π_associatorBimod_hom`, `π_whiskerRight_homAux`,
  `π_freeTensorIso_hom`: the relevant maps on the generators `m ⊗ n` of `M ⊗_A N`.
* `freeTensorIso_leftUnitality`, `freeTensorIso_rightUnitality`: the unit axioms of a monoidal
  functor (in the form of Mathlib's `Functor.CoreMonoidal.left_unitality`,
  `right_unitality`): `λ_{F X} = (ε ⊗_A F X) ≫ μ_{𝟙,X} ≫ F(λ_X)` and
  `ρ_{F X} = (F X ⊗_A ε) ≫ μ_{X,𝟙} ≫ F(ρ_X)`.  Right unitality uses that `ε` is a map of
  bimodules (commutativity of `A`).
* `freeActLeft_eq`: the left action `a · (w ⊗ b) = w ⊗ ab` of `F W` (hexagon and
  commutativity); `assoc_core`: the braided computation on generators
  `(x ⊗ a) ⊗ (y ⊗ b) ⊗ (z ⊗ c)` (hexagons, naturality of the braiding, commutativity and
  associativity of `A`); `freeTensorIso_associativity`: the associativity axiom
  `(μ_{X,Y} ⊗_A F Z) ≫ μ_{X⊗Y,Z} ≫ F(α) = α_{FX,FY,FZ} ≫ (F X ⊗_A μ_{Y,Z}) ≫ μ_{X,Y⊗Z}`
  (Mathlib's `Functor.CoreMonoidal.associativity`).

Together with `freeTensorIso_natural_left`, `freeTensorIso_natural_right`
(`Category/FreeModuleNaturality.lean`) these are all the axioms of a monoidal functor
`C ⥤ (Bimod A A, ⊗_A)`; they are assembled in `Category/FreeModuleMonoidalFunctor.lean`.

Hypotheses: those of `Category/FreeModuleTensor.lean` (`C` has coequalizers preserved by
`X ⊗ -` and `- ⊗ X`; `A` commutative).  No external-theorem or certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section Generic

/-- Coherence used for the left unit axiom. -/
theorem leftUnit_aux {P W X Y : C} (f : P ⊗ W ⟶ X ⊗ Y) :
    f = (λ_ P).inv ▷ W ≫ ((α_ (𝟙_ C) P W).hom ≫ 𝟙_ C ◁ f) ≫ (α_ (𝟙_ C) X Y).inv ≫
      (λ_ X).hom ▷ Y := by
  monoidal

/-- Coherence used for the right unit axiom. -/
theorem rightUnit_aux {X P : C} (m : P ⊗ P ⟶ P) :
    (α_ X P P).hom ≫ X ◁ m =
      (X ⊗ P) ◁ (λ_ P).inv ≫ ((α_ X P (𝟙_ C ⊗ P)).hom ≫
        X ◁ ((P ◁ (λ_ P).hom ≫ m) ≫ (λ_ P).inv)) ≫ (α_ X (𝟙_ C) P).inv ≫ (ρ_ X).hom ▷ P := by
  monoidal

end Generic

section Braided

variable [BraidedCategory C] (A : Mon C) [IsCommMonObj A.X]

/-- The left action of `A` on the free module `W ⊗ A` (the bimodule `toBimod (free A W)`):
`a · (w ⊗ b) = w ⊗ b a`, through the braiding `c_{A, W ⊗ A}`. -/
def freeActLeft (W : C) : A.X ⊗ (W ⊗ A.X) ⟶ W ⊗ A.X :=
  (β_ A.X (W ⊗ A.X)).hom ≫ (α_ W A.X A.X).hom ≫ W ◁ μ[A.X]

/-- `a · (w ⊗ b) = w ⊗ a b` (hexagon identity and commutativity of `A`). -/
theorem freeActLeft_eq (W : C) :
    freeActLeft A W =
      (α_ A.X W A.X).inv ≫ (β_ A.X W).hom ▷ A.X ≫ (α_ W A.X A.X).hom ≫ W ◁ μ[A.X] := by
  rw [freeActLeft, BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, IsCommMonObj.mul_comm A.X]

/-- The braided computation behind the associativity of the tensorator of free induction:
`x ⊗ (a·(y ⊗ b)) ⊗ (z ⊗ c)` followed by `(ab)·(z ⊗ c)` agrees with
`x ⊗ a·(y ⊗ b·(z ⊗ c))` (hexagons, naturality of the braiding, and the commutativity and
associativity of `A`). -/
theorem assoc_core (X Y Z : C) :
    (((α_ X A.X (Y ⊗ A.X)).hom ≫ X ◁ freeActLeft A Y) ≫ (α_ X Y A.X).inv) ▷ (Z ⊗ A.X) ≫
        ((α_ (X ⊗ Y) A.X (Z ⊗ A.X)).hom ≫ (X ⊗ Y) ◁ freeActLeft A Z) ≫
          (α_ (X ⊗ Y) Z A.X).inv ≫ (α_ X Y Z).hom ▷ A.X =
      (α_ (X ⊗ A.X) (Y ⊗ A.X) (Z ⊗ A.X)).hom ≫
        (X ⊗ A.X) ◁ (((α_ Y A.X (Z ⊗ A.X)).hom ≫ Y ◁ freeActLeft A Z) ≫ (α_ Y Z A.X).inv) ≫
          ((α_ X A.X ((Y ⊗ Z) ⊗ A.X)).hom ≫ X ◁ freeActLeft A (Y ⊗ Z)) ≫
            (α_ X (Y ⊗ Z) A.X).inv := by
  simp only [freeActLeft_eq]
  rw [BraidedCategory.braiding_tensor_right_hom A.X Y Z]
  calc _ = 𝟙 _ ⊗≫ X ◁ (β_ A.X Y).hom ▷ (A.X ⊗ (Z ⊗ A.X)) ⊗≫
          (X ⊗ Y) ◁ ((μ[A.X] ▷ Z ≫ (β_ A.X Z).hom) ▷ A.X) ⊗≫
          (X ⊗ Y) ◁ Z ◁ μ[A.X] ⊗≫ 𝟙 _ := by
        monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (β_ A.X Y).hom ▷ (A.X ⊗ (Z ⊗ A.X)) ⊗≫
          (X ⊗ Y) ◁ (((β_ (A.X ⊗ A.X) Z).hom ≫ Z ◁ μ[A.X]) ▷ A.X) ⊗≫
          (X ⊗ Y) ◁ Z ◁ μ[A.X] ⊗≫ 𝟙 _ := by
        rw [BraidedCategory.braiding_naturality_left]
    _ = 𝟙 _ ⊗≫
          X ◁ ((β_ A.X Y).hom ▷ ((A.X ⊗ Z) ⊗ A.X) ≫ (Y ⊗ A.X) ◁ ((β_ A.X Z).hom ▷ A.X)) ⊗≫
          X ◁ Y ◁ ((β_ A.X Z).hom ▷ A.X) ▷ A.X ⊗≫
          X ◁ Y ◁ Z ◁ ((α_ A.X A.X A.X).hom ≫ A.X ◁ μ[A.X] ≫ μ[A.X]) ⊗≫ 𝟙 _ := by
        rw [BraidedCategory.braiding_tensor_left_hom, ← MonObj.mul_assoc A.X]
        monoidal
    _ = 𝟙 _ ⊗≫
          X ◁ ((A.X ⊗ Y) ◁ ((β_ A.X Z).hom ▷ A.X) ≫ (β_ A.X Y).hom ▷ ((Z ⊗ A.X) ⊗ A.X)) ⊗≫
          X ◁ Y ◁ ((β_ A.X Z).hom ▷ A.X) ▷ A.X ⊗≫
          X ◁ Y ◁ Z ◁ ((α_ A.X A.X A.X).hom ≫ A.X ◁ μ[A.X] ≫ μ[A.X]) ⊗≫ 𝟙 _ := by
        rw [← MonoidalCategory.whisker_exchange]
    _ = 𝟙 _ ⊗≫ X ◁ A.X ◁ Y ◁ (β_ A.X Z).hom ▷ A.X ⊗≫
          X ◁ (((β_ A.X Y).hom ▷ Z ≫ (α_ Y A.X Z).hom ≫ Y ◁ (β_ A.X Z).hom ≫
              (α_ Y Z A.X).inv) ▷ (A.X ⊗ A.X) ≫ ((Y ⊗ Z) ⊗ A.X) ◁ μ[A.X]) ⊗≫
          X ◁ Y ◁ Z ◁ μ[A.X] ⊗≫ 𝟙 _ := by
        monoidal
    _ = 𝟙 _ ⊗≫ X ◁ A.X ◁ Y ◁ (β_ A.X Z).hom ▷ A.X ⊗≫
          X ◁ (((A.X ⊗ Y) ⊗ Z) ◁ μ[A.X] ≫ ((β_ A.X Y).hom ▷ Z ≫ (α_ Y A.X Z).hom ≫
              Y ◁ (β_ A.X Z).hom ≫ (α_ Y Z A.X).inv) ▷ A.X) ⊗≫
          X ◁ Y ◁ Z ◁ μ[A.X] ⊗≫ 𝟙 _ := by
        rw [← MonoidalCategory.whisker_exchange]
    _ = _ := by
        monoidal

end Braided

variable [BraidedCategory C] (A : Mon C) [IsCommMonObj A.X] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

omit [BraidedCategory C] [IsCommMonObj A.X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(φ ⊗_A Q)(m ⊗ q) = φ(m) ⊗ q`. -/
@[reassoc]
theorem π_whiskerRight_hom {M₁ M₂ : Bimod A A} (φ : M₁ ⟶ M₂) (Q : Bimod A A) :
    coequalizer.π (M₁.actRight ▷ Q.X) ((α_ M₁.X A.X Q.X).hom ≫ M₁.X ◁ Q.actLeft) ≫
        (Bimod.whiskerRight φ Q).hom =
      φ.hom ▷ Q.X ≫
        coequalizer.π (M₂.actRight ▷ Q.X) ((α_ M₂.X A.X Q.X).hom ≫ M₂.X ◁ Q.actLeft) := by
  rw [Bimod.whiskerRight_hom]
  try dsimp only [Bimod.tensorBimod_X, Bimod.TensorBimod.X]
  rw [ι_colimMap, parallelPairHom_app_one]

omit [BraidedCategory C] [IsCommMonObj A.X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(M ⊗_A φ)(m ⊗ q) = m ⊗ φ(q)`. -/
@[reassoc]
theorem π_whiskerLeft_hom (M : Bimod A A) {Q₁ Q₂ : Bimod A A} (φ : Q₁ ⟶ Q₂) :
    coequalizer.π (M.actRight ▷ Q₁.X) ((α_ M.X A.X Q₁.X).hom ≫ M.X ◁ Q₁.actLeft) ≫
        (Bimod.whiskerLeft M φ).hom =
      M.X ◁ φ.hom ≫
        coequalizer.π (M.actRight ▷ Q₂.X) ((α_ M.X A.X Q₂.X).hom ≫ M.X ◁ Q₂.actLeft) := by
  rw [Bimod.whiskerLeft_hom]
  try dsimp only [Bimod.tensorBimod_X, Bimod.TensorBimod.X]
  rw [ι_colimMap, parallelPairHom_app_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Left unitality** of the tensorator of free induction:
`λ_{F X} = (ε ⊗_A F X) ≫ μ_{𝟙,X} ≫ F(λ_X)`. -/
theorem freeTensorIso_leftUnitality (X : C) :
    (Bimod.leftUnitorBimod ((toBimod A).obj (free A X))).hom =
      Bimod.whiskerRight (freeUnitIso A).inv ((toBimod A).obj (free A X)) ≫
        (freeTensorIso A (𝟙_ C) X).hom ≫ (toBimod A).map (freeMap A (λ_ X).hom) := by
  apply Bimod.hom_ext
  apply coequalizer.hom_ext
  rw [Bimod.comp_hom', Bimod.comp_hom', reassoc_of% π_whiskerRight_hom,
    freeTensorIso_hom_hom]
  simp only [Category.assoc]
  rw [reassoc_of% freeTensorXIso_π]
  exact (coequalizer.π_desc _ _).trans (leftUnit_aux _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Right unitality** of the tensorator of free induction:
`ρ_{F X} = (F X ⊗_A ε) ≫ μ_{X,𝟙} ≫ F(ρ_X)`. -/
theorem freeTensorIso_rightUnitality (X : C) :
    (Bimod.rightUnitorBimod ((toBimod A).obj (free A X))).hom =
      Bimod.whiskerLeft ((toBimod A).obj (free A X)) (freeUnitIso A).inv ≫
        (freeTensorIso A X (𝟙_ C)).hom ≫ (toBimod A).map (freeMap A (ρ_ X).hom) := by
  have h : ((toBimod A).obj (free A (𝟙_ C))).actLeft ≫ (λ_ A.X).hom =
      A.X ◁ (λ_ A.X).hom ≫ μ[A.X] :=
    (freeUnitIso A).hom.left_act_hom
  have hL : ((toBimod A).obj (free A (𝟙_ C))).actLeft =
      (A.X ◁ (λ_ A.X).hom ≫ μ[A.X]) ≫ (λ_ A.X).inv :=
    (Iso.eq_comp_inv (λ_ A.X)).2 h
  apply Bimod.hom_ext
  apply coequalizer.hom_ext
  rw [Bimod.comp_hom', Bimod.comp_hom', reassoc_of% π_whiskerLeft_hom,
    freeTensorIso_hom_hom]
  simp only [Category.assoc]
  rw [reassoc_of% freeTensorXIso_π, freeTensorπ, hL]
  exact (coequalizer.π_desc _ _).trans (rightUnit_aux _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `μ_{X,Y}` on generators: `(x ⊗ a) ⊗ (y ⊗ b) ↦ x ⊗ a·(y ⊗ b)`, then the associator. -/
@[reassoc]
theorem π_freeTensorIso_hom (X Y : C) :
    coequalizer.π (((toBimod A).obj (free A X)).actRight ▷ ((toBimod A).obj (free A Y)).X)
        ((α_ ((toBimod A).obj (free A X)).X A.X ((toBimod A).obj (free A Y)).X).hom ≫
          ((toBimod A).obj (free A X)).X ◁ ((toBimod A).obj (free A Y)).actLeft) ≫
        (freeTensorIso A X Y).hom.hom =
      freeTensorπ A X ((toBimod A).obj (free A Y)) ≫ (α_ X Y A.X).inv := by
  rw [freeTensorIso_hom_hom, reassoc_of% freeTensorXIso_π]

omit [BraidedCategory C] [IsCommMonObj A.X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator of `⊗_A` on generators. -/
@[reassoc]
theorem π_associatorBimod_hom (P Q L : Bimod A A) :
    coequalizer.π ((P.tensorBimod Q).actRight ▷ L.X)
        ((α_ (P.tensorBimod Q).X A.X L.X).hom ≫ (P.tensorBimod Q).X ◁ L.actLeft) ≫
        (Bimod.associatorBimod P Q L).hom.hom = Bimod.AssociatorBimod.homAux P Q L :=
  coequalizer.π_desc _ _

omit [BraidedCategory C] [IsCommMonObj A.X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator of `⊗_A` on generators: `((p ⊗ q) ⊗ l) ↦ p ⊗ (q ⊗ l)`. -/
@[reassoc]
theorem π_whiskerRight_homAux (P Q L : Bimod A A) :
    (coequalizer.π (P.actRight ▷ Q.X) ((α_ P.X A.X Q.X).hom ≫ P.X ◁ Q.actLeft) ▷ L.X) ≫
        Bimod.AssociatorBimod.homAux P Q L =
      (α_ P.X Q.X L.X).hom ≫
        P.X ◁ coequalizer.π (Q.actRight ▷ L.X) ((α_ Q.X A.X L.X).hom ≫ Q.X ◁ L.actLeft) ≫
          coequalizer.π (P.actRight ▷ (Q.tensorBimod L).X)
            ((α_ P.X A.X (Q.tensorBimod L).X).hom ≫ P.X ◁ (Q.tensorBimod L).actLeft) :=
  π_tensor_id_preserves_coequalizer_inv_desc _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Associativity** of the tensorator of free induction (the associativity axiom of a
monoidal functor, in the form of Mathlib's `Functor.CoreMonoidal.associativity`):
`(μ_{X,Y} ⊗_A F Z) ≫ μ_{X⊗Y,Z} ≫ F(α_{X,Y,Z}) = α_{F X,F Y,F Z} ≫ (F X ⊗_A μ_{Y,Z}) ≫
μ_{X,Y⊗Z}`. -/
theorem freeTensorIso_associativity (X Y Z : C) :
    Bimod.whiskerRight (freeTensorIso A X Y).hom ((toBimod A).obj (free A Z)) ≫
        (freeTensorIso A (X ⊗ Y) Z).hom ≫ (toBimod A).map (freeMap A (α_ X Y Z).hom) =
      (Bimod.associatorBimod ((toBimod A).obj (free A X)) ((toBimod A).obj (free A Y))
          ((toBimod A).obj (free A Z))).hom ≫
        Bimod.whiskerLeft ((toBimod A).obj (free A X)) (freeTensorIso A Y Z).hom ≫
          (freeTensorIso A X (Y ⊗ Z)).hom := by
  apply Bimod.hom_ext
  apply coequalizer.hom_ext
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app, Bimod.comp_hom']
  rw [π_whiskerRight_hom_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
    π_freeTensorIso_hom, π_freeTensorIso_hom_assoc, π_associatorBimod_hom_assoc,
    π_whiskerRight_homAux_assoc, π_whiskerLeft_hom_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, π_freeTensorIso_hom, π_freeTensorIso_hom]
  exact assoc_core A X Y Z

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.π_whiskerRight_hom
#print axioms HaagerupIzumi.C8.RightMod.π_whiskerLeft_hom
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso_leftUnitality
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso_rightUnitality
#print axioms HaagerupIzumi.C8.RightMod.freeActLeft_eq
#print axioms HaagerupIzumi.C8.RightMod.assoc_core
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso_associativity
