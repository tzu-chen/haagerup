module

public import HaagerupIzumi.C8.Category.FreeModule
public import HaagerupIzumi.C8.Category.RelativeTensor

@[expose] public section

/-! # Free induction carries `⊗` to `⊗_A`: the tensorator on objects

Toward the first sentence of the identification step of `L_untwisted` (manuscript
`haagerup_c8_expanded.tex`, lines 3337–3338): "Free `H/B`-module induction is tensor on this
subcategory."  For a commutative algebra `A` in a braided monoidal category `C` we construct
the components of the tensor structure of free induction `X ↦ X ⊗ A` with values in the
relative tensor product `⊗_A` of `Category/RelativeTensor.lean` (Mathlib's
`Bimod.tensorBimod`, right modules being viewed as bimodules through the braiding, `toBimod`).

* `freeTensorXIso A X Q : (X ⊗ A) ⊗_A Q ≅ X ⊗ Q` (underlying objects) for every
  `A`-bimodule `Q`: the cofork `(X ⊗ A) ⊗ Q ⟶ X ⊗ Q`, `(x ⊗ a) ⊗ q ↦ x ⊗ a·q`, is a split
  coequalizer of the two actions (sections `x ⊗ q ↦ (x ⊗ 1) ⊗ q` and
  `(x ⊗ a) ⊗ q ↦ ((x ⊗ 1) ⊗ a) ⊗ q`; only the unit and associativity of the left action of
  `Q` are used).  `freeTensorXIso_actRight`: it intertwines the right actions (by the
  `middle_assoc` law of `Q`).  `freeTensorXIso_whiskerRight`, `freeTensorXIso_whiskerLeft`:
  it is natural in `X` and in `Q`.
* `freeTensorRightModIso A X Y`: the right module underlying `(X ⊗ A) ⊗_A (Y ⊗ A)` is
  isomorphic to `(X ⊗ Y) ⊗ A`.
* `freeTensorIso A X Y : (X ⊗ A) ⊗_A (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A` as `A`-bimodules (built with
  `Bimod.isoOfIso`; the left actions agree because both bimodules satisfy
  `actLeft = c_{A,-} ≫ actRight`, `tensorBimod_relation`, and by naturality of the braiding).
  Its underlying morphism is `freeTensorXIso` followed by the associator
  (`freeTensorIso_hom_hom`), so its naturality in `X` and `Y` reduces to
  `freeTensorXIso_whiskerRight`, `freeTensorXIso_whiskerLeft` and naturality of the
  associator; that assembly is `freeTensorIso_natural_left/right` in
  `Category/FreeModuleNaturality.lean`.
* `freeUnitIso A : 𝟙 ⊗ A ≅ A` as `A`-bimodules (the regular bimodule `Bimod.regular A`):
  the unit isomorphism.

Hypotheses: those of `Category/RelativeTensor.lean`: `C` has coequalizers and `X ⊗ -`,
`- ⊗ X` preserve them.  These hold in any rigid abelian (e.g. fusion) category (coequalizers
exist, and `X ⊗ -`, `- ⊗ X` are left adjoints); for separable `A` the coequalizer defining
`⊗_A` is moreover split (`Category/SeparableCoequalizer.lean`).  Also the commutativity of `A`.  No external-theorem or certificate
inputs.

Continued in: `Category/FreeModuleNaturality.lean` (naturality of `freeTensorIso`),
`Category/FreeModuleMonoidal.lean` (unit and associativity coherence) and
`Category/FreeModuleMonoidalFunctor.lean` (`freeCoreMonoidal`: free induction is a monoidal
functor `C ⥤ (Bimod A A, ⊗_A)`).  Not formalized: a monoidal structure on `𝒞_A = RightMod A`
itself (here `⊗_A` is taken in Mathlib's bicategory of bimodules, `Bimod.monBicategory`); the
restriction to the pointed subcategory on `L₋`. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section Generic

variable {A : Mon C}

/-- An isomorphism of underlying objects intertwining the actions is an isomorphism of right
modules. -/
def isoOfIso {M N : RightMod A} (e : M.X ≅ N.X) (h : M.act ≫ e.hom = e.hom ▷ A.X ≫ N.act) :
    M ≅ N where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    rw [Iso.comp_inv_eq, Category.assoc, h, ← MonoidalCategory.comp_whiskerRight_assoc,
      Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]⟩
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

theorem tensorLeftObj_act_one (X : C) (N : RightMod A) :
    (X ⊗ N.X) ◁ η[A.X] ≫ (α_ X N.X A.X).hom ≫ X ◁ N.act = (ρ_ (X ⊗ N.X)).hom := by
  calc (X ⊗ N.X) ◁ η[A.X] ≫ (α_ X N.X A.X).hom ≫ X ◁ N.act
      = (α_ X N.X (𝟙_ C)).hom ≫ X ◁ (N.X ◁ η[A.X] ≫ N.act) := by monoidal
    _ = (ρ_ (X ⊗ N.X)).hom := by rw [N.act_one]; monoidal

theorem tensorLeftObj_act_assoc (X : C) (N : RightMod A) :
    (X ⊗ N.X) ◁ μ[A.X] ≫ (α_ X N.X A.X).hom ≫ X ◁ N.act =
      (α_ (X ⊗ N.X) A.X A.X).inv ≫ ((α_ X N.X A.X).hom ≫ X ◁ N.act) ▷ A.X ≫
        (α_ X N.X A.X).hom ≫ X ◁ N.act := by
  calc (X ⊗ N.X) ◁ μ[A.X] ≫ (α_ X N.X A.X).hom ≫ X ◁ N.act
      = (α_ X N.X (A.X ⊗ A.X)).hom ≫ X ◁ (N.X ◁ μ[A.X] ≫ N.act) := by monoidal
    _ = (α_ X N.X (A.X ⊗ A.X)).hom ≫
          X ◁ ((α_ N.X A.X A.X).inv ≫ N.act ▷ A.X ≫ N.act) := by rw [N.act_assoc]
    _ = (α_ (X ⊗ N.X) A.X A.X).inv ≫ ((α_ X N.X A.X).hom ≫ X ◁ N.act) ▷ A.X ≫
          (α_ X N.X A.X).hom ≫ X ◁ N.act := by monoidal

/-- The right module `X ⊗ N`, `(x ⊗ n) · a = x ⊗ (n · a)`. -/
def tensorLeftObj (X : C) (N : RightMod A) : RightMod A where
  X := X ⊗ N.X
  act := (α_ X N.X A.X).hom ≫ X ◁ N.act
  act_one := tensorLeftObj_act_one X N
  act_assoc := tensorLeftObj_act_assoc X N

variable (A) in
/-- `X ⊗ (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A` as right modules (the associator). -/
def tensorLeftObjFreeIso (X Y : C) : tensorLeftObj X (free A Y) ≅ free A (X ⊗ Y) :=
  isoOfIso (α_ X Y A.X).symm (by
    show ((α_ X (Y ⊗ A.X) A.X).hom ≫ X ◁ ((α_ Y A.X A.X).hom ≫ Y ◁ μ[A.X])) ≫ (α_ X Y A.X).inv =
      (α_ X Y A.X).inv ▷ A.X ≫ (α_ (X ⊗ Y) A.X A.X).hom ≫ (X ⊗ Y) ◁ μ[A.X]
    monoidal)

end Generic

variable [BraidedCategory C] (A : Mon C) [IsCommMonObj A.X] (X : C) (Q : Bimod A A)

/-- `(x ⊗ a) ⊗ q ↦ x ⊗ a·q`. -/
def freeTensorπ : ((toBimod A).obj (free A X)).X ⊗ Q.X ⟶ X ⊗ Q.X :=
  (α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft

/-- `x ⊗ q ↦ (x ⊗ 1) ⊗ q`. -/
def freeTensorSec : X ⊗ Q.X ⟶ ((toBimod A).obj (free A X)).X ⊗ Q.X :=
  X ◁ ((λ_ Q.X).inv ≫ η[A.X] ▷ Q.X) ≫ (α_ X A.X Q.X).inv

/-- `(x ⊗ a) ⊗ q ↦ ((x ⊗ 1) ⊗ a) ⊗ q`. -/
def freeTensorT :
    ((toBimod A).obj (free A X)).X ⊗ Q.X ⟶ (((toBimod A).obj (free A X)).X ⊗ A.X) ⊗ Q.X :=
  (freeUnit A X ▷ A.X) ▷ Q.X

/-- The cofork condition: `x ⊗ (a b)·q = x ⊗ a·(b·q)` (associativity of the left action). -/
theorem freeTensorπ_condition :
    (((toBimod A).obj (free A X)).actRight ▷ Q.X) ≫ freeTensorπ A X Q =
      ((α_ ((toBimod A).obj (free A X)).X A.X Q.X).hom ≫
        ((toBimod A).obj (free A X)).X ◁ Q.actLeft) ≫ freeTensorπ A X Q := by
  show (((α_ X A.X A.X).hom ≫ X ◁ μ[A.X]) ▷ Q.X) ≫ (α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft =
    ((α_ (X ⊗ A.X) A.X Q.X).hom ≫ (X ⊗ A.X) ◁ Q.actLeft) ≫ (α_ X A.X Q.X).hom ≫
      X ◁ Q.actLeft
  calc (((α_ X A.X A.X).hom ≫ X ◁ μ[A.X]) ▷ Q.X) ≫ (α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft
      = (α_ (X ⊗ A.X) A.X Q.X).hom ≫ (α_ X A.X (A.X ⊗ Q.X)).hom ≫
          X ◁ (α_ A.X A.X Q.X).inv ≫ X ◁ (μ[A.X] ▷ Q.X ≫ Q.actLeft) := by monoidal
    _ = (α_ (X ⊗ A.X) A.X Q.X).hom ≫ (α_ X A.X (A.X ⊗ Q.X)).hom ≫
          X ◁ (α_ A.X A.X Q.X).inv ≫
          X ◁ ((α_ A.X A.X Q.X).hom ≫ A.X ◁ Q.actLeft ≫ Q.actLeft) := by rw [Q.left_assoc]
    _ = ((α_ (X ⊗ A.X) A.X Q.X).hom ≫ (X ⊗ A.X) ◁ Q.actLeft) ≫ (α_ X A.X Q.X).hom ≫
          X ◁ Q.actLeft := by monoidal

/-- `x ⊗ 1·q = x ⊗ q`. -/
theorem freeTensorSec_π : freeTensorSec A X Q ≫ freeTensorπ A X Q = 𝟙 (X ⊗ Q.X) := by
  show (X ◁ ((λ_ Q.X).inv ≫ η[A.X] ▷ Q.X) ≫ (α_ X A.X Q.X).inv) ≫ (α_ X A.X Q.X).hom ≫
    X ◁ Q.actLeft = 𝟙 (X ⊗ Q.X)
  calc (X ◁ ((λ_ Q.X).inv ≫ η[A.X] ▷ Q.X) ≫ (α_ X A.X Q.X).inv) ≫ (α_ X A.X Q.X).hom ≫
        X ◁ Q.actLeft
      = X ◁ ((λ_ Q.X).inv ≫ η[A.X] ▷ Q.X ≫ Q.actLeft) := by monoidal
    _ = 𝟙 (X ⊗ Q.X) := by rw [Q.one_actLeft]; monoidal

/-- `(x ⊗ 1) · a = x ⊗ a`. -/
theorem freeTensorT_f :
    freeTensorT A X Q ≫ ((toBimod A).obj (free A X)).actRight ▷ Q.X =
      𝟙 (((toBimod A).obj (free A X)).X ⊗ Q.X) := by
  show (freeUnit A X ▷ A.X) ▷ Q.X ≫ freeAct A X ▷ Q.X = 𝟙 ((X ⊗ A.X) ⊗ Q.X)
  rw [← MonoidalCategory.comp_whiskerRight, freeUnit_whiskerRight_freeAct,
    MonoidalCategory.id_whiskerRight]

/-- `(x ⊗ 1) ⊗ a·q`, computed in two ways. -/
theorem freeTensorT_g :
    freeTensorT A X Q ≫ (α_ ((toBimod A).obj (free A X)).X A.X Q.X).hom ≫
        ((toBimod A).obj (free A X)).X ◁ Q.actLeft =
      freeTensorπ A X Q ≫ freeTensorSec A X Q := by
  show (freeUnit A X ▷ A.X) ▷ Q.X ≫ (α_ (X ⊗ A.X) A.X Q.X).hom ≫ (X ⊗ A.X) ◁ Q.actLeft =
    ((α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft) ≫ X ◁ ((λ_ Q.X).inv ≫ η[A.X] ▷ Q.X) ≫
      (α_ X A.X Q.X).inv
  rw [MonoidalCategory.associator_naturality_left_assoc, ← MonoidalCategory.whisker_exchange]
  unfold freeUnit
  monoidal

/-- The right-action computation behind `freeTensorXIso_actRight`:
`x ⊗ a·(q·b) = x ⊗ (a·q)·b` (the `middle_assoc` law of `Q`). -/
theorem freeTensor_actRight_core :
    (α_ ((toBimod A).obj (free A X)).X Q.X A.X).hom ≫ ((toBimod A).obj (free A X)).X ◁
        Q.actRight ≫ freeTensorπ A X Q =
      freeTensorπ A X Q ▷ A.X ≫ (α_ X Q.X A.X).hom ≫ X ◁ Q.actRight := by
  show (α_ (X ⊗ A.X) Q.X A.X).hom ≫ (X ⊗ A.X) ◁ Q.actRight ≫ (α_ X A.X Q.X).hom ≫
      X ◁ Q.actLeft =
    ((α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft) ▷ A.X ≫ (α_ X Q.X A.X).hom ≫ X ◁ Q.actRight
  calc (α_ (X ⊗ A.X) Q.X A.X).hom ≫ (X ⊗ A.X) ◁ Q.actRight ≫ (α_ X A.X Q.X).hom ≫
        X ◁ Q.actLeft
      = (α_ X A.X Q.X).hom ▷ A.X ≫ (α_ X (A.X ⊗ Q.X) A.X).hom ≫
          X ◁ ((α_ A.X Q.X A.X).hom ≫ A.X ◁ Q.actRight ≫ Q.actLeft) := by monoidal
    _ = (α_ X A.X Q.X).hom ▷ A.X ≫ (α_ X (A.X ⊗ Q.X) A.X).hom ≫
          X ◁ (Q.actLeft ▷ A.X ≫ Q.actRight) := by rw [Q.middle_assoc]
    _ = ((α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft) ▷ A.X ≫ (α_ X Q.X A.X).hom ≫
          X ◁ Q.actRight := by monoidal

/-- Naturality of `freeTensorπ` in `X`: `f x ⊗ a·q`, computed in two ways. -/
theorem freeTensorπ_whiskerRight {X' : C} (f : X ⟶ X') :
    (f ▷ A.X) ▷ Q.X ≫ freeTensorπ A X' Q = freeTensorπ A X Q ≫ f ▷ Q.X := by
  show (f ▷ A.X) ▷ Q.X ≫ (α_ X' A.X Q.X).hom ≫ X' ◁ Q.actLeft =
    ((α_ X A.X Q.X).hom ≫ X ◁ Q.actLeft) ≫ f ▷ Q.X
  rw [Category.assoc, MonoidalCategory.associator_naturality_left_assoc,
    ← MonoidalCategory.whisker_exchange]

/-- Naturality of `freeTensorπ` in `Q`: `x ⊗ a·φ(q) = x ⊗ φ(a·q)` (left `A`-linearity
of `φ`). -/
theorem freeTensorπ_whiskerLeft {Q₁ Q₂ : Bimod A A} (φ : Q₁ ⟶ Q₂) :
    ((toBimod A).obj (free A X)).X ◁ φ.hom ≫ freeTensorπ A X Q₂ =
      freeTensorπ A X Q₁ ≫ X ◁ φ.hom := by
  show (X ⊗ A.X) ◁ φ.hom ≫ (α_ X A.X Q₂.X).hom ≫ X ◁ Q₂.actLeft =
    ((α_ X A.X Q₁.X).hom ≫ X ◁ Q₁.actLeft) ≫ X ◁ φ.hom
  calc (X ⊗ A.X) ◁ φ.hom ≫ (α_ X A.X Q₂.X).hom ≫ X ◁ Q₂.actLeft
      = (α_ X A.X Q₁.X).hom ≫ X ◁ (A.X ◁ φ.hom ≫ Q₂.actLeft) := by monoidal
    _ = (α_ X A.X Q₁.X).hom ≫ X ◁ (Q₁.actLeft ≫ φ.hom) := by rw [φ.left_act_hom]
    _ = ((α_ X A.X Q₁.X).hom ≫ X ◁ Q₁.actLeft) ≫ X ◁ φ.hom := by monoidal

/-- **The unit isomorphism**: `𝟙 ⊗ A ≅ A` as `A`-bimodules, `A` being the regular
bimodule (the unit for `⊗_A`). -/
def freeUnitIso : (toBimod A).obj (free A (𝟙_ C)) ≅ Bimod.regular A :=
  Bimod.isoOfIso (λ_ A.X)
    (by
      show ((β_ A.X (𝟙_ C ⊗ A.X)).hom ≫ (α_ (𝟙_ C) A.X A.X).hom ≫ 𝟙_ C ◁ μ[A.X]) ≫
          (λ_ A.X).hom = A.X ◁ (λ_ A.X).hom ≫ μ[A.X]
      calc ((β_ A.X (𝟙_ C ⊗ A.X)).hom ≫ (α_ (𝟙_ C) A.X A.X).hom ≫ 𝟙_ C ◁ μ[A.X]) ≫
            (λ_ A.X).hom
          = (β_ A.X (𝟙_ C ⊗ A.X)).hom ≫ (λ_ A.X).hom ▷ A.X ≫ μ[A.X] := by
            simp only [Category.assoc]
            rw [MonoidalCategory.leftUnitor_naturality]
            monoidal
        _ = A.X ◁ (λ_ A.X).hom ≫ (β_ A.X A.X).hom ≫ μ[A.X] := by
            rw [BraidedCategory.braiding_naturality_right_assoc]
        _ = A.X ◁ (λ_ A.X).hom ≫ μ[A.X] := by rw [IsCommMonObj.mul_comm])
    (by
      show ((α_ (𝟙_ C) A.X A.X).hom ≫ 𝟙_ C ◁ μ[A.X]) ≫ (λ_ A.X).hom =
        (λ_ A.X).hom ▷ A.X ≫ μ[A.X]
      rw [Category.assoc, MonoidalCategory.leftUnitor_naturality]
      monoidal)

variable [HasCoequalizers C]

set_option backward.isDefEq.respectTransparency false in
/-- **`(X ⊗ A) ⊗_A Q ≅ X ⊗ Q`** on underlying objects: the cofork `freeTensorπ` is a split
coequalizer. -/
noncomputable def freeTensorXIso :
    Bimod.TensorBimod.X ((toBimod A).obj (free A X)) Q ≅ X ⊗ Q.X where
  hom := coequalizer.desc (freeTensorπ A X Q) (freeTensorπ_condition A X Q)
  inv := freeTensorSec A X Q ≫ coequalizer.π _ _
  hom_inv_id := by
    dsimp only [Bimod.TensorBimod.X]
    apply coequalizer.hom_ext
    rw [coequalizer.π_desc_assoc]
    refine Eq.trans ?_ (Category.comp_id _).symm
    rw [← Category.assoc, ← freeTensorT_g, Category.assoc, ← coequalizer.condition,
      ← Category.assoc, freeTensorT_f, Category.id_comp]
  inv_hom_id := by
    dsimp only [Bimod.TensorBimod.X]
    rw [Category.assoc, coequalizer.π_desc, freeTensorSec_π]

theorem freeTensorXIso_π :
    coequalizer.π (((toBimod A).obj (free A X)).actRight ▷ Q.X)
        ((α_ ((toBimod A).obj (free A X)).X A.X Q.X).hom ≫
          ((toBimod A).obj (free A X)).X ◁ Q.actLeft) ≫ (freeTensorXIso A X Q).hom =
      freeTensorπ A X Q :=
  coequalizer.π_desc _ _

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `freeTensorXIso` intertwines the right actions: `(x ⊗ q) · b = x ⊗ (q · b)`. -/
theorem freeTensorXIso_actRight :
    Bimod.TensorBimod.actRight ((toBimod A).obj (free A X)) Q ≫ (freeTensorXIso A X Q).hom =
      (freeTensorXIso A X Q).hom ▷ A.X ≫ (α_ X Q.X A.X).hom ≫ X ◁ Q.actRight := by
  refine (cancel_epi ((tensorRight A.X).map (coequalizer.π _ _))).1 ?_
  dsimp [Bimod.TensorBimod.X]
  rw [reassoc_of% (Bimod.TensorBimod.π_tensor_id_actRight ((toBimod A).obj (free A X)) Q),
    ← MonoidalCategory.comp_whiskerRight_assoc, freeTensorXIso_π]
  exact freeTensor_actRight_core A X Q

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] (Y : C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `freeTensorXIso` is natural in `X`. -/
theorem freeTensorXIso_whiskerRight {X' : C} (f : X ⟶ X') :
    (Bimod.whiskerRight ((toBimod A).map (freeMap A f)) Q).hom ≫ (freeTensorXIso A X' Q).hom =
      (freeTensorXIso A X Q).hom ≫ f ▷ Q.X := by
  apply coequalizer.hom_ext
  rw [Bimod.whiskerRight_hom]
  try dsimp only [Bimod.tensorBimod_X, Bimod.TensorBimod.X]
  rw [ι_colimMap_assoc, parallelPairHom_app_one, freeTensorXIso_π,
    reassoc_of% (freeTensorXIso_π A X Q)]
  exact freeTensorπ_whiskerRight A X Q f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `freeTensorXIso` is natural in the bimodule `Q`. -/
theorem freeTensorXIso_whiskerLeft {Q₁ Q₂ : Bimod A A} (φ : Q₁ ⟶ Q₂) :
    (Bimod.whiskerLeft ((toBimod A).obj (free A X)) φ).hom ≫ (freeTensorXIso A X Q₂).hom =
      (freeTensorXIso A X Q₁).hom ≫ X ◁ φ.hom := by
  apply coequalizer.hom_ext
  rw [Bimod.whiskerLeft_hom]
  try dsimp only [Bimod.tensorBimod_X, Bimod.TensorBimod.X]
  rw [ι_colimMap_assoc, parallelPairHom_app_one, freeTensorXIso_π,
    reassoc_of% (freeTensorXIso_π A X Q₁)]
  exact freeTensorπ_whiskerLeft A X φ

/-- The right module underlying the relative tensor product `(X ⊗ A) ⊗_A (Y ⊗ A)`. -/
noncomputable def freeTensorRightMod : RightMod A :=
  ⟨(((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).X,
    (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).actRight,
    (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).actRight_one,
    (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).right_assoc⟩

/-- As right modules, `(X ⊗ A) ⊗_A (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A`. -/
noncomputable def freeTensorRightModIso : freeTensorRightMod A X Y ≅ free A (X ⊗ Y) :=
  (isoOfIso (M := freeTensorRightMod A X Y)
      (N := tensorLeftObj X (free A Y))
      (freeTensorXIso A X ((toBimod A).obj (free A Y)))
      (freeTensorXIso_actRight A X ((toBimod A).obj (free A Y)))) ≪≫
    tensorLeftObjFreeIso A X Y

/-- On underlying objects, the isomorphism is induced by
`(x ⊗ a) ⊗ (y ⊗ b) ↦ x ⊗ a·(y ⊗ b) = x ⊗ (y ⊗ ba)` (the left action of `Y ⊗ A` goes through
the braiding `c_{A, Y ⊗ A}`, `toBimod`), followed by the associator. -/
theorem freeTensorRightModIso_hom_hom :
    (freeTensorRightModIso A X Y).hom.hom =
      (freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ (α_ X Y A.X).inv :=
  rfl

/-- The underlying isomorphism `(X ⊗ A) ⊗_A (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A` of objects of `C`. -/
noncomputable def freeTensorObjIso :
    (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).X ≅
      ((toBimod A).obj (free A (X ⊗ Y))).X :=
  freeTensorXIso A X ((toBimod A).obj (free A Y)) ≪≫ (α_ X Y A.X).symm

theorem freeTensorObjIso_actRight :
    (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).actRight ≫
        (freeTensorObjIso A X Y).hom =
      (freeTensorObjIso A X Y).hom ▷ A.X ≫ ((toBimod A).obj (free A (X ⊗ Y))).actRight :=
  (freeTensorRightModIso A X Y).hom.act_hom

/-- The left actions agree: both satisfy `actLeft = c_{A,-} ≫ actRight`. -/
theorem freeTensorObjIso_actLeft :
    (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).actLeft ≫
        (freeTensorObjIso A X Y).hom =
      A.X ◁ (freeTensorObjIso A X Y).hom ≫ ((toBimod A).obj (free A (X ⊗ Y))).actLeft := by
  have h1 : (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).actLeft =
      (β_ A.X (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).X).hom ≫
        (((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y))).actRight :=
    tensorBimod_relation A (toBimod_obj_actLeft A (free A X)) (toBimod_obj_actLeft A (free A Y))
  have h2 : ((toBimod A).obj (free A (X ⊗ Y))).actLeft =
      (β_ A.X ((toBimod A).obj (free A (X ⊗ Y))).X).hom ≫
        ((toBimod A).obj (free A (X ⊗ Y))).actRight :=
    toBimod_obj_actLeft A (free A (X ⊗ Y))
  rw [h1, h2, Category.assoc, freeTensorObjIso_actRight,
    BraidedCategory.braiding_naturality_right_assoc]

/-- **Free induction carries `⊗` to `⊗_A`** (manuscript lines 3337–3338): for a commutative
algebra `A` in a braided category, `(X ⊗ A) ⊗_A (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A` as `A`-bimodules. -/
noncomputable def freeTensorIso :
    ((toBimod A).obj (free A X)).tensorBimod ((toBimod A).obj (free A Y)) ≅
      (toBimod A).obj (free A (X ⊗ Y)) :=
  Bimod.isoOfIso (freeTensorObjIso A X Y) (freeTensorObjIso_actLeft A X Y)
    (freeTensorObjIso_actRight A X Y)

theorem freeTensorIso_hom_hom :
    (freeTensorIso A X Y).hom.hom =
      (freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ (α_ X Y A.X).inv :=
  rfl

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.isoOfIso
#print axioms HaagerupIzumi.C8.RightMod.tensorLeftObjFreeIso
#print axioms HaagerupIzumi.C8.RightMod.freeTensorXIso
#print axioms HaagerupIzumi.C8.RightMod.freeTensorXIso_actRight
#print axioms HaagerupIzumi.C8.RightMod.freeTensorRightModIso
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso
#print axioms HaagerupIzumi.C8.RightMod.freeTensorRightModIso_hom_hom
#print axioms HaagerupIzumi.C8.RightMod.freeTensorXIso_whiskerRight
#print axioms HaagerupIzumi.C8.RightMod.freeTensorXIso_whiskerLeft
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso_hom_hom
#print axioms HaagerupIzumi.C8.RightMod.freeUnitIso
