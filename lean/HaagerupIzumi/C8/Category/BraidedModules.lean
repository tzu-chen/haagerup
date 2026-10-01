module

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.EssentialImage

@[expose] public section

/-! # Right modules over a commutative algebra object are bimodules

This file formalizes the algebraic core of the first paragraph of the proof of
Lemma `lem:analytic-unitary-all-modules` (manuscript `haagerup_c8_expanded.tex`,
lines 4900–4934).

Let `C` be a braided monoidal category, `A` a commutative monoid (algebra) object of `C`
(`MonObj A` with `IsCommMonObj A`), and `r : X ⊗ A ⟶ X` a right action of `A` on `X`,
with unit and associativity axioms written exactly as the right-action axioms of Mathlib's
`Bimod`.  As in the manuscript we start from the right action and put
`l := (β_ A X).hom ≫ r`, i.e. `l = r ∘ c_{A,X}`.

* `braidedLeftAct_one`, `braidedLeftAct_assoc`: `l` is a unital associative left action.
  Associativity uses the commutativity of `A` and the hexagon identities (through
  `braiding_tensor_left_hom` and `braiding_tensor_right_hom`).
* `braidedLeftAct_middle_assoc`: the two actions commute,
  `(l ▷ A) ≫ r = (α_ A X A).hom ≫ (A ◁ r) ≫ l` (commutativity and a hexagon).
* `braidedLeftAct_hom`: every right-module morphism intertwines the induced left actions
  (naturality of the braiding only).
* `bimodOfRightAct`, `bimodHomOfRightActHom`: the resulting object of Mathlib's
  `Bimod A A` and the bimodule morphisms; `modObjOfRightAct` and `isModHom_of_rightActHom`
  give the same for Mathlib's (left) module objects `ModObj`.
* `RightMod A` (the category `𝒞_A`), the functor `toBimod A : RightMod A ⥤ Bimod A A`,
  `toBimodFullyFaithful`, `toBimod_obj_actLeft` and `toBimod_obj_of_relation`: `𝒞_A` is
  realized as the full subcategory of `A`-bimodules whose left action is
  `(β_ A X).hom ≫ actRight`.
* `IsLocalRightAct`, `isLocalRightAct_iff`: the locality (monodromy) condition
  `r ∘ c_{A,X} ∘ c_{X,A} = r`; it holds iff the left actions built from the two braiding
  orientations, `c_{A,X}` and `c_{X,A}⁻¹`, agree.  Locality is not assumed anywhere else.

No hypothesis beyond the braided monoidal structure and the commutativity of `A` is used;
there are no external-theorem or certificate inputs in this file.  Not formalized here:
the relative tensor product and the closure of the subcategory under it, sums and
summands, Gui's unitarizability theorem [Gui, Thm. 2.28] and unitary relative tensor
product [Gui, Thm. 3.13], semisimplicity, rigidity and finiteness (second and third
paragraphs of the manuscript's proof). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section RightModules

/-- A right module object over a monoid object `A`: an object of the category `𝒞_A` of the
manuscript.  The axioms are the right-action axioms of Mathlib's `Bimod`. -/
structure RightMod (A : Mon C) where
  /-- The underlying object. -/
  X : C
  /-- The right action `r : X ⊗ A ⟶ X`. -/
  act : X ⊗ A.X ⟶ X
  act_one : X ◁ η ≫ act = (ρ_ X).hom
  act_assoc : X ◁ μ ≫ act = (α_ X A.X A.X).inv ≫ act ▷ A.X ≫ act

namespace RightMod

variable {A : Mon C}

/-- Morphisms of right module objects. -/
@[ext]
structure Hom (M N : RightMod A) where
  /-- The underlying morphism. -/
  hom : M.X ⟶ N.X
  act_hom : M.act ≫ hom = hom ▷ A.X ≫ N.act

/-- The identity morphism of a right module object. -/
def Hom.id (M : RightMod A) : Hom M M :=
  ⟨𝟙 M.X, by rw [Category.comp_id, MonoidalCategory.id_whiskerRight, Category.id_comp]⟩

/-- Composition of morphisms of right module objects. -/
def Hom.comp {M N P : RightMod A} (f : Hom M N) (g : Hom N P) : Hom M P :=
  ⟨f.hom ≫ g.hom, by
    rw [reassoc_of% f.act_hom, g.act_hom, MonoidalCategory.comp_whiskerRight_assoc]⟩

instance : Category (RightMod A) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

end RightMod

end RightModules

variable [BraidedCategory C]

section Core

variable {A X : C}

/-- The left action induced by the braiding from a right action `r : X ⊗ A ⟶ X`:
`l = r ∘ c_{A,X}` (manuscript, proof of `lem:analytic-unitary-all-modules`). -/
def braidedLeftAct (r : X ⊗ A ⟶ X) : A ⊗ X ⟶ X := (β_ A X).hom ≫ r

theorem braidedLeftAct_def (r : X ⊗ A ⟶ X) : braidedLeftAct r = (β_ A X).hom ≫ r := rfl

/-- (a) Unit axiom for the induced left action. -/
theorem braidedLeftAct_one [MonObj A] (r : X ⊗ A ⟶ X) (h_one : X ◁ η ≫ r = (ρ_ X).hom) :
    η ▷ X ≫ braidedLeftAct r = (λ_ X).hom := by
  rw [braidedLeftAct_def, BraidedCategory.braiding_naturality_left_assoc, h_one,
    CategoryTheory.braiding_rightUnitor]

/-- The point where commutativity enters: exchanging the two `A`-factors does not change
the iterated right action. -/
theorem rightAct_braid [MonObj A] [IsCommMonObj A] (r : X ⊗ A ⟶ X)
    (h_assoc : X ◁ μ ≫ r = (α_ X A A).inv ≫ r ▷ A ≫ r) :
    (α_ X A A).hom ≫ X ◁ (β_ A A).hom ≫ (α_ X A A).inv ≫ r ▷ A ≫ r = r ▷ A ≫ r := by
  rw [← h_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, IsCommMonObj.mul_comm A, h_assoc,
    Iso.hom_inv_id_assoc]

/-- (a) Associativity of the induced left action.  Uses the commutativity of `A` and the
hexagon identities (as `braiding_tensor_left_hom`, `braiding_tensor_right_hom`). -/
theorem braidedLeftAct_assoc [MonObj A] [IsCommMonObj A] (r : X ⊗ A ⟶ X)
    (h_assoc : X ◁ μ ≫ r = (α_ X A A).inv ≫ r ▷ A ≫ r) :
    μ ▷ X ≫ braidedLeftAct r =
      (α_ A A X).hom ≫ A ◁ braidedLeftAct r ≫ braidedLeftAct r := by
  simp only [braidedLeftAct_def]
  rw [BraidedCategory.braiding_naturality_left_assoc, h_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, rightAct_braid r h_assoc]

/-- (b) The induced left action commutes with the right action (the `middle_assoc` axiom of
Mathlib's `Bimod`).  Uses the commutativity of `A` and a hexagon identity. -/
theorem braidedLeftAct_middle_assoc [MonObj A] [IsCommMonObj A] (r : X ⊗ A ⟶ X)
    (h_assoc : X ◁ μ ≫ r = (α_ X A A).inv ≫ r ▷ A ≫ r) :
    braidedLeftAct r ▷ A ≫ r = (α_ A X A).hom ≫ A ◁ r ≫ braidedLeftAct r := by
  simp only [braidedLeftAct_def]
  rw [MonoidalCategory.comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, rightAct_braid r h_assoc]

/-- (c) Naturality of the braiding: a morphism intertwining right actions intertwines the
induced left actions. -/
theorem braidedLeftAct_hom {Y : C} (r : X ⊗ A ⟶ X) (s : Y ⊗ A ⟶ Y) (f : X ⟶ Y)
    (hf : r ≫ f = f ▷ A ≫ s) :
    braidedLeftAct r ≫ f = A ◁ f ≫ braidedLeftAct s := by
  rw [braidedLeftAct_def, braidedLeftAct_def, Category.assoc, hf,
    BraidedCategory.braiding_naturality_right_assoc]

/-- (d) Locality of a right action: the monodromy condition `r ∘ c_{A,X} ∘ c_{X,A} = r`. -/
def IsLocalRightAct (r : X ⊗ A ⟶ X) : Prop := (β_ X A).hom ≫ (β_ A X).hom ≫ r = r

/-- (d) A right action is local iff the left actions induced by the two braiding
orientations, `r ∘ c_{A,X}` and `r ∘ c_{X,A}⁻¹`, agree. -/
theorem isLocalRightAct_iff (r : X ⊗ A ⟶ X) :
    IsLocalRightAct r ↔ braidedLeftAct r = (β_ X A).inv ≫ r := by
  unfold IsLocalRightAct
  rw [braidedLeftAct_def]
  constructor
  · intro h
    calc (β_ A X).hom ≫ r = (β_ X A).inv ≫ (β_ X A).hom ≫ (β_ A X).hom ≫ r := by
          rw [Iso.inv_hom_id_assoc]
      _ = (β_ X A).inv ≫ r := by rw [h]
  · intro h
    rw [h, Iso.hom_inv_id_assoc]

/-- The induced left action as a module object in Mathlib's sense (`ModObj`, a left
action). -/
@[instance_reducible]
def modObjOfRightAct [MonObj A] [IsCommMonObj A] (r : X ⊗ A ⟶ X)
    (h_one : X ◁ η ≫ r = (ρ_ X).hom)
    (h_assoc : X ◁ μ ≫ r = (α_ X A A).inv ≫ r ▷ A ≫ r) : ModObj A X where
  smul := braidedLeftAct r
  one_smul := braidedLeftAct_one r h_one
  mul_smul := braidedLeftAct_assoc r h_assoc

/-- (c) for Mathlib's `ModObj`: right-module morphisms are module morphisms for the induced
left actions. -/
theorem isModHom_of_rightActHom [MonObj A] [IsCommMonObj A] {Y : C}
    (r : X ⊗ A ⟶ X) (hr₁ : X ◁ η ≫ r = (ρ_ X).hom)
    (hr₂ : X ◁ μ ≫ r = (α_ X A A).inv ≫ r ▷ A ≫ r)
    (s : Y ⊗ A ⟶ Y) (hs₁ : Y ◁ η ≫ s = (ρ_ Y).hom)
    (hs₂ : Y ◁ μ ≫ s = (α_ Y A A).inv ≫ s ▷ A ≫ s)
    (f : X ⟶ Y) (hf : r ≫ f = f ▷ A ≫ s) :
    letI := modObjOfRightAct r hr₁ hr₂
    letI := modObjOfRightAct s hs₁ hs₂
    IsModHom A f :=
  letI := modObjOfRightAct r hr₁ hr₂
  letI := modObjOfRightAct s hs₁ hs₂
  ⟨braidedLeftAct_hom r s f hf⟩

end Core

section Bimodules

/-- A right module over a commutative monoid object `A` is an `A`-`A`-bimodule (Mathlib's
`Bimod`), with right action `r` and left action `l = r ∘ c_{A,X}`. -/
def bimodOfRightAct (A : Mon C) [IsCommMonObj A.X] (X : C) (r : X ⊗ A.X ⟶ X)
    (h_one : X ◁ η ≫ r = (ρ_ X).hom)
    (h_assoc : X ◁ μ ≫ r = (α_ X A.X A.X).inv ≫ r ▷ A.X ≫ r) : Bimod A A where
  X := X
  actLeft := braidedLeftAct r
  one_actLeft := braidedLeftAct_one r h_one
  left_assoc := braidedLeftAct_assoc r h_assoc
  actRight := r
  actRight_one := h_one
  right_assoc := h_assoc
  middle_assoc := braidedLeftAct_middle_assoc r h_assoc

/-- (c) A right-module morphism is a morphism of the associated bimodules. -/
def bimodHomOfRightActHom (A : Mon C) [IsCommMonObj A.X] {X Y : C}
    (r : X ⊗ A.X ⟶ X) (hr₁ : X ◁ η ≫ r = (ρ_ X).hom)
    (hr₂ : X ◁ μ ≫ r = (α_ X A.X A.X).inv ≫ r ▷ A.X ≫ r)
    (s : Y ⊗ A.X ⟶ Y) (hs₁ : Y ◁ η ≫ s = (ρ_ Y).hom)
    (hs₂ : Y ◁ μ ≫ s = (α_ Y A.X A.X).inv ≫ s ▷ A.X ≫ s)
    (f : X ⟶ Y) (hf : r ≫ f = f ▷ A.X ≫ s) :
    Bimod.Hom (bimodOfRightAct A X r hr₁ hr₂) (bimodOfRightAct A Y s hs₁ hs₂) where
  hom := f
  left_act_hom := braidedLeftAct_hom r s f hf
  right_act_hom := hf

/-- The functor `𝒞_A ⥤ Bimod A A` (identity on underlying objects and morphisms). -/
def toBimod (A : Mon C) [IsCommMonObj A.X] : RightMod A ⥤ Bimod A A where
  obj M := bimodOfRightAct A M.X M.act M.act_one M.act_assoc
  map {M N} f := bimodHomOfRightActHom A M.act M.act_one M.act_assoc N.act N.act_one
    N.act_assoc f.hom f.act_hom
  map_id _ := Bimod.hom_ext _ _ rfl
  map_comp _ _ := Bimod.hom_ext _ _ rfl

/-- `toBimod` is fully faithful: the bimodule morphisms between such bimodules are exactly
the right-module morphisms. -/
def toBimodFullyFaithful (A : Mon C) [IsCommMonObj A.X] : (toBimod A).FullyFaithful where
  preimage f := ⟨f.hom, f.right_act_hom⟩
  map_preimage _ := Bimod.hom_ext _ _ rfl
  preimage_map _ := RightMod.Hom.ext rfl

/-- Every bimodule in the image of `toBimod` satisfies `actLeft = c_{A,X} ≫ actRight`. -/
theorem toBimod_obj_actLeft (A : Mon C) [IsCommMonObj A.X] (M : RightMod A) :
    ((toBimod A).obj M).actLeft = (β_ A.X M.X).hom ≫ ((toBimod A).obj M).actRight :=
  rfl

/-- Conversely, every `A`-bimodule with `actLeft = c_{A,X} ≫ actRight` is the image of its
underlying right module, so the image of `toBimod` is exactly the full subcategory of
bimodules satisfying this relation. -/
theorem toBimod_obj_of_relation (A : Mon C) [IsCommMonObj A.X] (B : Bimod A A)
    (hB : B.actLeft = (β_ A.X B.X).hom ≫ B.actRight) :
    (toBimod A).obj ⟨B.X, B.actRight, B.actRight_one, B.right_assoc⟩ = B := by
  cases B
  dsimp only at hB
  subst hB
  rfl

/-- The relation `actLeft = c_{A,X} ≫ actRight` is transported along isomorphisms of
bimodules (manuscript: "an isomorphism transporting the actions preserves the displayed
relation"). -/
theorem relation_of_iso (A : Mon C) {B B' : Bimod A A} (e : B ≅ B')
    (hB : B.actLeft = (β_ A.X B.X).hom ≫ B.actRight) :
    B'.actLeft = (β_ A.X B'.X).hom ≫ B'.actRight := by
  have h₁ : e.hom.hom ≫ e.inv.hom = 𝟙 B.X := congrArg Bimod.Hom.hom e.hom_inv_id
  have h₂ : e.inv.hom ≫ e.hom.hom = 𝟙 B'.X := congrArg Bimod.Hom.hom e.inv_hom_id
  have : IsIso e.hom.hom := ⟨⟨e.inv.hom, h₁, h₂⟩⟩
  have key := braidedLeftAct_hom B.actRight B'.actRight e.hom.hom e.hom.right_act_hom
  rw [braidedLeftAct_def, braidedLeftAct_def, ← hB, e.hom.left_act_hom] at key
  exact (cancel_epi (A.X ◁ e.hom.hom)).mp key

/-- The essential image of `toBimod` is exactly the class of `A`-bimodules whose left action
is `c_{A,X} ≫ actRight`: `𝒞_A` is realized as this full subcategory of bimodules. -/
theorem mem_essImage_toBimod_iff (A : Mon C) [IsCommMonObj A.X] (B : Bimod A A) :
    (toBimod A).essImage B ↔ B.actLeft = (β_ A.X B.X).hom ≫ B.actRight := by
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    exact relation_of_iso A e (toBimod_obj_actLeft A M)
  · intro hB
    exact ⟨⟨B.X, B.actRight, B.actRight_one, B.right_assoc⟩,
      ⟨eqToIso (toBimod_obj_of_relation A B hB)⟩⟩

end Bimodules

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.braidedLeftAct_one
#print axioms HaagerupIzumi.C8.braidedLeftAct_assoc
#print axioms HaagerupIzumi.C8.braidedLeftAct_middle_assoc
#print axioms HaagerupIzumi.C8.braidedLeftAct_hom
#print axioms HaagerupIzumi.C8.isLocalRightAct_iff
#print axioms HaagerupIzumi.C8.isModHom_of_rightActHom
#print axioms HaagerupIzumi.C8.bimodOfRightAct
#print axioms HaagerupIzumi.C8.bimodHomOfRightActHom
#print axioms HaagerupIzumi.C8.toBimod
#print axioms HaagerupIzumi.C8.toBimodFullyFaithful
#print axioms HaagerupIzumi.C8.toBimod_obj_of_relation
#print axioms HaagerupIzumi.C8.relation_of_iso
#print axioms HaagerupIzumi.C8.mem_essImage_toBimod_iff
