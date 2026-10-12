module

public import HaagerupIzumi.C8.Category.GradedMat
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

/-! # The untwisted symmetric monoidal category of graded matrices, directly

`GradedMat.lean` obtains the coherence axioms of the standard monoidal structure on
`GrMat M 𝕜` by inducing them along a faithful realization.  Here they are proved directly, by
matrix algebra (Kronecker products and permutation matrices), so that

* `GrMat.instMonoidalCategory`: `GrMat M 𝕜` is a monoidal category (for any commutative
  semiring `𝕜` and commutative monoid `M`), with tensor product the Kronecker product on index
  pairs and structure maps the permutation matrices of `Equiv.prodAssoc`, `Equiv.uniqueProd`,
  `Equiv.prodUnique`;
* `GrMat.instSymmetricCategory`: with the swap braiding (`Equiv.prodComm`) it is symmetric
  monoidal: the untwisted `Vec_M` (trivial associator and symmetric braiding).

`monoidal_eq`: the induced monoidal structure of `GradedMat.lean` is this instance (by `rfl`).
The induced braiding `GrMat.braided` is definitionally the canonical one: its braiding is
`braidIso` (`GrMat.braided_braiding`).  So `Lminus_vec_braided_equivalence` restates the
comparison with the canonical instances.  No external-theorem or certificate inputs beyond those of the restated theorem. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Limits Module Matrix

universe v u

namespace GrMat

variable {M 𝕜 : Type}

section Perm

variable [Semiring 𝕜]

theorem perm_mul_apply {α β γ : Type} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (A : Matrix β γ 𝕜) (i : α) (k : γ) : ((perm e : Matrix α β 𝕜) * A) i k = A (e i) k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
  · rw [perm_apply, if_pos rfl, one_mul]
  · intro j _ hj
    rw [perm_apply, if_neg (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_perm_apply {α β γ : Type} [Fintype β] [DecidableEq γ] (A : Matrix α β 𝕜)
    (e : β ≃ γ) (i : α) (k : γ) : (A * (perm e : Matrix β γ 𝕜)) i k = A i (e.symm k) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm k)]
  · rw [perm_apply, Equiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro j _ hj
    rw [perm_apply, if_neg (fun h => hj (by rw [← h, Equiv.symm_apply_apply])), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem perm_kron_one {α β γ : Type} [DecidableEq β] [DecidableEq γ] (e : α ≃ β) :
    kroneckerMap (· * ·) (perm e : Matrix α β 𝕜) (1 : Matrix γ γ 𝕜) =
      perm (Equiv.prodCongr e (Equiv.refl γ)) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  by_cases h1 : e i = i' <;> by_cases h2 : j = j' <;>
    simp [perm_apply, kroneckerMap_apply, h1, h2]

theorem one_kron_perm {α β γ : Type} [DecidableEq β] [DecidableEq γ] (e : α ≃ β) :
    kroneckerMap (· * ·) (1 : Matrix γ γ 𝕜) (perm e : Matrix α β 𝕜) =
      perm (Equiv.prodCongr (Equiv.refl γ) e) := by
  ext ⟨j, i⟩ ⟨j', i'⟩
  by_cases h1 : e i = i' <;> by_cases h2 : j = j' <;>
    simp [perm_apply, kroneckerMap_apply, h1, h2]

end Perm

variable [CommSemiring 𝕜] [CommMonoid M]

section Mats

variable {X Y Z X₁ X₂ Y₁ Y₂ : GrMat M 𝕜}

theorem tensorHom_mat_kron (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    Hom.mat (f ⊗ₘ g) = kroneckerMap (· * ·) (Hom.mat f) (Hom.mat g) := rfl

theorem whiskerLeft_mat (X : GrMat M 𝕜) (g : Y₁ ⟶ Y₂) :
    Hom.mat (X ◁ g) = kroneckerMap (· * ·) (1 : Matrix X.I X.I 𝕜) (Hom.mat g) := rfl

theorem whiskerRight_mat (f : X₁ ⟶ X₂) (Y : GrMat M 𝕜) :
    Hom.mat (f ▷ Y) = kroneckerMap (· * ·) (Hom.mat f) (1 : Matrix Y.I Y.I 𝕜) := rfl

theorem associator_hom_mat (X Y Z : GrMat M 𝕜) :
    Hom.mat (α_ X Y Z).hom = perm (Equiv.prodAssoc X.I Y.I Z.I) := rfl

theorem associator_inv_mat (X Y Z : GrMat M 𝕜) :
    Hom.mat (α_ X Y Z).inv = perm (Equiv.prodAssoc X.I Y.I Z.I).symm := rfl

theorem leftUnitor_hom_mat (X : GrMat M 𝕜) :
    Hom.mat (λ_ X).hom = perm (Equiv.uniqueProd X.I Unit) := rfl

theorem rightUnitor_hom_mat (X : GrMat M 𝕜) :
    Hom.mat (ρ_ X).hom = perm (Equiv.prodUnique X.I Unit) := rfl

theorem braidIso_hom_mat (X Y : GrMat M 𝕜) :
    Hom.mat (braidIso X Y).hom = perm (Equiv.prodComm X.I Y.I) := rfl

theorem braidIso_inv_mat (X Y : GrMat M 𝕜) :
    Hom.mat (braidIso X Y).inv = perm (Equiv.prodComm X.I Y.I).symm := rfl

end Mats

section Axioms

variable {X Y Z W X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : GrMat M 𝕜}

theorem tensorHom_def_aux (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f ⊗ₘ g = f ▷ X₂ ≫ Y₁ ◁ g := by
  apply hom_ext
  rw [comp_mat, whiskerRight_mat, whiskerLeft_mat, tensorHom_mat_kron, ← mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

theorem id_tensorHom_id_aux (X Y : GrMat M 𝕜) : 𝟙 X ⊗ₘ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  apply hom_ext
  rw [tensorHom_mat_kron, id_mat, id_mat, id_mat, one_kronecker_one]

theorem tensorHom_comp_tensorHom_aux (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  apply hom_ext
  rw [comp_mat, tensorHom_mat_kron, tensorHom_mat_kron, tensorHom_mat_kron,
    ← mul_kronecker_mul, comp_mat, comp_mat]

theorem whiskerLeft_id_aux (X Y : GrMat M 𝕜) : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  apply hom_ext
  rw [whiskerLeft_mat, id_mat, id_mat, one_kronecker_one]

theorem id_whiskerRight_aux (X Y : GrMat M 𝕜) : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  apply hom_ext
  rw [whiskerRight_mat, id_mat, id_mat, one_kronecker_one]

theorem associator_naturality_aux (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  apply hom_ext
  rw [comp_mat, comp_mat, associator_hom_mat, associator_hom_mat, tensorHom_mat_kron,
    tensorHom_mat_kron, tensorHom_mat_kron, tensorHom_mat_kron]
  ext p q
  rcases p with ⟨⟨i, j⟩, k⟩
  rcases q with ⟨i', ⟨j', k'⟩⟩
  rw [mul_perm_apply, perm_mul_apply]
  show Hom.mat f₁ i i' * Hom.mat f₂ j j' * Hom.mat f₃ k k' =
    Hom.mat f₁ i i' * (Hom.mat f₂ j j' * Hom.mat f₃ k k')
  rw [mul_assoc]

theorem leftUnitor_naturality_aux (f : X ⟶ Y) : 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  apply hom_ext
  rw [comp_mat, comp_mat, leftUnitor_hom_mat, leftUnitor_hom_mat, whiskerLeft_mat]
  ext p j
  rcases p with ⟨⟨⟩, i⟩
  rw [mul_perm_apply, perm_mul_apply]
  simp [kroneckerMap_apply]

theorem rightUnitor_naturality_aux (f : X ⟶ Y) : f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  apply hom_ext
  rw [comp_mat, comp_mat, rightUnitor_hom_mat, rightUnitor_hom_mat, whiskerRight_mat]
  ext p j
  rcases p with ⟨i, ⟨⟩⟩
  rw [mul_perm_apply, perm_mul_apply]
  simp [kroneckerMap_apply]

theorem pentagon_aux (W X Y Z : GrMat M 𝕜) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  apply hom_ext
  simp only [comp_mat, whiskerRight_mat, whiskerLeft_mat, associator_hom_mat, perm_kron_one,
    one_kron_perm, perm_mul_perm]
  congr 1

theorem triangle_aux (X Y : GrMat M 𝕜) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  apply hom_ext
  simp only [comp_mat, whiskerRight_mat, whiskerLeft_mat, associator_hom_mat,
    leftUnitor_hom_mat, rightUnitor_hom_mat, perm_kron_one, one_kron_perm, perm_mul_perm]
  congr 1

end Axioms

/-- **The monoidal category of graded matrices** (Kronecker product on index pairs, standard
permutation-matrix structure maps). -/
instance instMonoidalCategory : MonoidalCategory (GrMat M 𝕜) where
  tensorHom_def := tensorHom_def_aux
  id_tensorHom_id := id_tensorHom_id_aux
  tensorHom_comp_tensorHom := tensorHom_comp_tensorHom_aux
  whiskerLeft_id := whiskerLeft_id_aux
  id_whiskerRight := id_whiskerRight_aux
  associator_naturality := associator_naturality_aux
  leftUnitor_naturality := leftUnitor_naturality_aux
  rightUnitor_naturality := rightUnitor_naturality_aux
  pentagon := pentagon_aux
  triangle := triangle_aux

section BraidAxioms

variable {X Y Z : GrMat M 𝕜}

theorem braiding_naturality_right_aux (X : GrMat M 𝕜) (g : Y ⟶ Z) :
    X ◁ g ≫ (braidIso X Z).hom = (braidIso X Y).hom ≫ g ▷ X := by
  apply hom_ext
  rw [comp_mat, comp_mat, braidIso_hom_mat, braidIso_hom_mat, whiskerLeft_mat, whiskerRight_mat]
  ext p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, i'⟩
  rw [mul_perm_apply, perm_mul_apply]
  simp [kroneckerMap_apply, mul_comm]

theorem braiding_naturality_left_aux (f : X ⟶ Y) (Z : GrMat M 𝕜) :
    f ▷ Z ≫ (braidIso Y Z).hom = (braidIso X Z).hom ≫ Z ◁ f := by
  apply hom_ext
  rw [comp_mat, comp_mat, braidIso_hom_mat, braidIso_hom_mat, whiskerLeft_mat, whiskerRight_mat]
  ext p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, i'⟩
  rw [mul_perm_apply, perm_mul_apply]
  simp [kroneckerMap_apply, mul_comm]

theorem hexagon_forward_aux (X Y Z : GrMat M 𝕜) :
    (α_ X Y Z).hom ≫ (braidIso X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((braidIso X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braidIso X Z).hom) := by
  apply hom_ext
  simp only [comp_mat, whiskerRight_mat, whiskerLeft_mat, associator_hom_mat,
    braidIso_hom_mat, perm_kron_one, one_kron_perm, perm_mul_perm]
  congr 1

theorem hexagon_reverse_aux (X Y Z : GrMat M 𝕜) :
    (α_ X Y Z).inv ≫ (braidIso (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (braidIso Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braidIso X Z).hom ▷ Y) := by
  apply hom_ext
  simp only [comp_mat, whiskerRight_mat, whiskerLeft_mat, associator_inv_mat,
    braidIso_hom_mat, perm_kron_one, one_kron_perm, perm_mul_perm]
  congr 1

end BraidAxioms

/-- **The untwisted symmetric structure**: the swap braiding. -/
instance instSymmetricCategory : SymmetricCategory (GrMat M 𝕜) where
  braiding := braidIso
  braiding_naturality_right X _ _ g := braiding_naturality_right_aux X g
  braiding_naturality_left := braiding_naturality_left_aux
  hexagon_forward := hexagon_forward_aux
  hexagon_reverse := hexagon_reverse_aux
  symmetry X Y := braidIso_symm X Y

section Canonical

variable {𝕜' : Type} [Field 𝕜'] [DecidableEq M]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [Linear 𝕜' C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜' C]

/-- The monoidal structure induced along a faithful realization is the canonical one. -/
theorem monoidal_eq (G : Discrete M ⥤ C) [G.Monoidal]
    [∀ a b : M, FiniteDimensional 𝕜' (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩)]
    (hG : ∀ a b : M, finrank 𝕜' (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0) :
    monoidal G hG = (instMonoidalCategory : MonoidalCategory (GrMat M 𝕜')) := rfl

/-- **The realization is a braided monoidal functor for the canonical untwisted symmetric
structure of `GrMat M 𝕜`**, for any braided `G : Discrete M ⥤ C` whose lines satisfy the
Schur condition. -/
@[instance_reducible]
noncomputable def realBraidedCanonical [BraidedCategory C] (G : Discrete M ⥤ C) [G.Braided]
    [∀ a b : M, FiniteDimensional 𝕜' (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩)]
    (hG : ∀ a b : M, finrank 𝕜' (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0) :
    (real G : GrMat M 𝕜' ⥤ C).Braided :=
  realBraided G hG

end Canonical

end GrMat

section Lminus

open GrMat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type) [Field 𝕜]
  [Linear 𝕜 C] [MonoidalLinear 𝕜 C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]

/-- **`Vec_{ℤ/3}` (untwisted, symmetric) is braided monoidally equivalent to the additive
closure of `L₋`.**  Under `hSchur`, `hfusion`, `hunitS` and **[external]** `hθ`: there is a
functor `G : Discrete (ℤ/3) ⥤ C` with `G (a) = S (a, -a)` such that the realization
`X ↦ ⨁_{i ∈ X.I} G (deg i)` of graded matrices lifts to a functor
`GrMat (ℤ/3) 𝕜 ⥤ LminusClosure S` which is **braided monoidal** (source: the canonical
`instMonoidalCategory` / `instSymmetricCategory`, i.e. Kronecker tensor product, trivial
associator and swap braiding; target: `lminusClosure_isMonoidal` with the inherited braiding)
and **an equivalence of categories**. -/
theorem Lminus_vec_braided_equivalence (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) :
    haveI := RightMod.lminusClosure_isMonoidal hfusion hunitS
    ∃ (G : Discrete (Multiplicative (ZMod 3)) ⥤ C)
      (hmem : ∀ X : GrMat (Multiplicative (ZMod 3)) 𝕜,
        RightMod.LminusClosure S ((real G).obj X)),
      (∀ a : ZMod 3, G.obj ⟨Multiplicative.ofAdd a⟩ = S (a, -a)) ∧
      Nonempty ((RightMod.LminusClosure S).lift (real G) hmem).Braided ∧
      ((RightMod.LminusClosure S).lift (real G) hmem).IsEquivalence := by
  obtain ⟨G, hGB, hG, hmem, hobj, hbr, heq⟩ :=
    Lminus_graded_braided_equivalence 𝕜 S hSchur hfusion hunitS hθ
  exact ⟨G, hmem, hobj, hbr, heq⟩

end Lminus

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.GrMat.instMonoidalCategory
#print axioms HaagerupIzumi.C8.GrMat.instSymmetricCategory
#print axioms HaagerupIzumi.C8.GrMat.monoidal_eq
#print axioms HaagerupIzumi.C8.GrMat.realBraidedCanonical
#print axioms HaagerupIzumi.C8.Lminus_vec_braided_equivalence
