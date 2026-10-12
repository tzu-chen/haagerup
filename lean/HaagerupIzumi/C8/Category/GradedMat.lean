module

public import HaagerupIzumi.C8.Category.LminusClosureFunctor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-! # Graded matrices: the untwisted `Vec_M` and its realization as a monoidal functor

For a commutative monoid `M` (written multiplicatively, as for `Discrete M`), `GrMat M 𝕜` is the
category of finite-dimensional `M`-graded `𝕜`-vector spaces with a chosen homogeneous basis: an
object is a finite type `I` of basis vectors with a degree map `deg : I → M`; a morphism is a
matrix `I × J → 𝕜` vanishing between basis vectors of different degrees.

* `GrMat.instMonoidalCategoryStruct`: the graded tensor product on index pairs
  (`(X ⊗ Y).I = X.I × Y.I`, degrees multiply), Kronecker product on matrices, and **the standard
  (untwisted) structure maps**: associator, unitors and braiding are the permutation matrices of
  `Equiv.prodAssoc`, `Equiv.uniqueProd`, `Equiv.prodUnique`, `Equiv.prodComm`.
* `real G : GrMat M 𝕜 ⥤ C`: for a functor `G : Discrete M ⥤ C` into a `𝕜`-linear category with
  finite biproducts, `X ↦ ⨁_{i ∈ X.I} G (deg i)`, `f ↦ (f i j • tr)` (scalar matrices).
  `real_faithful`, `real_full`: fully faithful when `Hom(G a, G b)` has dimension `δ_{a,b}`.
* `μIso`: for a monoidal `G`, the distributivity isomorphism
  `real X ⊗ real Y ≅ real (X ⊗ Y)`, with components the tensorators `μ_G (deg i) (deg j)` on the
  biproduct summands (`ι_μHom`).  `inducingData`: these satisfy all the compatibilities of
  `Monoidal.InducingFunctorData` (naturality via Kronecker entries, associativity and unitality
  via those of `G`, componentwise).
* `monoidal`: the resulting monoidal category structure on `GrMat M 𝕜` (its underlying
  `MonoidalCategoryStruct` is the standard one, `monoidal_toStruct`), for which `real G` is
  monoidal; `braided`: for braided `G`, the standard braiding (swap of index pairs) makes
  `GrMat M 𝕜` braided and `real G` braided (`realBraided`).

* `Lminus_graded_braided_equivalence`: for `G` the braided functor of `Lminus_braided_vec`
  (`G (a) = S (a, -a)`), the realization lifts to a braided monoidal equivalence
  `GrMat (ℤ/3) 𝕜 ≌ LminusClosure S`.  Inputs: `hSchur`, `hfusion`, `hunitS`, **[external]** `hθ`.

Here the coherence axioms of `GrMat M 𝕜` are obtained by `Monoidal.induced` along the faithful
realization; `GradedMatMonoidal.lean` proves them directly by matrix algebra
(`instMonoidalCategory`, `instSymmetricCategory`) and shows the two agree (`monoidal_eq`, by
`rfl`).  The structure maps are the standard ones in both.  No certificate inputs. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Limits Module

universe v u

/-- Finite-dimensional `M`-graded vector spaces with a chosen homogeneous basis. -/
structure GrMat (M : Type) (𝕜 : Type) where
  /-- The basis vectors. -/
  I : Type
  [fin : Fintype I]
  [dec : DecidableEq I]
  /-- The degree of each basis vector. -/
  deg : I → M

attribute [instance] GrMat.fin GrMat.dec

namespace GrMat

variable {M 𝕜 : Type}

section Category

variable [Semiring 𝕜]

/-- Morphisms of graded spaces: matrices vanishing between basis vectors of different degrees. -/
@[ext]
structure Hom (X Y : GrMat M 𝕜) where
  /-- The matrix. -/
  mat : Matrix X.I Y.I 𝕜
  graded : ∀ i j, X.deg i ≠ Y.deg j → mat i j = 0

instance : Category (GrMat M 𝕜) where
  Hom := Hom
  id X := ⟨1, fun _ _ h => Matrix.one_apply_ne (fun e => h (congrArg X.deg e))⟩
  comp {X Y Z} f g := ⟨f.mat * g.mat, fun i k h => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : X.deg i = Y.deg j
    · rw [g.graded j k (fun e => h (hj.trans e)), mul_zero]
    · rw [f.graded i j hj, zero_mul]⟩
  id_comp _ := Hom.ext (Matrix.one_mul _)
  comp_id _ := Hom.ext (Matrix.mul_one _)
  assoc _ _ _ := Hom.ext (Matrix.mul_assoc _ _ _)

@[simp]
theorem id_mat (X : GrMat M 𝕜) : Hom.mat (𝟙 X) = 1 := rfl

@[simp]
theorem comp_mat {X Y Z : GrMat M 𝕜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.mat (f ≫ g) = Hom.mat f * Hom.mat g := rfl

@[ext]
theorem hom_ext {X Y : GrMat M 𝕜} {f g : X ⟶ Y} (h : Hom.mat f = Hom.mat g) : f = g :=
  Hom.ext h

/-- The permutation matrix of a bijection. -/
def perm {α β : Type} [DecidableEq β] (e : α ≃ β) : Matrix α β 𝕜 :=
  Matrix.of fun i j => if e i = j then 1 else 0

theorem perm_apply {α β : Type} [DecidableEq β] (e : α ≃ β) (i : α) (j : β) :
    (perm e : Matrix α β 𝕜) i j = if e i = j then 1 else 0 := rfl

theorem perm_mul_perm {α β γ : Type} [Fintype β] [DecidableEq β] [DecidableEq γ] (e : α ≃ β)
    (e' : β ≃ γ) : perm e * perm e' = (perm (e.trans e') : Matrix α γ 𝕜) := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
  · show (if e i = e i then (1 : 𝕜) else 0) * (if e' (e i) = k then 1 else 0) =
      if e' (e i) = k then 1 else 0
    simp
  · intro j _ hj
    simp [perm_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem perm_refl {α : Type} [DecidableEq α] : (perm (Equiv.refl α) : Matrix α α 𝕜) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [perm_apply, Matrix.one_apply, h]

/-- The isomorphism of graded spaces given by a degree-preserving bijection of bases. -/
def reindexIso {X Y : GrMat M 𝕜} (e : X.I ≃ Y.I) (he : ∀ i, Y.deg (e i) = X.deg i) : X ≅ Y where
  hom := ⟨perm e, fun i j h => by
    rw [perm_apply, if_neg]
    rintro rfl
    exact h (he i).symm⟩
  inv := ⟨perm e.symm, fun j i h => by
    rw [perm_apply, if_neg]
    rintro rfl
    exact h (by simpa using he (e.symm j))⟩
  hom_inv_id := hom_ext (by simp [perm_mul_perm, perm_refl])
  inv_hom_id := hom_ext (by simp [perm_mul_perm, perm_refl])

@[simp]
theorem reindexIso_hom_mat {X Y : GrMat M 𝕜} (e : X.I ≃ Y.I) (he : ∀ i, Y.deg (e i) = X.deg i) :
    Hom.mat (reindexIso e he).hom = perm e := rfl

end Category

section MonoidalStruct

variable [CommSemiring 𝕜] [CommMonoid M]

/-- The graded tensor product: index pairs, degrees multiply. -/
@[reducible]
def tensorObj (X Y : GrMat M 𝕜) : GrMat M 𝕜 where
  I := X.I × Y.I
  deg p := X.deg p.1 * Y.deg p.2

/-- The Kronecker product of graded matrices. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : GrMat M 𝕜} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨Matrix.of fun p q => Hom.mat f p.1 q.1 * Hom.mat g p.2 q.2, fun p q h => by
    by_cases h1 : X₁.deg p.1 = Y₁.deg q.1
    · have h2 : X₂.deg p.2 ≠ Y₂.deg q.2 := fun h2 => h (by
        show X₁.deg p.1 * X₂.deg p.2 = Y₁.deg q.1 * Y₂.deg q.2
        rw [h1, h2])
      simp [Hom.graded g _ _ h2]
    · simp [Hom.graded f _ _ h1]⟩

/-- The unit: one basis vector of degree `1`. -/
@[reducible]
def tensorUnit : GrMat M 𝕜 where
  I := Unit
  deg _ := 1

/-- The standard (untwisted) monoidal structure data on graded matrices. -/
instance : MonoidalCategoryStruct (GrMat M 𝕜) where
  tensorObj := tensorObj
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator X Y Z :=
    reindexIso (Equiv.prodAssoc X.I Y.I Z.I) fun _ => (mul_assoc _ _ _).symm
  leftUnitor X := reindexIso (Equiv.uniqueProd X.I Unit) fun _ => (one_mul _).symm
  rightUnitor X := reindexIso (Equiv.prodUnique X.I Unit) fun _ => (mul_one _).symm

/-- The standard (symmetric) braiding: swap of index pairs. -/
def braidIso (X Y : GrMat M 𝕜) : X ⊗ Y ≅ Y ⊗ X :=
  reindexIso (Equiv.prodComm X.I Y.I) fun _ => mul_comm _ _

@[simp]
theorem tensorHom_mat {X₁ Y₁ X₂ Y₂ : GrMat M 𝕜} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (p : X₁.I × X₂.I) (q : Y₁.I × Y₂.I) :
    Hom.mat (MonoidalCategoryStruct.tensorHom f g) p q = Hom.mat f p.1 q.1 * Hom.mat g p.2 q.2 := rfl

end MonoidalStruct

section Real

variable [Field 𝕜] [CommMonoid M]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [Linear 𝕜 C]
  (G : Discrete M ⥤ C)

theorem dhom_eq {X Y : Discrete M} (f g : X ⟶ Y) : f = g := by
  rcases f with ⟨⟨_⟩⟩
  rcases g with ⟨⟨_⟩⟩
  rfl

open Classical in
/-- Transport between the lines of degrees `a` and `b` (zero if `a ≠ b`). -/
noncomputable def tr (a b : M) : G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩ :=
  if h : a = b then G.map (Discrete.eqToHom' h) else 0

theorem tr_of_eq {a b : M} (h : a = b) (f : (⟨a⟩ : Discrete M) ⟶ ⟨b⟩) : tr G a b = G.map f := by
  rw [tr, dif_pos h]
  exact congrArg G.map (dhom_eq _ _)

theorem tr_of_ne {a b : M} (h : a ≠ b) : tr G a b = 0 := by
  rw [tr, dif_neg h]

theorem tr_self (a : M) : tr G a a = 𝟙 _ := by
  rw [tr_of_eq G rfl (𝟙 _), G.map_id]

theorem tr_comp {a b c : M} (h1 : a = b) (h2 : b = c) : tr G a b ≫ tr G b c = tr G a c := by
  subst h1 h2
  rw [tr_self, Category.id_comp]

/-- The summands of the realization of a graded space. -/
abbrev fam (X : GrMat M 𝕜) : X.I → C := fun i => G.obj ⟨X.deg i⟩

/-- The realization of a graded matrix: a matrix of scalar multiples of transports. -/
noncomputable def realMap {X Y : GrMat M 𝕜} (f : X ⟶ Y) : ⨁ fam G X ⟶ ⨁ fam G Y :=
  biproduct.matrix fun i j => Hom.mat f i j • tr G (X.deg i) (Y.deg j)

theorem ι_realMap_π {X Y : GrMat M 𝕜} (f : X ⟶ Y) (i : X.I) (j : Y.I) :
    biproduct.ι (fam G X) i ≫ realMap G f ≫ biproduct.π (fam G Y) j =
      Hom.mat f i j • tr G (X.deg i) (Y.deg j) := by
  simp [realMap]

theorem biprod_ext {J K : Type} [Fintype J] [Fintype K] {f : J → C} {g : K → C}
    {x y : ⨁ f ⟶ ⨁ g}
    (h : ∀ j k, biproduct.ι f j ≫ x ≫ biproduct.π g k = biproduct.ι f j ≫ y ≫ biproduct.π g k) :
    x = y := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simpa only [Category.assoc] using h j k

theorem ι_comp_π {J K L : Type} [Fintype J] [Fintype K] [Fintype L] {f : J → C} {g : K → C}
    {h : L → C} (x : ⨁ f ⟶ ⨁ g) (y : ⨁ g ⟶ ⨁ h) (j : J) (l : L) :
    biproduct.ι f j ≫ (x ≫ y) ≫ biproduct.π h l =
      ∑ k, (biproduct.ι f j ≫ x ≫ biproduct.π g k) ≫ (biproduct.ι g k ≫ y ≫ biproduct.π h l) := by
  have e : x ≫ y = x ≫ (∑ k, biproduct.π g k ≫ biproduct.ι g k) ≫ y := by
    rw [biproduct.total, Category.id_comp]
  rw [e]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]

/-- **The realization functor** `X ↦ ⨁_{i ∈ X.I} G (deg i)`. -/
@[reducible]
noncomputable def real : GrMat M 𝕜 ⥤ C where
  obj X := ⨁ fam G X
  map f := realMap G f
  map_id X := by
    apply biprod_ext
    intro i j
    rw [ι_realMap_π, id_mat, Category.id_comp]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, one_smul, tr_self, biproduct.ι_π_self]
    · rw [Matrix.one_apply_ne h, zero_smul, biproduct.ι_π_ne _ h]
  map_comp {X Y Z} f g := by
    apply biprod_ext
    intro i k
    rw [ι_comp_π, ι_realMap_π G (f ≫ g) i k, comp_mat, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ι_realMap_π G f i j, ι_realMap_π G g j k, Linear.smul_comp, Linear.comp_smul, smul_smul]
    by_cases h1 : X.deg i = Y.deg j
    · by_cases h2 : Y.deg j = Z.deg k
      · rw [tr_comp G h1 h2]
      · rw [Hom.graded g j k h2, mul_zero, zero_smul, zero_smul]
    · rw [Hom.graded f i j h1, zero_mul, zero_smul, zero_smul]

section Schur

variable [DecidableEq M] [∀ a b : M, FiniteDimensional 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩)]
  (hG : ∀ a b : M, finrank 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0)

include hG in
theorem id_ne_zero (a : M) : (𝟙 (G.obj ⟨a⟩) : G.obj ⟨a⟩ ⟶ G.obj ⟨a⟩) ≠ 0 := by
  intro h
  have : Subsingleton (G.obj ⟨a⟩ ⟶ G.obj ⟨a⟩) := ⟨fun f g => by
    rw [← Category.comp_id f, ← Category.comp_id g, h, Limits.comp_zero, Limits.comp_zero]⟩
  have h1 := hG a a
  rw [if_pos rfl, Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

include hG in
theorem tr_ne_zero {a b : M} (h : a = b) : tr G a b ≠ 0 := by
  subst h
  rw [tr_self]
  exact id_ne_zero G hG a

include hG in
theorem exists_scal {a : M} (f : G.obj ⟨a⟩ ⟶ G.obj ⟨a⟩) : ∃ c : 𝕜, c • 𝟙 _ = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 _) (id_ne_zero G hG a)).1 (by rw [hG, if_pos rfl]) f

include hG in
theorem hom_subsingleton {a b : M} (h : a ≠ b) : Subsingleton (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) :=
  Module.finrank_zero_iff.1 (by rw [hG, if_neg h])

include hG in
theorem real_faithful : (real G : GrMat M 𝕜 ⥤ C).Faithful where
  map_injective {X Y} f g h := by
    apply hom_ext
    ext i j
    have e : biproduct.ι (fam G X) i ≫ realMap G f ≫ biproduct.π (fam G Y) j =
        biproduct.ι (fam G X) i ≫ realMap G g ≫ biproduct.π (fam G Y) j := by
      rw [show realMap G f = realMap G g from h]
    rw [ι_realMap_π, ι_realMap_π] at e
    by_cases hd : X.deg i = Y.deg j
    · exact smul_left_injective 𝕜 (tr_ne_zero G hG hd) e
    · rw [Hom.graded f i j hd, Hom.graded g i j hd]

include hG in
theorem real_full : (real G : GrMat M 𝕜 ⥤ C).Full where
  map_surjective {X Y} h := by
    change ⨁ fam G X ⟶ ⨁ fam G Y at h
    let c : X.I → Y.I → 𝕜 := fun i j =>
      if hd : X.deg i = Y.deg j then
        Classical.choose (exists_scal G hG (biproduct.ι (fam G X) i ≫ h ≫
          biproduct.π (fam G Y) j ≫ tr G (Y.deg j) (X.deg i)))
      else 0
    refine ⟨⟨Matrix.of c, fun i j hd => by simp [c, hd]⟩, ?_⟩
    change realMap G _ = h
    apply biprod_ext
    intro i j
    rw [ι_realMap_π]
    show c i j • _ = _
    by_cases hd : X.deg i = Y.deg j
    · have hc := Classical.choose_spec (exists_scal G hG (biproduct.ι (fam G X) i ≫ h ≫
        biproduct.π (fam G Y) j ≫ tr G (Y.deg j) (X.deg i)))
      simp only [c, dif_pos hd]
      rw [← Category.id_comp (tr G (X.deg i) (Y.deg j)), ← Linear.smul_comp, hc]
      simp only [Category.assoc]
      rw [tr_comp G hd.symm hd, tr_self, Category.comp_id]
    · simp only [c, dif_neg hd, zero_smul]
      have := hom_subsingleton G hG hd
      exact Subsingleton.elim _ _

end Schur

end Real


section MonoidalReal

variable [Field 𝕜] [CommMonoid M]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [Linear 𝕜 C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C]
  (G : Discrete M ⥤ C)

theorem smul_tensorHom' (r : 𝕜) {W X Y Z : C} (a : W ⟶ X) (b : Y ⟶ Z) :
    (r • a) ⊗ₘ b = r • (a ⊗ₘ b) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

theorem tensorHom_smul' (r : 𝕜) {W X Y Z : C} (a : W ⟶ X) (b : Y ⟶ Z) :
    a ⊗ₘ (r • b) = r • (a ⊗ₘ b) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
theorem tensor_comp_whiskerRight' {A B A' B' D : C} (a : A ⟶ A') (b : B ⟶ B') (c : A' ⟶ D) :
    (a ⊗ₘ b) ≫ (c ▷ B') = (a ≫ c) ⊗ₘ b := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
theorem tensor_comp_whiskerLeft' {A B A' B' D : C} (a : A ⟶ A') (b : B ⟶ B') (c : B' ⟶ D) :
    (a ⊗ₘ b) ≫ (A' ◁ c) = a ⊗ₘ (b ≫ c) := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
theorem comp_tensor_eq' {A A' A'' B B' : C} (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') :
    (a ≫ a') ⊗ₘ b = (a ▷ B) ≫ (a' ⊗ₘ b) := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
theorem tensor_comp_eq' {A A' B B' B'' : C} (a : A ⟶ A') (b : B ⟶ B') (b' : B' ⟶ B'') :
    a ⊗ₘ (b ≫ b') = (A ◁ b) ≫ (a ⊗ₘ b') := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
/-- The identity of a tensor product of biproducts, decomposed along the summands. -/
theorem tensor_total {J K : Type} [Fintype J] [Fintype K] (f : J → C) (g : K → C) :
    𝟙 ((⨁ f) ⊗ (⨁ g)) = ∑ j, ∑ k,
      (biproduct.π f j ⊗ₘ biproduct.π g k) ≫ (biproduct.ι f j ⊗ₘ biproduct.ι g k) := by
  rw [← id_tensorHom_id, ← biproduct.total, ← biproduct.total]
  simp only [sum_tensor, tensor_sum, ← tensorHom_comp_tensorHom]
  exact Finset.sum_comm

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
/-- Maps out of a tensor product of biproducts are determined on pairs of summands. -/
theorem tensor_ext {J K : Type} [Fintype J] [Fintype K] {f : J → C} {g : K → C} {W : C}
    {x y : (⨁ f) ⊗ (⨁ g) ⟶ W}
    (h : ∀ j k, (biproduct.ι f j ⊗ₘ biproduct.ι g k) ≫ x = (biproduct.ι f j ⊗ₘ biproduct.ι g k) ≫ y) :
    x = y := by
  rw [← Category.id_comp x, ← Category.id_comp y, tensor_total]
  simp only [Preadditive.sum_comp, Category.assoc, h]

omit [Linear 𝕜 C] [MonoidalLinear 𝕜 C] in
/-- Maps out of a triple tensor product of biproducts are determined on triples of summands. -/
theorem tensor_ext₃ {J K L : Type} [Fintype J] [Fintype K] [Fintype L] {f : J → C} {g : K → C}
    {h : L → C} {W : C} {x y : ((⨁ f) ⊗ (⨁ g)) ⊗ (⨁ h) ⟶ W}
    (H : ∀ j k l, ((biproduct.ι f j ⊗ₘ biproduct.ι g k) ⊗ₘ biproduct.ι h l) ≫ x =
      ((biproduct.ι f j ⊗ₘ biproduct.ι g k) ⊗ₘ biproduct.ι h l) ≫ y) :
    x = y := by
  rw [← Category.id_comp x, ← Category.id_comp y, ← id_tensorHom_id, tensor_total f g,
    ← biproduct.total]
  simp only [sum_tensor, tensor_sum, ← tensorHom_comp_tensorHom, Preadditive.sum_comp,
    Category.assoc, H]

variable [G.Monoidal]

/-- The tensorator of `G` on the lines. -/
noncomputable def μG (a b : M) : G.obj ⟨a⟩ ⊗ G.obj ⟨b⟩ ≅ G.obj ⟨a * b⟩ :=
  Functor.Monoidal.μIso G ⟨a⟩ ⟨b⟩

theorem tr_tensor_μG {a a' b b' : M} (ha : a = a') (hb : b = b') :
    (tr G a a' ⊗ₘ tr G b b') ≫ (μG G a' b').hom = (μG G a b).hom ≫ tr G (a * b) (a' * b') := by
  subst ha hb
  rw [tr_self, tr_self, tr_self, id_tensorHom_id, Category.id_comp, Category.comp_id]

theorem μG_assoc (a b c : M) :
    ((μG G a b).hom ▷ G.obj ⟨c⟩) ≫ (μG G (a * b) c).hom ≫ tr G (a * b * c) (a * (b * c)) =
      (α_ _ _ _).hom ≫ (G.obj ⟨a⟩ ◁ (μG G b c).hom) ≫ (μG G a (b * c)).hom := by
  rw [tr_of_eq G (mul_assoc a b c) (α_ (⟨a⟩ : Discrete M) ⟨b⟩ ⟨c⟩).hom]
  exact Functor.LaxMonoidal.associativity G ⟨a⟩ ⟨b⟩ ⟨c⟩

theorem μG_left (a : M) :
    (μG G 1 a).hom ≫ tr G (1 * a) a =
      ((Functor.Monoidal.εIso G).inv ▷ G.obj ⟨a⟩) ≫ (λ_ (G.obj ⟨a⟩)).hom := by
  rw [tr_of_eq G (one_mul a) (λ_ (⟨a⟩ : Discrete M)).hom, Functor.LaxMonoidal.left_unitality G ⟨a⟩,
    show Functor.LaxMonoidal.ε G = (Functor.Monoidal.εIso G).hom from rfl,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  rfl

theorem μG_right (a : M) :
    (μG G a 1).hom ≫ tr G (a * 1) a =
      (G.obj ⟨a⟩ ◁ (Functor.Monoidal.εIso G).inv) ≫ (ρ_ (G.obj ⟨a⟩)).hom := by
  rw [tr_of_eq G (mul_one a) (ρ_ (⟨a⟩ : Discrete M)).hom,
    Functor.LaxMonoidal.right_unitality G ⟨a⟩,
    show Functor.LaxMonoidal.ε G = (Functor.Monoidal.εIso G).hom from rfl,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  rfl

/-- The distributivity map `real X ⊗ real Y ⟶ real (X ⊗ Y)`: on the summand `(i, j)` it is the
tensorator `μ_G (deg i) (deg j)`. -/
noncomputable def μHom (X Y : GrMat M 𝕜) : (⨁ fam G X) ⊗ (⨁ fam G Y) ⟶ ⨁ fam G (X ⊗ Y) :=
  biproduct.lift fun p => (biproduct.π (fam G X) p.1 ⊗ₘ biproduct.π (fam G Y) p.2) ≫
    (μG G (X.deg p.1) (Y.deg p.2)).hom

/-- The inverse of `μHom`. -/
noncomputable def μInv (X Y : GrMat M 𝕜) : ⨁ fam G (X ⊗ Y) ⟶ (⨁ fam G X) ⊗ (⨁ fam G Y) :=
  biproduct.desc fun p => (μG G (X.deg p.1) (Y.deg p.2)).inv ≫
    (biproduct.ι (fam G X) p.1 ⊗ₘ biproduct.ι (fam G Y) p.2)

theorem μHom_π (X Y : GrMat M 𝕜) (k : X.I) (l : Y.I) :
    μHom G X Y ≫ biproduct.π (fam G (X ⊗ Y)) (k, l) =
      (biproduct.π (fam G X) k ⊗ₘ biproduct.π (fam G Y) l) ≫ (μG G (X.deg k) (Y.deg l)).hom :=
  biproduct.lift_π _ _

theorem ι_μInv (X Y : GrMat M 𝕜) (i : X.I) (j : Y.I) :
    biproduct.ι (fam G (X ⊗ Y)) (i, j) ≫ μInv G X Y =
      (μG G (X.deg i) (Y.deg j)).inv ≫ (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j) :=
  biproduct.ι_desc _ _

theorem μHom_μInv (X Y : GrMat M 𝕜) : μHom G X Y ≫ μInv G X Y = 𝟙 _ := by
  rw [μHom, μInv, biproduct.lift_desc, tensor_total]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact Fintype.sum_prod_type (f := fun p : X.I × Y.I =>
    (biproduct.π (fam G X) p.1 ⊗ₘ biproduct.π (fam G Y) p.2) ≫
      (biproduct.ι (fam G X) p.1 ⊗ₘ biproduct.ι (fam G Y) p.2))

theorem μInv_μHom (X Y : GrMat M 𝕜) : μInv G X Y ≫ μHom G X Y = 𝟙 _ := by
  apply biproduct.hom_ext'
  rintro ⟨i, j⟩
  apply biproduct.hom_ext
  rintro ⟨k, l⟩
  rw [Category.comp_id, Category.assoc, Category.assoc, μHom_π, ← Category.assoc, ι_μInv,
    Category.assoc, tensorHom_comp_tensorHom_assoc]
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      simp
    · rw [biproduct.ι_π_ne _ hjl, MonoidalPreadditive.tensor_zero, Limits.zero_comp, Limits.comp_zero,
        biproduct.ι_π_ne _ (fun h => hjl (congrArg Prod.snd h))]
  · rw [biproduct.ι_π_ne _ hik, MonoidalPreadditive.zero_tensor, Limits.zero_comp, Limits.comp_zero,
      biproduct.ι_π_ne _ (fun h => hik (congrArg Prod.fst h))]

/-- **Distributivity of the realization**: `μ_G` on the summand `(i, j)`. -/
theorem ι_μHom (X Y : GrMat M 𝕜) (i : X.I) (j : Y.I) :
    (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j) ≫ μHom G X Y =
      (μG G (X.deg i) (Y.deg j)).hom ≫ biproduct.ι (fam G (X ⊗ Y)) (i, j) := by
  rw [← Iso.hom_inv_id_assoc (μG G (X.deg i) (Y.deg j))
      (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j), ← ι_μInv, Category.assoc,
    Category.assoc, μInv_μHom, Category.comp_id]

/-- The tensorator of the realization. -/
noncomputable def realμIso (X Y : GrMat M 𝕜) :
    (real G).obj X ⊗ (real G).obj Y ≅ (real G).obj (X ⊗ Y) where
  hom := μHom G X Y
  inv := μInv G X Y
  hom_inv_id := μHom_μInv G X Y
  inv_hom_id := μInv_μHom G X Y

/-- The unit isomorphism of the realization. -/
noncomputable def realεIso : 𝟙_ C ≅ (real G).obj (𝟙_ (GrMat M 𝕜)) where
  hom := (Functor.Monoidal.εIso G).hom ≫ biproduct.ι (fam G (𝟙_ (GrMat M 𝕜))) ()
  inv := biproduct.π (fam G (𝟙_ (GrMat M 𝕜))) () ≫ (Functor.Monoidal.εIso G).inv
  hom_inv_id := by simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro ⟨⟩
    simp

theorem ι_realεIso_inv :
    biproduct.ι (fam G (𝟙_ (GrMat M 𝕜))) () ≫ (realεIso G).inv =
      (Functor.Monoidal.εIso G).inv := by
  simp [realεIso]

/-- Naturality of the distributivity isomorphism (Kronecker products of scalar matrices). -/
theorem μHom_realMap_tensor {X₁ Y₁ X₂ Y₂ : GrMat M 𝕜} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    μHom G X₁ X₂ ≫ realMap G (MonoidalCategoryStruct.tensorHom f g) =
      (realMap G f ⊗ₘ realMap G g) ≫ μHom G Y₁ Y₂ := by
  apply tensor_ext
  intro i j
  apply biproduct.hom_ext
  rintro ⟨k, l⟩
  simp only [Category.assoc]
  rw [← Category.assoc (biproduct.ι (fam G X₁) i ⊗ₘ biproduct.ι (fam G X₂) j), ι_μHom,
    Category.assoc, ι_realMap_π G (MonoidalCategoryStruct.tensorHom f g) (i, j) (k, l), μHom_π,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, Category.assoc, Category.assoc, ι_realMap_π,
    ι_realMap_π]
  simp only [Linear.comp_smul, Linear.smul_comp, smul_tensorHom', tensorHom_smul', smul_smul,
    tensorHom_mat]
  by_cases h1 : X₁.deg i = Y₁.deg k
  · by_cases h2 : X₂.deg j = Y₂.deg l
    · rw [tr_tensor_μG G h1 h2, mul_comm]
      rfl
    · simp only [Hom.graded g j l h2, mul_zero, zero_mul, zero_smul]
  · simp only [Hom.graded f i k h1, mul_zero, zero_mul, zero_smul]

theorem realMap_tensor_eq {X₁ Y₁ X₂ Y₂ : GrMat M 𝕜} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    realMap G (MonoidalCategoryStruct.tensorHom f g) =
      μInv G X₁ X₂ ≫ (realMap G f ⊗ₘ realMap G g) ≫ μHom G Y₁ Y₂ := by
  rw [← μHom_realMap_tensor, ← Category.assoc, μInv_μHom, Category.id_comp]

theorem associator_mat (X Y Z : GrMat M 𝕜) :
    Hom.mat (α_ X Y Z).hom = perm (Equiv.prodAssoc X.I Y.I Z.I) := rfl

theorem leftUnitor_mat (X : GrMat M 𝕜) :
    Hom.mat (λ_ X).hom = perm (Equiv.uniqueProd X.I Unit) := rfl

theorem rightUnitor_mat (X : GrMat M 𝕜) :
    Hom.mat (ρ_ X).hom = perm (Equiv.prodUnique X.I Unit) := rfl

theorem braidIso_mat (X Y : GrMat M 𝕜) :
    Hom.mat (braidIso X Y).hom = perm (Equiv.prodComm X.I Y.I) := rfl

/-- **Associativity of the distributivity isomorphism**, from the associativity of `μ_G`
componentwise. -/
theorem assoc_core (X Y Z : GrMat M 𝕜) :
    (μHom G X Y ▷ (⨁ fam G Z)) ≫ μHom G (X ⊗ Y) Z ≫ realMap G (α_ X Y Z).hom =
      (α_ _ _ _).hom ≫ ((⨁ fam G X) ◁ μHom G Y Z) ≫ μHom G X (Y ⊗ Z) := by
  apply tensor_ext₃
  intro i j k
  apply biproduct.hom_ext
  rintro ⟨i', j', k'⟩
  simp only [Category.assoc]
  rw [← Category.assoc ((biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j) ⊗ₘ
      biproduct.ι (fam G Z) k), tensor_comp_whiskerRight', ι_μHom, comp_tensor_eq',
    Category.assoc, ← Category.assoc (biproduct.ι (fam G (X ⊗ Y)) (i, j) ⊗ₘ biproduct.ι (fam G Z) k),
    ι_μHom, Category.assoc, ι_realMap_π, associator_mat, perm_apply,
    ← Category.assoc ((biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j) ⊗ₘ
      biproduct.ι (fam G Z) k), associator_naturality, Category.assoc,
    ← Category.assoc (biproduct.ι (fam G X) i ⊗ₘ (biproduct.ι (fam G Y) j ⊗ₘ
      biproduct.ι (fam G Z) k)), tensor_comp_whiskerLeft', ι_μHom, tensor_comp_eq',
    Category.assoc, ← Category.assoc (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G (Y ⊗ Z)) (j, k)),
    ι_μHom]
  simp only [Category.assoc]
  by_cases hq : (i, (j, k)) = (i', (j', k'))
  · simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    simp only [Equiv.prodAssoc_apply, if_true, one_smul, biproduct.ι_π_self]
    erw [Category.comp_id]
    exact μG_assoc G (X.deg i) (Y.deg j) (Z.deg k)
  · rw [if_neg (by simpa using hq), zero_smul, Limits.comp_zero, Limits.comp_zero,
      biproduct.ι_π_ne _ hq, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]

/-- Left unitality of the realization. -/
theorem left_core (X : GrMat M 𝕜) :
    μHom G (𝟙_ _) X ≫ realMap G (λ_ X).hom =
      ((realεIso G).inv ▷ (⨁ fam G X)) ≫ (λ_ (⨁ fam G X)).hom := by
  apply tensor_ext
  rintro ⟨⟩ j
  apply biproduct.hom_ext
  intro k
  simp only [Category.assoc]
  rw [← Category.assoc (biproduct.ι (fam G (𝟙_ (GrMat M 𝕜))) () ⊗ₘ biproduct.ι (fam G X) j),
    ι_μHom, Category.assoc, ι_realMap_π, leftUnitor_mat, perm_apply,
    ← Category.assoc (biproduct.ι (fam G (𝟙_ (GrMat M 𝕜))) () ⊗ₘ biproduct.ι (fam G X) j),
    tensor_comp_whiskerRight', ι_realεIso_inv, MonoidalCategory.tensorHom_def, Category.assoc,
    leftUnitor_naturality_assoc]
  by_cases hjk : j = k
  · subst hjk
    simp only [Equiv.uniqueProd_apply, if_true, one_smul, biproduct.ι_π_self, Category.comp_id]
    exact μG_left G (X.deg j)
  · rw [if_neg (by simpa using hjk), zero_smul, Limits.comp_zero, biproduct.ι_π_ne _ hjk,
      Limits.comp_zero, Limits.comp_zero]

/-- Right unitality of the realization. -/
theorem right_core (X : GrMat M 𝕜) :
    μHom G X (𝟙_ _) ≫ realMap G (ρ_ X).hom =
      ((⨁ fam G X) ◁ (realεIso G).inv) ≫ (ρ_ (⨁ fam G X)).hom := by
  apply tensor_ext
  rintro i ⟨⟩
  apply biproduct.hom_ext
  intro k
  simp only [Category.assoc]
  rw [← Category.assoc (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G (𝟙_ (GrMat M 𝕜))) ()),
    ι_μHom, Category.assoc, ι_realMap_π, rightUnitor_mat, perm_apply,
    ← Category.assoc (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G (𝟙_ (GrMat M 𝕜))) ()),
    tensor_comp_whiskerLeft', ι_realεIso_inv, MonoidalCategory.tensorHom_def', Category.assoc,
    rightUnitor_naturality_assoc]
  by_cases hik : i = k
  · subst hik
    simp only [Equiv.prodUnique_apply, if_true, one_smul, biproduct.ι_π_self, Category.comp_id]
    exact μG_right G (X.deg i)
  · rw [if_neg (by simpa using hik), zero_smul, Limits.comp_zero, biproduct.ι_π_ne _ hik,
      Limits.comp_zero, Limits.comp_zero]

/-- **The realization preserves the standard tensor structure up to the distributivity
isomorphisms**: the data of `Monoidal.InducingFunctorData`. -/
noncomputable def inducingData : Monoidal.InducingFunctorData (real G : GrMat M 𝕜 ⥤ C) where
  μIso := realμIso G
  whiskerLeft_eq X {Y₁ Y₂} f := by
    show realMap G (MonoidalCategoryStruct.tensorHom (𝟙 X) f) =
      μInv G X Y₁ ≫ ((⨁ fam G X) ◁ realMap G f) ≫ μHom G X Y₂
    rw [realMap_tensor_eq, show realMap G (𝟙 X) = 𝟙 (⨁ fam G X) from (real G).map_id X,
      id_tensorHom]
  whiskerRight_eq {X₁ X₂} f Y := by
    show realMap G (MonoidalCategoryStruct.tensorHom f (𝟙 Y)) =
      μInv G X₁ Y ≫ (realMap G f ▷ (⨁ fam G Y)) ≫ μHom G X₂ Y
    rw [realMap_tensor_eq, show realMap G (𝟙 Y) = 𝟙 (⨁ fam G Y) from (real G).map_id Y,
      tensorHom_id]
  tensorHom_eq f g := realMap_tensor_eq G f g
  εIso := realεIso G
  associator_eq X Y Z := by
    show realMap G (α_ X Y Z).hom = (μInv G (X ⊗ Y) Z ≫ (μInv G X Y ⊗ₘ 𝟙 (⨁ fam G Z))) ≫
      (α_ (⨁ fam G X) (⨁ fam G Y) (⨁ fam G Z)).hom ≫
        ((𝟙 (⨁ fam G X) ⊗ₘ μHom G Y Z) ≫ μHom G X (Y ⊗ Z))
    rw [tensorHom_id, id_tensorHom, ← assoc_core, Category.assoc, ← comp_whiskerRight_assoc,
      μInv_μHom, id_whiskerRight, Category.id_comp, ← Category.assoc, μInv_μHom,
      Category.id_comp]
  leftUnitor_eq X := by
    show realMap G (λ_ X).hom = (μInv G (𝟙_ _) X ≫ ((realεIso G).inv ⊗ₘ 𝟙 (⨁ fam G X))) ≫
      (λ_ (⨁ fam G X)).hom
    rw [tensorHom_id, Category.assoc, ← left_core, ← Category.assoc, μInv_μHom, Category.id_comp]
  rightUnitor_eq X := by
    show realMap G (ρ_ X).hom = (μInv G X (𝟙_ _) ≫ (𝟙 (⨁ fam G X) ⊗ₘ (realεIso G).inv)) ≫
      (ρ_ (⨁ fam G X)).hom
    rw [id_tensorHom, Category.assoc, ← right_core, ← Category.assoc, μInv_μHom,
      Category.id_comp]

end MonoidalReal

section BraidedReal

variable [Field 𝕜] [CommMonoid M]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [Linear 𝕜 C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [BraidedCategory C]
  (G : Discrete M ⥤ C) [G.Braided]

theorem μG_braid (a b : M) :
    (μG G a b).hom ≫ tr G (a * b) (b * a) = (β_ _ _).hom ≫ (μG G b a).hom := by
  rw [tr_of_eq G (mul_comm a b) (β_ (⟨a⟩ : Discrete M) ⟨b⟩).hom]
  exact Functor.LaxBraided.braided (F := G) ⟨a⟩ ⟨b⟩

/-- Compatibility of the realization with the standard braiding (swap of index pairs). -/
theorem braid_core (X Y : GrMat M 𝕜) :
    μHom G X Y ≫ realMap G (braidIso X Y).hom = (β_ _ _).hom ≫ μHom G Y X := by
  apply tensor_ext
  intro i j
  apply biproduct.hom_ext
  rintro ⟨l, k⟩
  simp only [Category.assoc]
  rw [← Category.assoc (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j), ι_μHom,
    Category.assoc, ι_realMap_π, braidIso_mat, perm_apply,
    ← Category.assoc (biproduct.ι (fam G X) i ⊗ₘ biproduct.ι (fam G Y) j),
    BraidedCategory.braiding_naturality, Category.assoc, μHom_π, tensorHom_comp_tensorHom_assoc]
  by_cases hq : j = l ∧ i = k
  · obtain ⟨rfl, rfl⟩ := hq
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, if_true, one_smul,
      biproduct.ι_π_self, id_tensorHom_id, Category.id_comp]
    exact μG_braid G (X.deg i) (Y.deg j)
  · rw [if_neg (by simpa using hq), zero_smul, Limits.comp_zero]
    by_cases hjl : j = l
    · have hik : i ≠ k := fun h => hq ⟨hjl, h⟩
      rw [biproduct.ι_π_ne _ hik, MonoidalPreadditive.tensor_zero, Limits.zero_comp, Limits.comp_zero]
    · rw [biproduct.ι_π_ne _ hjl, MonoidalPreadditive.zero_tensor, Limits.zero_comp, Limits.comp_zero]

end BraidedReal

section Induced

variable [Field 𝕜] [CommMonoid M] [DecidableEq M]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [Linear 𝕜 C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C]
  (G : Discrete M ⥤ C) [G.Monoidal] [∀ a b : M, FiniteDimensional 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩)]
  (hG : ∀ a b : M, finrank 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0)

/-- **The monoidal category of graded matrices**: the standard structure data
(`instMonoidalCategoryStruct`), with the coherence axioms induced along the faithful
realization `real G`. -/
@[instance_reducible]
noncomputable def monoidal : MonoidalCategory (GrMat M 𝕜) :=
  letI := real_faithful G hG
  Monoidal.induced (real G) (inducingData G)

/-- The structure maps of `monoidal` are the standard ones. -/
theorem monoidal_toStruct :
    (monoidal G hG).toMonoidalCategoryStruct =
      (inferInstance : MonoidalCategoryStruct (GrMat M 𝕜)) := rfl

/-- **The realization is a monoidal functor**, with tensorator `realμIso` (the tensorators of
`G` on biproduct components) and unit `realεIso`. -/
@[instance_reducible]
noncomputable def realMonoidal :
    letI := monoidal G hG
    (real G : GrMat M 𝕜 ⥤ C).Monoidal :=
  letI := real_faithful G hG
  Monoidal.fromInducedMonoidal (real G) (inducingData G)

end Induced

/-- The standard braiding is symmetric. -/
theorem braidIso_symm [CommSemiring 𝕜] [CommMonoid M] (X Y : GrMat M 𝕜) :
    (braidIso X Y).hom ≫ (braidIso Y X).hom = 𝟙 _ := by
  apply hom_ext
  show (perm (Equiv.prodComm X.I Y.I) * perm (Equiv.prodComm Y.I X.I) :
    Matrix (X.I × Y.I) (X.I × Y.I) 𝕜) = 1
  rw [perm_mul_perm]
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [perm_apply, Matrix.one_apply]

section InducedBraided

variable [Field 𝕜] [CommMonoid M] [DecidableEq M]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [Linear 𝕜 C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [BraidedCategory C]
  (G : Discrete M ⥤ C) [G.Braided] [∀ a b : M, FiniteDimensional 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩)]
  (hG : ∀ a b : M, finrank 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0)

/-- **The standard (swap) braiding on graded matrices**, braided coherence induced along the
realization of a braided `G`. -/
@[instance_reducible]
noncomputable def braided :
    letI := monoidal G hG
    BraidedCategory (GrMat M 𝕜) :=
  letI := monoidal G hG
  letI := real_faithful G hG
  letI := realMonoidal G hG
  BraidedCategory.ofFaithful (real G) braidIso (fun X Y => braid_core G X Y)

theorem braided_braiding (X Y : GrMat M 𝕜) :
    letI := monoidal G hG
    letI := braided G hG
    (β_ X Y).hom = (braidIso X Y).hom := rfl

/-- The braiding of `GrMat M 𝕜` is symmetric (untwisted `Vec_M`). -/
@[instance_reducible]
noncomputable def symmetric :
    letI := monoidal G hG
    SymmetricCategory (GrMat M 𝕜) :=
  letI := monoidal G hG
  { braided G hG with symmetry := fun X Y => braidIso_symm (𝕜 := 𝕜) X Y }

/-- **The realization is a braided monoidal functor.** -/
@[instance_reducible]
noncomputable def realBraided :
    letI := monoidal G hG
    letI := braided G hG
    (real G : GrMat M 𝕜 ⥤ C).Braided :=
  letI := monoidal G hG
  letI := braided G hG
  letI := realMonoidal G hG
  { (realMonoidal G hG) with braided := fun X Y => braid_core G X Y }

end InducedBraided

section Lminus

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type) [Field 𝕜]
  [Linear 𝕜 C] [MonoidalLinear 𝕜 C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]

theorem real_mem_LminusClosure (S : ZMod 3 × ZMod 3 → C)
    (G : Discrete (Multiplicative (ZMod 3)) ⥤ C)
    (hobj : ∀ a : ZMod 3, G.obj ⟨Multiplicative.ofAdd a⟩ = S (a, -a))
    (X : GrMat (Multiplicative (ZMod 3)) 𝕜) :
    RightMod.LminusClosure S ((real G).obj X) := by
  let e := Fintype.equivFin X.I
  refine ⟨Fintype.card X.I, fun j => Multiplicative.toAdd (X.deg (e.symm j)), ⟨?_⟩⟩
  refine biproduct.whiskerEquiv e (fun i => eqToIso ?_)
  simp only [Equiv.symm_apply_apply]
  exact (hobj _).symm

theorem real_essSurj_LminusClosure (S : ZMod 3 × ZMod 3 → C)
    (G : Discrete (Multiplicative (ZMod 3)) ⥤ C)
    (hobj : ∀ a : ZMod 3, G.obj ⟨Multiplicative.ofAdd a⟩ = S (a, -a))
    {Y : C} (hY : RightMod.LminusClosure S Y) :
    ∃ X : GrMat (Multiplicative (ZMod 3)) 𝕜, Nonempty ((real G).obj X ≅ Y) := by
  obtain ⟨n, a, ⟨eY⟩⟩ := hY
  exact ⟨{ I := Fin n, deg := fun j => Multiplicative.ofAdd (a j) },
    ⟨biproduct.mapIso (fun j => eqToIso (hobj (a j))) ≪≫ eY.symm⟩⟩

/-- **Braided monoidal comparison `Vec_{ℤ/3}` ≃ additive closure of `L₋`.**  Under `hSchur`,
`hfusion`, `hunitS` and **[external]** `hθ`, there is a braided monoidal functor
`G : Discrete (ℤ/3) ⥤ C` with `G (a) = S (a, -a)` and Schur property `hG`, such that the
realization of graded matrices lifts to a **braided monoidal equivalence**
`GrMat (ℤ/3) 𝕜 ≌ LminusClosure S`, where `GrMat (ℤ/3) 𝕜` carries the standard untwisted
symmetric structure (`monoidal`, `braided`, with structure maps the permutation matrices of
`Equiv.prodAssoc`, `Equiv.uniqueProd`, `Equiv.prodUnique`, `Equiv.prodComm`) and
`LminusClosure S` the monoidal structure of `lminusClosure_isMonoidal` with the inherited
braiding. -/
theorem Lminus_graded_braided_equivalence (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) :
    haveI := RightMod.lminusClosure_isMonoidal hfusion hunitS
    ∃ (G : Discrete (Multiplicative (ZMod 3)) ⥤ C) (hGB : G.Braided)
      (hG : ∀ a b, finrank 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0)
      (hmem : ∀ X : GrMat (Multiplicative (ZMod 3)) 𝕜,
        RightMod.LminusClosure S ((real G).obj X)),
      (∀ a : ZMod 3, G.obj ⟨Multiplicative.ofAdd a⟩ = S (a, -a)) ∧
      (letI := hGB
       letI := monoidal G hG
       letI := braided G hG
       Nonempty ((RightMod.LminusClosure S).lift (real G) hmem).Braided) ∧
      ((RightMod.LminusClosure S).lift (real G) hmem).IsEquivalence := by
  have := RightMod.lminusClosure_isMonoidal hfusion hunitS
  obtain ⟨G, hGB, hobj, hdim⟩ := PointedCocycle.Lminus_braided_vec 𝕜 S hSchur hfusion hunitS hθ
  have hG : ∀ a b, finrank 𝕜 (G.obj ⟨a⟩ ⟶ G.obj ⟨b⟩) = if a = b then 1 else 0 := by
    intro a b
    rw [hdim]
    by_cases h : a = b
    · rw [if_pos (congrArg Discrete.mk h), if_pos h]
    · rw [if_neg (fun h' => h (congrArg Discrete.as h')), if_neg h]
  have hmem := real_mem_LminusClosure 𝕜 S G hobj
  refine ⟨G, hGB, hG, hmem, hobj, ?_, ?_⟩
  · let _ := hGB
    let _ := monoidal G hG
    let _ := braided G hG
    have := real_faithful G hG
    exact ⟨RightMod.liftBraided (RightMod.LminusClosure S) (real G) hmem
      (Monoidal.fromInducedCoreMonoidal (real G) (inducingData G))
      (fun X Y => braid_core G X Y)⟩
  · have hfaith := real_faithful (𝕜 := 𝕜) G hG
    have hfull := real_full (𝕜 := 𝕜) G hG
    have hf1 : ((RightMod.LminusClosure S).lift (real G) hmem ⋙
      (RightMod.LminusClosure S).ι).Faithful := hfaith
    have hf2 : ((RightMod.LminusClosure S).lift (real G) hmem ⋙
      (RightMod.LminusClosure S).ι).Full := hfull
    refine
      { faithful := Functor.Faithful.of_comp _ (RightMod.LminusClosure S).ι
        full := Functor.Full.of_comp_faithful _ (RightMod.LminusClosure S).ι
        essSurj := ⟨fun Y => ?_⟩ }
    obtain ⟨X, ⟨e⟩⟩ := real_essSurj_LminusClosure 𝕜 S G hobj Y.property
    exact ⟨X, ⟨(RightMod.LminusClosure S).isoMk e⟩⟩

end Lminus

end GrMat

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.GrMat.reindexIso
#print axioms HaagerupIzumi.C8.GrMat.real
#print axioms HaagerupIzumi.C8.GrMat.real_faithful
#print axioms HaagerupIzumi.C8.GrMat.real_full
#print axioms HaagerupIzumi.C8.GrMat.ι_μHom
#print axioms HaagerupIzumi.C8.GrMat.inducingData
#print axioms HaagerupIzumi.C8.GrMat.monoidal
#print axioms HaagerupIzumi.C8.GrMat.realMonoidal
#print axioms HaagerupIzumi.C8.GrMat.braided
#print axioms HaagerupIzumi.C8.GrMat.symmetric
#print axioms HaagerupIzumi.C8.GrMat.realBraided
#print axioms HaagerupIzumi.C8.GrMat.Lminus_graded_braided_equivalence
