module

public import HaagerupIzumi.C8.Category.AbelianCocycleZ3
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! # The abelian 3-cocycle of a pointed braided linear category (skeletalization)

Let `C` be a `𝕜`-linear braided monoidal category (`𝕜` a field, linear composition and
whiskering), `A` an additive commutative group and `S : A → C` objects with one-dimensional
endomorphism algebras (`hEnd : finrank 𝕜 (S a ⟶ S a) = 1`), with chosen isomorphisms
`φ a b : S a ⊗ S b ≅ S (a + b)`.

* `scal`: the Schur scalar of an endomorphism of `S a` (`f = scal f • 𝟙`).
* `ωs φ a b c`: the scalar of `(φ_{a,b} ▷ S c ≫ φ_{a+b,c})⁻¹ ≫ α ≫ (S a ◁ φ_{b,c} ≫ φ_{a,b+c})`
  (followed by the identification `S (a + (b + c)) = S ((a + b) + c)`); `ω_rel`:
  `α ≫ S a ◁ φ_{b,c} ≫ φ_{a,b+c} = ωs a b c • (φ_{a,b} ▷ S c ≫ φ_{a+b,c} ≫ eqToHom _)`.
* `cs φ a b`: the scalar of `φ_{a,b}⁻¹ ≫ β_{S a, S b} ≫ φ_{b,a}`; `c_rel`.
* `pentagon_scalar`, `hexagon_forward_scalar`, `hexagon_reverse_scalar`: from Mathlib's pentagon
  and hexagon axioms, `(ωs, cs)` satisfies the pentagon and both hexagon equations of an
  abelian 3-cocycle (`AbelianCocycle`, `Category/AbelianCocycleZ3.lean`), without
  normalization.  `ωs_ne_zero`, `cs_ne_zero`: the scalars are units.
* `ωs_scale`, `cs_scale`: rescaling `φ_{a,b}` by `g(a,b) ∈ 𝕜ˣ` changes `(ωs, cs)` by the
  abelian coboundary of `g⁻¹`: the class of `(ωs, cs)` does not depend on the choice of `φ`.
* `cs_self_eq_one`: if the self-braiding `β_{S a, S a}` is the identity, then `cs φ a a = 1` for
  every choice of `φ`.

The skeletalization statement for `L₋` (trivial twists ⇒ untwisted and symmetric) is
`Category/PointedCocycleZ3.lean`.  No external-theorem or certificate inputs. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Module

universe v u

namespace PointedCocycle

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]
  {A : Type*} [AddCommGroup A] (S : A → C) (hEnd : ∀ a, finrank 𝕜 (S a ⟶ S a) = 1)

section Scalar

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] [AddCommGroup A] in
include hEnd in
theorem id_ne_zero (a : A) : (𝟙 (S a) : S a ⟶ S a) ≠ 0 := by
  intro h
  have : Subsingleton (S a ⟶ S a) := ⟨fun f g => by
    rw [← Category.comp_id f, ← Category.comp_id g, h, Limits.comp_zero, Limits.comp_zero]⟩
  have h1 := hEnd a
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

/-- The Schur scalar of an endomorphism of `S a`. -/
noncomputable def scal {a : A} (f : S a ⟶ S a) : 𝕜 :=
  Classical.choose
    ((finrank_eq_one_iff_of_nonzero' (𝟙 (S a)) (id_ne_zero 𝕜 S hEnd a)).1 (hEnd a) f)

theorem scal_smul {a : A} (f : S a ⟶ S a) : scal 𝕜 S hEnd f • 𝟙 (S a) = f :=
  Classical.choose_spec
    ((finrank_eq_one_iff_of_nonzero' (𝟙 (S a)) (id_ne_zero 𝕜 S hEnd a)).1 (hEnd a) f)

theorem scal_eq {a : A} (f : S a ⟶ S a) (t : 𝕜) (h : f = t • 𝟙 (S a)) :
    scal 𝕜 S hEnd f = t :=
  smul_left_injective 𝕜 (id_ne_zero 𝕜 S hEnd a) ((scal_smul 𝕜 S hEnd f).trans h)

theorem scal_ne_zero {a : A} (f : S a ⟶ S a) [IsIso f] : scal 𝕜 S hEnd f ≠ 0 := by
  intro h0
  have hf : f = 0 := by rw [← scal_smul 𝕜 S hEnd f, h0, zero_smul]
  apply id_ne_zero 𝕜 S hEnd a
  calc 𝟙 (S a) = inv f ≫ f := (IsIso.inv_hom_id f).symm
    _ = inv f ≫ 0 := congrArg (fun k => inv f ≫ k) hf
    _ = 0 := Limits.comp_zero

theorem scal_smul_eq {a : A} (f : S a ⟶ S a) (r : 𝕜) :
    scal 𝕜 S hEnd (r • f) = r * scal 𝕜 S hEnd f :=
  scal_eq 𝕜 S hEnd _ _ (by rw [← smul_smul, scal_smul])

include hEnd in
/-- Cancellation of a scalar against an isomorphism into some `S y`. -/
theorem smul_cancel {X : C} {y : A} (M : X ⟶ S y) [IsIso M] {s t : 𝕜} (h : s • M = t • M) :
    s = t := by
  have hM : M ≠ 0 := by
    intro h0
    apply id_ne_zero 𝕜 S hEnd y
    calc 𝟙 (S y) = inv M ≫ M := (IsIso.inv_hom_id M).symm
      _ = inv M ≫ 0 := congrArg (fun k => inv M ≫ k) h0
      _ = 0 := Limits.comp_zero
  exact smul_left_injective 𝕜 hM h

end Scalar

variable (φ : ∀ a b : A, S a ⊗ S b ≅ S (a + b))

section Transport

omit [Preadditive C] [MonoidalPreadditive C] in
theorem natR {x y : A} (h : x = y) (d : A) :
    eqToHom (congrArg S h) ▷ S d ≫ (φ y d).hom =
      (φ x d).hom ≫ eqToHom (congrArg S (congrArg (· + d) h)) := by
  subst h
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
theorem natL (a : A) {x y : A} (h : x = y) :
    S a ◁ eqToHom (congrArg S h) ≫ (φ a y).hom =
      (φ a x).hom ≫ eqToHom (congrArg S (congrArg (a + ·) h)) := by
  subst h
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
theorem natR_assoc {x y : A} (h : x = y) (d : A) {Z : C} (k : S (y + d) ⟶ Z) :
    eqToHom (congrArg S h) ▷ S d ≫ (φ y d).hom ≫ k =
      (φ x d).hom ≫ eqToHom (congrArg S (congrArg (· + d) h)) ≫ k := by
  subst h
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
theorem natL_assoc (a : A) {x y : A} (h : x = y) {Z : C} (k : S (a + y) ⟶ Z) :
    S a ◁ eqToHom (congrArg S h) ≫ (φ a y).hom ≫ k =
      (φ a x).hom ≫ eqToHom (congrArg S (congrArg (a + ·) h)) ≫ k := by
  subst h
  simp

end Transport

section Associator

/-- The associator endomorphism of `S ((a + b) + c)`. -/
noncomputable def ωEnd (a b c : A) : S (a + b + c) ⟶ S (a + b + c) :=
  (φ (a + b) c).inv ≫ (φ a b).inv ▷ S c ≫ (α_ (S a) (S b) (S c)).hom ≫ S a ◁ (φ b c).hom ≫
    (φ a (b + c)).hom ≫ eqToHom (congrArg S (add_assoc a b c).symm)

instance (a b c : A) : IsIso (ωEnd S φ a b c) := by
  unfold ωEnd
  infer_instance

/-- The associator scalar `ω(a,b,c)`. -/
noncomputable def ωs (a b c : A) : 𝕜 := scal 𝕜 S hEnd (ωEnd S φ a b c)

theorem ωs_ne_zero (a b c : A) : ωs 𝕜 S hEnd φ a b c ≠ 0 :=
  scal_ne_zero 𝕜 S hEnd _

theorem ω_rel (a b c : A) :
    (α_ (S a) (S b) (S c)).hom ≫ S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom =
      ωs 𝕜 S hEnd φ a b c • ((φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫
        eqToHom (congrArg S (add_assoc a b c))) := by
  have h := scal_smul 𝕜 S hEnd (ωEnd S φ a b c)
  calc _ = (φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫ ωEnd S φ a b c ≫
        eqToHom (congrArg S (add_assoc a b c)) := by
        simp [ωEnd]
    _ = _ := by
        rw [← h]
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
        rfl

theorem ω_rel_assoc (a b c : A) {Z : C} (h : S (a + (b + c)) ⟶ Z) :
    (α_ (S a) (S b) (S c)).hom ≫ S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom ≫ h =
      ωs 𝕜 S hEnd φ a b c • ((φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫
        eqToHom (congrArg S (add_assoc a b c)) ≫ h) := by
  have := congrArg (· ≫ h) (ω_rel 𝕜 S hEnd φ a b c)
  simpa only [Category.assoc, Linear.smul_comp] using this

theorem ω_rel_inv (a b c : A) :
    (α_ (S a) (S b) (S c)).inv ≫ (φ a b).hom ▷ S c ≫ (φ (a + b) c).hom =
      (ωs 𝕜 S hEnd φ a b c)⁻¹ • (S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom ≫
        eqToHom (congrArg S (add_assoc a b c).symm)) := by
  have hω := ωs_ne_zero 𝕜 S hEnd φ a b c
  have h := ω_rel 𝕜 S hEnd φ a b c
  calc _ = (ωs 𝕜 S hEnd φ a b c)⁻¹ • (ωs 𝕜 S hEnd φ a b c • ((α_ (S a) (S b) (S c)).inv ≫
        (φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫ eqToHom (congrArg S (add_assoc a b c)) ≫
          eqToHom (congrArg S (add_assoc a b c).symm))) := by
        rw [smul_smul, inv_mul_cancel₀ hω, one_smul]
        simp
    _ = _ := by
        congr 1
        rw [← Linear.comp_smul]
        have h' := congrArg (· ≫ eqToHom (congrArg S (add_assoc a b c).symm)) h
        simp only [Category.assoc, Linear.smul_comp] at h'
        rw [← h']
        simp

theorem ω_rel_inv_assoc (a b c : A) {Z : C} (h : S (a + b + c) ⟶ Z) :
    (α_ (S a) (S b) (S c)).inv ≫ (φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫ h =
      (ωs 𝕜 S hEnd φ a b c)⁻¹ • (S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom ≫
        eqToHom (congrArg S (add_assoc a b c).symm) ≫ h) := by
  have := congrArg (· ≫ h) (ω_rel_inv 𝕜 S hEnd φ a b c)
  simpa only [Category.assoc, Linear.smul_comp] using this

/-- **Pentagon ⇒ 3-cocycle**: `ω(a,b,c) ω(a,b+c,d) ω(b,c,d) = ω(a+b,c,d) ω(a,b,c+d)`. -/
theorem pentagon_scalar (a b c d : A) :
    ωs 𝕜 S hEnd φ a b c * ωs 𝕜 S hEnd φ a (b + c) d * ωs 𝕜 S hEnd φ b c d =
      ωs 𝕜 S hEnd φ (a + b) c d * ωs 𝕜 S hEnd φ a b (c + d) := by
  have hR : (α_ (S a ⊗ S b) (S c) (S d)).hom ≫ (α_ (S a) (S b) (S c ⊗ S d)).hom ≫
      S a ◁ (S b ◁ (φ c d).hom ≫ (φ b (c + d)).hom) ≫ (φ a (b + (c + d))).hom =
        (ωs 𝕜 S hEnd φ a b (c + d) * ωs 𝕜 S hEnd φ (a + b) c d) •
          (((φ a b).hom ▷ S c) ▷ S d ≫ (φ (a + b) c).hom ▷ S d ≫ (φ (a + b + c) d).hom ≫
            eqToHom (congrArg S (add_assoc (a + b) c d)) ≫
              eqToHom (congrArg S (add_assoc a b (c + d)))) := by
    rw [MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.associator_naturality_right_assoc, ω_rel 𝕜 S hEnd φ, Linear.comp_smul,
      Linear.comp_smul, MonoidalCategory.whisker_exchange_assoc,
      ← MonoidalCategory.associator_naturality_left_assoc, ω_rel_assoc 𝕜 S hEnd φ, Linear.comp_smul,
      smul_smul]
  have hL : (α_ (S a) (S b) (S c)).hom ▷ S d ≫ (α_ (S a) (S b ⊗ S c) (S d)).hom ≫
      S a ◁ (α_ (S b) (S c) (S d)).hom ≫
        S a ◁ (S b ◁ (φ c d).hom ≫ (φ b (c + d)).hom) ≫ (φ a (b + (c + d))).hom =
        (ωs 𝕜 S hEnd φ b c d * ωs 𝕜 S hEnd φ a (b + c) d * ωs 𝕜 S hEnd φ a b c) •
          (((φ a b).hom ▷ S c) ▷ S d ≫ (φ (a + b) c).hom ▷ S d ≫ (φ (a + b + c) d).hom ≫
            eqToHom (congrArg S (congrArg (· + d) (add_assoc a b c))) ≫
              eqToHom (congrArg S (add_assoc a (b + c) d)) ≫
                eqToHom (congrArg S (congrArg (a + ·) (add_assoc b c d)))) := by
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ω_rel 𝕜 S hEnd φ, MonoidalLinear.whiskerLeft_smul (R := 𝕜),
      Linear.smul_comp, Linear.comp_smul, Linear.comp_smul,
      MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
      natL S φ a (add_assoc b c d), ← MonoidalCategory.associator_naturality_middle_assoc, ω_rel_assoc 𝕜 S hEnd φ,
      Linear.comp_smul, Linear.comp_smul, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, Category.assoc, ω_rel 𝕜 S hEnd φ,
      MonoidalLinear.smul_whiskerRight (R := 𝕜), Linear.smul_comp,
      MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.comp_whiskerRight_assoc,
      natR_assoc S φ (add_assoc a b c) d,
      smul_smul, smul_smul]
  have hpent : (α_ (S a) (S b) (S c)).hom ▷ S d ≫ (α_ (S a) (S b ⊗ S c) (S d)).hom ≫
      S a ◁ (α_ (S b) (S c) (S d)).hom ≫
        S a ◁ (S b ◁ (φ c d).hom ≫ (φ b (c + d)).hom) ≫ (φ a (b + (c + d))).hom =
      (α_ (S a ⊗ S b) (S c) (S d)).hom ≫ (α_ (S a) (S b) (S c ⊗ S d)).hom ≫
        S a ◁ (S b ◁ (φ c d).hom ≫ (φ b (c + d)).hom) ≫ (φ a (b + (c + d))).hom := by
    rw [MonoidalCategory.pentagon_assoc]
  have key := hL.symm.trans (hpent.trans hR)
  simp only [eqToHom_trans] at key
  have key' := smul_cancel 𝕜 S hEnd _ key
  linear_combination key'

end Associator

section Braiding

variable [BraidedCategory C]

/-- The braiding endomorphism of `S (a + b)`. -/
noncomputable def cEnd (a b : A) : S (a + b) ⟶ S (a + b) :=
  (φ a b).inv ≫ (β_ (S a) (S b)).hom ≫ (φ b a).hom ≫ eqToHom (congrArg S (add_comm b a))

instance (a b : A) : IsIso (cEnd S φ a b) := by
  unfold cEnd
  infer_instance

/-- The braiding scalar `c(a,b)`. -/
noncomputable def cs (a b : A) : 𝕜 := scal 𝕜 S hEnd (cEnd S φ a b)

theorem cs_ne_zero (a b : A) : cs 𝕜 S hEnd φ a b ≠ 0 :=
  scal_ne_zero 𝕜 S hEnd _

theorem c_rel (a b : A) :
    (β_ (S a) (S b)).hom ≫ (φ b a).hom =
      cs 𝕜 S hEnd φ a b • ((φ a b).hom ≫ eqToHom (congrArg S (add_comm a b))) := by
  have h := scal_smul 𝕜 S hEnd (cEnd S φ a b)
  calc _ = (φ a b).hom ≫ cEnd S φ a b ≫ eqToHom (congrArg S (add_comm a b)) := by
        simp [cEnd]
    _ = _ := by
        rw [← h]
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
        rfl

theorem c_rel_assoc (a b : A) {Z : C} (h : S (b + a) ⟶ Z) :
    (β_ (S a) (S b)).hom ≫ (φ b a).hom ≫ h =
      cs 𝕜 S hEnd φ a b • ((φ a b).hom ≫ eqToHom (congrArg S (add_comm a b)) ≫ h) := by
  have := congrArg (· ≫ h) (c_rel 𝕜 S hEnd φ a b)
  simpa only [Category.assoc, Linear.smul_comp] using this

/-- **First hexagon**: `ω(a,b,c) c(a,b+c) ω(b,c,a) = c(a,b) ω(b,a,c) c(a,c)`. -/
theorem hexagon_forward_scalar (a b c : A) :
    ωs 𝕜 S hEnd φ a b c * cs 𝕜 S hEnd φ a (b + c) * ωs 𝕜 S hEnd φ b c a =
      cs 𝕜 S hEnd φ a b * ωs 𝕜 S hEnd φ b a c * cs 𝕜 S hEnd φ a c := by
  have hL : (α_ (S a) (S b) (S c)).hom ≫ (β_ (S a) (S b ⊗ S c)).hom ≫
      (α_ (S b) (S c) (S a)).hom ≫ S b ◁ (φ c a).hom ≫ (φ b (c + a)).hom =
        (ωs 𝕜 S hEnd φ b c a * cs 𝕜 S hEnd φ a (b + c) * ωs 𝕜 S hEnd φ a b c) •
          ((φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫ eqToHom (congrArg S (add_assoc a b c)) ≫
            eqToHom (congrArg S (add_comm a (b + c))) ≫
              eqToHom (congrArg S (add_assoc b c a))) := by
    rw [ω_rel 𝕜 S hEnd φ, Linear.comp_smul, Linear.comp_smul,
      ← BraidedCategory.braiding_naturality_right_assoc, c_rel_assoc 𝕜 S hEnd φ,
      Linear.comp_smul, Linear.comp_smul, ω_rel_assoc 𝕜 S hEnd φ, smul_smul, smul_smul]
  have hR : (β_ (S a) (S b)).hom ▷ S c ≫ (α_ (S b) (S a) (S c)).hom ≫
      S b ◁ (β_ (S a) (S c)).hom ≫ S b ◁ (φ c a).hom ≫ (φ b (c + a)).hom =
        (cs 𝕜 S hEnd φ a c * ωs 𝕜 S hEnd φ b a c * cs 𝕜 S hEnd φ a b) •
          ((φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫
            eqToHom (congrArg S (congrArg (· + c) (add_comm a b))) ≫
              eqToHom (congrArg S (add_assoc b a c)) ≫
                eqToHom (congrArg S (congrArg (b + ·) (add_comm a c)))) := by
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, c_rel 𝕜 S hEnd φ,
      MonoidalLinear.whiskerLeft_smul (R := 𝕜), Linear.smul_comp, Linear.comp_smul,
      Linear.comp_smul, MonoidalCategory.whiskerLeft_comp_assoc, natL S φ b (add_comm a c),
      ω_rel_assoc 𝕜 S hEnd φ, Linear.comp_smul, ← MonoidalCategory.comp_whiskerRight_assoc,
      c_rel 𝕜 S hEnd φ, MonoidalLinear.smul_whiskerRight (R := 𝕜), Linear.smul_comp,
      MonoidalCategory.comp_whiskerRight_assoc, natR_assoc S φ (add_comm a b) c, smul_smul,
      smul_smul]
  have hhex : (α_ (S a) (S b) (S c)).hom ≫ (β_ (S a) (S b ⊗ S c)).hom ≫
      (α_ (S b) (S c) (S a)).hom ≫ S b ◁ (φ c a).hom ≫ (φ b (c + a)).hom =
      (β_ (S a) (S b)).hom ▷ S c ≫ (α_ (S b) (S a) (S c)).hom ≫
        S b ◁ (β_ (S a) (S c)).hom ≫ S b ◁ (φ c a).hom ≫ (φ b (c + a)).hom := by
    rw [BraidedCategory.hexagon_forward_assoc]
  have key := hL.symm.trans (hhex.trans hR)
  simp only [eqToHom_trans] at key
  have key' := smul_cancel 𝕜 S hEnd _ key
  linear_combination key'

/-- **Second hexagon**:
`ω(a,b,c)⁻¹ c(a+b,c) ω(c,a,b)⁻¹ = c(b,c) ω(a,c,b)⁻¹ c(a,c)`. -/
theorem hexagon_reverse_scalar (a b c : A) :
    (ωs 𝕜 S hEnd φ a b c)⁻¹ * cs 𝕜 S hEnd φ (a + b) c * (ωs 𝕜 S hEnd φ c a b)⁻¹ =
      cs 𝕜 S hEnd φ b c * (ωs 𝕜 S hEnd φ a c b)⁻¹ * cs 𝕜 S hEnd φ a c := by
  have hL : (α_ (S a) (S b) (S c)).inv ≫ (β_ (S a ⊗ S b) (S c)).hom ≫
      (α_ (S c) (S a) (S b)).inv ≫ (φ c a).hom ▷ S b ≫ (φ (c + a) b).hom =
        ((ωs 𝕜 S hEnd φ c a b)⁻¹ * cs 𝕜 S hEnd φ (a + b) c * (ωs 𝕜 S hEnd φ a b c)⁻¹) •
          (S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom ≫
            eqToHom (congrArg S (add_assoc a b c).symm) ≫
              eqToHom (congrArg S (add_comm (a + b) c)) ≫
                eqToHom (congrArg S (add_assoc c a b).symm)) := by
    rw [ω_rel_inv 𝕜 S hEnd φ, Linear.comp_smul, Linear.comp_smul,
      ← BraidedCategory.braiding_naturality_left_assoc, c_rel_assoc 𝕜 S hEnd φ,
      Linear.comp_smul, Linear.comp_smul, ω_rel_inv_assoc 𝕜 S hEnd φ, smul_smul, smul_smul]
  have hR : S a ◁ (β_ (S b) (S c)).hom ≫ (α_ (S a) (S c) (S b)).inv ≫
      (β_ (S a) (S c)).hom ▷ S b ≫ (φ c a).hom ▷ S b ≫ (φ (c + a) b).hom =
        (cs 𝕜 S hEnd φ a c * (ωs 𝕜 S hEnd φ a c b)⁻¹ * cs 𝕜 S hEnd φ b c) •
          (S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom ≫
            eqToHom (congrArg S (congrArg (a + ·) (add_comm b c))) ≫
              eqToHom (congrArg S (add_assoc a c b).symm) ≫
                eqToHom (congrArg S (congrArg (· + b) (add_comm a c)))) := by
    rw [← MonoidalCategory.comp_whiskerRight_assoc, c_rel 𝕜 S hEnd φ,
      MonoidalLinear.smul_whiskerRight (R := 𝕜), Linear.smul_comp, Linear.comp_smul,
      Linear.comp_smul, MonoidalCategory.comp_whiskerRight_assoc, natR S φ (add_comm a c) b,
      ω_rel_inv_assoc 𝕜 S hEnd φ, Linear.comp_smul, ← MonoidalCategory.whiskerLeft_comp_assoc,
      c_rel 𝕜 S hEnd φ, MonoidalLinear.whiskerLeft_smul (R := 𝕜), Linear.smul_comp,
      MonoidalCategory.whiskerLeft_comp_assoc, natL_assoc S φ a (add_comm b c), smul_smul,
      smul_smul]
  have hhex : (α_ (S a) (S b) (S c)).inv ≫ (β_ (S a ⊗ S b) (S c)).hom ≫
      (α_ (S c) (S a) (S b)).inv ≫ (φ c a).hom ▷ S b ≫ (φ (c + a) b).hom =
      S a ◁ (β_ (S b) (S c)).hom ≫ (α_ (S a) (S c) (S b)).inv ≫
        (β_ (S a) (S c)).hom ▷ S b ≫ (φ c a).hom ▷ S b ≫ (φ (c + a) b).hom := by
    rw [BraidedCategory.hexagon_reverse_assoc]
  have key := hL.symm.trans (hhex.trans hR)
  simp only [eqToHom_trans] at key
  have key' := smul_cancel 𝕜 S hEnd _ key
  linear_combination key'

end Braiding

section Rescale

/-- Rescaling the chosen isomorphisms: `φ'_{a,b} = g(a,b) φ_{a,b}`. -/
@[simps]
noncomputable def scaleφ (g : A → A → 𝕜ˣ) (a b : A) : S a ⊗ S b ≅ S (a + b) where
  hom := (g a b : 𝕜) • (φ a b).hom
  inv := ((g a b : 𝕜))⁻¹ • (φ a b).inv
  hom_inv_id := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.hom_inv_id,
      mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  inv_hom_id := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.inv_hom_id,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]

/-- **Changing `φ` changes `ω` by a coboundary**:
`ω'(a,b,c) g(a,b) g(a+b,c) = ω(a,b,c) g(b,c) g(a,b+c)`. -/
theorem ωs_scale (g : A → A → 𝕜ˣ) (a b c : A) :
    ωs 𝕜 S hEnd (scaleφ 𝕜 S φ g) a b c * ((g a b : 𝕜) * g (a + b) c) =
      ωs 𝕜 S hEnd φ a b c * ((g b c : 𝕜) * g a (b + c)) := by
  have hE : ωEnd S (scaleφ 𝕜 S φ g) a b c =
      (((g (a + b) c : 𝕜))⁻¹ * ((g a b : 𝕜))⁻¹ * g b c * g a (b + c)) • ωEnd S φ a b c := by
    simp only [ωEnd, scaleφ_hom, scaleφ_inv, Linear.smul_comp, Linear.comp_smul,
      MonoidalLinear.smul_whiskerRight (R := 𝕜), MonoidalLinear.whiskerLeft_smul (R := 𝕜),
      smul_smul]
    congr 1
    ring
  have h1 := Units.ne_zero (g a b)
  have h2 := Units.ne_zero (g (a + b) c)
  unfold ωs
  rw [hE, scal_smul_eq]
  field_simp

end Rescale

section RescaleBraiding

variable [BraidedCategory C]

/-- **Changing `φ` changes `c` by a coboundary**: `c'(a,b) g(a,b) = c(a,b) g(b,a)`. -/
theorem cs_scale (g : A → A → 𝕜ˣ) (a b : A) :
    cs 𝕜 S hEnd (scaleφ 𝕜 S φ g) a b * (g a b : 𝕜) = cs 𝕜 S hEnd φ a b * (g b a : 𝕜) := by
  have hE : cEnd S (scaleφ 𝕜 S φ g) a b = (((g a b : 𝕜))⁻¹ * g b a) • cEnd S φ a b := by
    simp only [cEnd, scaleφ_hom, scaleφ_inv, Linear.smul_comp, Linear.comp_smul, smul_smul]
    congr 1
    ring
  have h1 := Units.ne_zero (g a b)
  unfold cs
  rw [hE, scal_smul_eq]
  field_simp

/-- The twist: if the self-braiding of `S a` is trivial, `c(a,a) = 1` (for any `φ`). -/
theorem cs_self_eq_one (a : A) (hθ : (β_ (S a) (S a)).hom = 𝟙 _) : cs 𝕜 S hEnd φ a a = 1 := by
  apply scal_eq
  simp [cEnd, hθ]

end RescaleBraiding


end PointedCocycle

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PointedCocycle.ω_rel
#print axioms HaagerupIzumi.C8.PointedCocycle.c_rel
#print axioms HaagerupIzumi.C8.PointedCocycle.pentagon_scalar
#print axioms HaagerupIzumi.C8.PointedCocycle.hexagon_forward_scalar
#print axioms HaagerupIzumi.C8.PointedCocycle.hexagon_reverse_scalar
#print axioms HaagerupIzumi.C8.PointedCocycle.ωs_scale
#print axioms HaagerupIzumi.C8.PointedCocycle.cs_scale
#print axioms HaagerupIzumi.C8.PointedCocycle.cs_self_eq_one
