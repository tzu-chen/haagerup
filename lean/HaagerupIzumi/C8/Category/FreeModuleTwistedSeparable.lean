module

public import HaagerupIzumi.C8.Category.FreeModuleGraded
public import HaagerupIzumi.C8.Category.FreeModuleSeparable

@[expose] public section

/-! # The separability section of a twisted group algebra (`H/B`)

The separability input of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`,
lines 3345–3347: "separability makes every module a summand of a free module"), made
concrete.  `Category/FreeModuleSeparable.lean` proves that every module is a retract of a
free module given a `SeparabilitySection A`; here such a section is constructed for a twisted
group algebra `A ≅ ⊕_{c ∈ K} T c` of a finite group `K` (`TwistedGroupAlgebra`,
`Category/FreeModuleGraded.lean`) in a `𝕜`-linear monoidal category with `|K|` invertible in
`𝕜`, which is the shape of `H/B ≅ ⊕_{ℓ ∈ L₊} ℓ` with `|L₊| = 3`.

* `sepComp D c = (homogMulIso D c)⁻¹ ≫ (incl_c ⊗ A) : A ⟶ A ⊗ A`, `a ↦ t_c ⊗ t_c⁻¹ a`; it is a
  section of the multiplication (`sepComp_mul`) and right `A`-linear (`mul_sepComp`).
* `whiskerLeft_sepComp_mul`, `incl_mul_homogMulInv`: for `x ∈ T a`,
  `x · ψ_c(y) = ψ_{a+c}(x y)` (associativity of `A` and the homogeneous multiplications).
* `twistedSep D 𝕜 = |K|⁻¹ ∑_c sepComp D c` (`a ↦ |K|⁻¹ ∑_c t_c ⊗ t_c⁻¹ a`):
  `twistedSep_mul` (a section of `μ`), `mul_twistedSep_right` and `mul_twistedSep_left`
  (right and left `A`-linearity, the latter by reindexing `c ↦ a + c`);
  `twistedSeparabilitySection`: the resulting `SeparabilitySection A`.
* `retractFree_twisted`, `retractFree_Lplus`: every right module over such an algebra, in
  particular over `H/B ≅ ⊕_{c ∈ ℤ/3} S (c, c)` when `3 ≠ 0` in `𝕜`, is a retract of a free
  module.

Hypotheses: the twisted-group-algebra structure `D` (as in `Category/FreeModuleGraded.lean`:
the multiplication maps `T c ⊗ T d` isomorphically onto the summand `T (c + d)`) and
`(|K| : 𝕜) ≠ 0`.  No braiding or commutativity is used.  No external-theorem or certificate
inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

variable [Preadditive C] [HasFiniteBiproducts C] [MonoidalPreadditive C] {A : Mon C}
  {K : Type} [Fintype K] [AddGroup K] {T : K → C} {hA : A.X ≅ ⨁ T}
  (D : TwistedGroupAlgebra hA)

section Components

/-- `ψ_c : a ↦ t_c ⊗ t_c⁻¹ a`, the `c`-th summand of the separability section. -/
noncomputable def sepComp (c : K) : A.X ⟶ A.X ⊗ A.X :=
  homogMulInv D c ≫ summandIncl hA c ▷ A.X

omit [MonoidalPreadditive C] in
theorem sepComp_mul (c : K) : sepComp D c ≫ μ[A.X] = 𝟙 A.X := by
  rw [sepComp, Category.assoc]
  exact homogMulInv_hom D c

/-- The inverse of the homogeneous multiplication is a map of right modules. -/
theorem mul_homogMulInv (c : K) :
    μ[A.X] ≫ homogMulInv D c =
      homogMulInv D c ▷ A.X ≫ (α_ (T c) A.X A.X).hom ≫ T c ◁ μ[A.X] :=
  (freeHomogIso D c).inv.act_hom

/-- `ψ_c` is right `A`-linear: `ψ_c(a b) = ψ_c(a) b`. -/
theorem mul_sepComp (c : K) :
    μ[A.X] ≫ sepComp D c = sepComp D c ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫ A.X ◁ μ[A.X] := by
  rw [sepComp, reassoc_of% (mul_homogMulInv D c), MonoidalCategory.whisker_exchange,
    ← MonoidalCategory.associator_naturality_left_assoc,
    MonoidalCategory.comp_whiskerRight_assoc]

omit [MonoidalPreadditive C] in
/-- `x · ψ_c(y)`, for `x ∈ T a`, is `(x t_c) ⊗ t_c⁻¹ y` with `x t_c ∈ T (a + c)`. -/
theorem whiskerLeft_sepComp_mul (a c : K) :
    T a ◁ sepComp D c ≫ summandIncl hA a ▷ (A.X ⊗ A.X) ≫ (α_ A.X A.X A.X).inv ≫
        μ[A.X] ▷ A.X =
      (T a ◁ homogMulInv D c ≫ (α_ (T a) (T c) A.X).inv ≫ (D.m a c).hom ▷ A.X) ≫
        summandIncl hA (a + c) ▷ A.X := by
  calc T a ◁ sepComp D c ≫ summandIncl hA a ▷ (A.X ⊗ A.X) ≫ (α_ A.X A.X A.X).inv ≫
        μ[A.X] ▷ A.X
      = T a ◁ homogMulInv D c ≫ (α_ (T a) (T c) A.X).inv ≫
          ((summandIncl hA a ⊗ₘ summandIncl hA c) ≫ μ[A.X]) ▷ A.X := by
        rw [sepComp, MonoidalCategory.tensorHom_def']
        monoidal
    _ = _ := by
        rw [D.mul_eq, MonoidalCategory.comp_whiskerRight]
        simp only [Category.assoc]

/-- `ψ_{a+c}(x y) = (x t_c) ⊗ t_c⁻¹ y` for `x ∈ T a` (associativity of `A`). -/
theorem incl_mul_homogMulInv (a c : K) :
    (summandIncl hA a ▷ A.X ≫ μ[A.X]) ≫ homogMulInv D (a + c) =
      T a ◁ homogMulInv D c ≫ (α_ (T a) (T c) A.X).inv ≫ (D.m a c).hom ▷ A.X := by
  refine (Iso.comp_inv_eq (homogMulIso D (a + c))).2 ?_
  calc summandIncl hA a ▷ A.X ≫ μ[A.X]
      = summandIncl hA a ▷ A.X ≫
          A.X ◁ (homogMulInv D c ≫ summandIncl hA c ▷ A.X ≫ μ[A.X]) ≫ μ[A.X] := by
        rw [homogMulInv_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    _ = T a ◁ homogMulInv D c ≫ summandIncl hA a ▷ (T c ⊗ A.X) ≫
          A.X ◁ (summandIncl hA c ▷ A.X) ≫ A.X ◁ μ[A.X] ≫ μ[A.X] := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        rw [← MonoidalCategory.whisker_exchange_assoc]
    _ = T a ◁ homogMulInv D c ≫ (α_ (T a) (T c) A.X).inv ≫
          ((summandIncl hA a ⊗ₘ summandIncl hA c) ≫ μ[A.X]) ▷ A.X ≫ μ[A.X] := by
        rw [MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight_assoc,
          MonObj.mul_assoc A.X]
        monoidal
    _ = (T a ◁ homogMulInv D c ≫ (α_ (T a) (T c) A.X).inv ≫ (D.m a c).hom ▷ A.X) ≫
          summandIncl hA (a + c) ▷ A.X ≫ μ[A.X] := by
        rw [D.mul_eq]
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]

end Components

section Separable

variable (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]

/-- The separability section `sep = |K|⁻¹ ∑_c ψ_c`, `a ↦ |K|⁻¹ ∑_c t_c ⊗ t_c⁻¹ a`. -/
noncomputable def twistedSep : A.X ⟶ A.X ⊗ A.X :=
  ((Fintype.card K : 𝕜)⁻¹) • ∑ c, sepComp D c

omit [MonoidalPreadditive C] [MonoidalLinear 𝕜 C] in
/-- `μ ∘ sep = 𝟙`. -/
theorem twistedSep_mul (hK : (Fintype.card K : 𝕜) ≠ 0) :
    twistedSep D 𝕜 ≫ μ[A.X] = 𝟙 A.X := by
  rw [twistedSep, Linear.smul_comp, Preadditive.sum_comp]
  simp only [sepComp_mul, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (R := 𝕜), smul_smul, inv_mul_cancel₀ hK, one_smul]

/-- Right `A`-linearity: `sep(a b) = sep(a) b`. -/
theorem mul_twistedSep_right :
    μ[A.X] ≫ twistedSep D 𝕜 =
      twistedSep D 𝕜 ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫ A.X ◁ μ[A.X] := by
  simp only [twistedSep, Linear.comp_smul, Preadditive.comp_sum,
    MonoidalLinear.smul_whiskerRight, sum_whiskerRight, Linear.smul_comp,
    Preadditive.sum_comp, mul_sepComp]

/-- Left `A`-linearity on the summand `T a`: `sep(x b) = x sep(b)` for `x ∈ T a`. -/
theorem summandIncl_mul_twistedSep (a : K) :
    summandIncl hA a ▷ A.X ≫ μ[A.X] ≫ twistedSep D 𝕜 =
      summandIncl hA a ▷ A.X ≫ A.X ◁ twistedSep D 𝕜 ≫ (α_ A.X A.X A.X).inv ≫
        μ[A.X] ▷ A.X := by
  have key : ∀ c, summandIncl hA a ▷ A.X ≫ A.X ◁ sepComp D c ≫ (α_ A.X A.X A.X).inv ≫
      μ[A.X] ▷ A.X = summandIncl hA a ▷ A.X ≫ μ[A.X] ≫ sepComp D (a + c) := by
    intro c
    rw [← MonoidalCategory.whisker_exchange_assoc, whiskerLeft_sepComp_mul,
      ← incl_mul_homogMulInv]
    simp only [sepComp, Category.assoc]
  simp only [twistedSep, Linear.comp_smul, Preadditive.comp_sum,
    MonoidalLinear.whiskerLeft_smul, whiskerLeft_sum, Linear.smul_comp, Preadditive.sum_comp,
    key]
  congr 1
  exact (Equiv.sum_comp (Equiv.addLeft a)
    (fun c => summandIncl hA a ▷ A.X ≫ μ[A.X] ≫ sepComp D c)).symm

/-- Left `A`-linearity: `sep(a b) = a sep(b)`. -/
theorem mul_twistedSep_left :
    μ[A.X] ≫ twistedSep D 𝕜 =
      A.X ◁ twistedSep D 𝕜 ≫ (α_ A.X A.X A.X).inv ≫ μ[A.X] ▷ A.X := by
  have htot : ∑ a, summandProj hA a ▷ A.X ≫ summandIncl hA a ▷ A.X = 𝟙 (A.X ⊗ A.X) := by
    rw [← MonoidalCategory.id_whiskerRight, ← summand_total hA, sum_whiskerRight]
    simp only [MonoidalCategory.comp_whiskerRight]
  calc μ[A.X] ≫ twistedSep D 𝕜
      = (∑ a, summandProj hA a ▷ A.X ≫ summandIncl hA a ▷ A.X) ≫ μ[A.X] ≫
          twistedSep D 𝕜 := by
        rw [htot, Category.id_comp]
    _ = (∑ a, summandProj hA a ▷ A.X ≫ summandIncl hA a ▷ A.X) ≫ A.X ◁ twistedSep D 𝕜 ≫
          (α_ A.X A.X A.X).inv ≫ μ[A.X] ▷ A.X := by
        simp only [Preadditive.sum_comp, Category.assoc, summandIncl_mul_twistedSep]
    _ = A.X ◁ twistedSep D 𝕜 ≫ (α_ A.X A.X A.X).inv ≫ μ[A.X] ▷ A.X := by
        rw [htot, Category.id_comp]

/-- **The separability section of a twisted group algebra** (`|K|` invertible in `𝕜`). -/
noncomputable def twistedSeparabilitySection (hK : (Fintype.card K : 𝕜) ≠ 0) :
    SeparabilitySection A where
  sep := twistedSep D 𝕜
  sep_mul := twistedSep_mul D 𝕜 hK
  mul_sep_right := mul_twistedSep_right D 𝕜
  mul_sep_left := mul_twistedSep_left D 𝕜

/-- Every right module over a twisted group algebra (`|K|` invertible) is a retract of a free
module. -/
noncomputable def retractFree_twisted (hK : (Fintype.card K : 𝕜) ≠ 0) (M : RightMod A) :
    Retract M (free A M.X) :=
  retractFree (twistedSeparabilitySection D 𝕜 hK) M

end Separable

/-- **Separability makes every module a summand of a free module, for `H/B`** (manuscript
lines 3345–3347): if `A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` is a twisted group algebra of `L₊` and
`3 ≠ 0` in `𝕜`, every right `A`-module is a retract of a free module. -/
theorem retractFree_Lplus (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]
    {S : ZMod 3 × ZMod 3 → C} {hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)}
    (D : TwistedGroupAlgebra hA) (h3 : (3 : 𝕜) ≠ 0) (M : RightMod A) :
    Nonempty (Retract M (free A M.X)) := by
  have hK : (Fintype.card (ZMod 3) : 𝕜) ≠ 0 := by
    rw [ZMod.card]
    exact_mod_cast h3
  exact ⟨retractFree_twisted D 𝕜 hK M⟩

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.mul_sepComp
#print axioms HaagerupIzumi.C8.RightMod.whiskerLeft_sepComp_mul
#print axioms HaagerupIzumi.C8.RightMod.incl_mul_homogMulInv
#print axioms HaagerupIzumi.C8.RightMod.twistedSep_mul
#print axioms HaagerupIzumi.C8.RightMod.mul_twistedSep_right
#print axioms HaagerupIzumi.C8.RightMod.mul_twistedSep_left
#print axioms HaagerupIzumi.C8.RightMod.twistedSeparabilitySection
#print axioms HaagerupIzumi.C8.RightMod.retractFree_Lplus
