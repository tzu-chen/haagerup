module

public import HaagerupIzumi.C8.Category.FreeModuleAdditive
public import HaagerupIzumi.C8.Category.FreeModuleTensor

@[expose] public section

/-! # `ℓ ⊗ A ≅ A` for `ℓ ∈ L₊`; every free module is induced from `L₋`

Step "Every free module is a direct sum of these three simple modules" of the proof of
`L_untwisted` (manuscript `haagerup_c8_expanded.tex`, lines 3345–3346).  There `A = H/B` is,
as an object of the pointed category `Rep(B)`, the sum `⊕_{ℓ ∈ L₊} ℓ` of the invertibles of
the isotropic line `L₊`, and a free module `v ⊗ A` with `v = x + ℓ`, `x ∈ L₋`, `ℓ ∈ L₊`, is
`x ⊗ (ℓ ⊗ A) ≅ x ⊗ A` because `ℓ ⊗ A ≅ A` as right `A`-modules.

* `RightMod.regularMod A`: `A` as a right module over itself.
* `summandIncl`, `summandProj`: the inclusions and projections of a decomposition
  `hA : A ≅ ⨁_{c ∈ K} T c`.
* `TwistedGroupAlgebra hA` (hypothesis structure): the multiplication of `A` restricted to
  `T c ⊗ T d` is an isomorphism `m c d : T c ⊗ T d ≅ T (c + d)` followed by the inclusion of
  the summand `T (c + d)`; i.e. `A` is a `K`-graded algebra whose homogeneous multiplications
  are invertible (a twisted group algebra of `K`).
* `homogMulIso hA D c : T c ⊗ A ≅ A`, `x ⊗ a ↦ x a`, with explicit inverse
  `∑_d proj_{c+d} ≫ m(c,d)⁻¹ ≫ (T c ◁ incl_d)`; `freeHomogIso`: it is an isomorphism of right
  `A`-modules `free A (T c) ≅ regularMod A`, **`ℓ ⊗ A ≅ A` for every homogeneous `ℓ`**.
* `freeTensorHomogIso hA D X c : (X ⊗ T c) ⊗ A ≅ X ⊗ A` as right `A`-modules (via
  `tensorLeftObjFreeIso` and `tensorLeftIso`).
* `biproductMapIso`: for an additive functor `F`, isomorphisms `F (X j) ≅ F (Y j)` assemble to
  `F (⨁ X) ≅ F (⨁ Y)` (no biproducts needed in the target).
* `free_iso_Lminus`: for the nine invertibles `S v`, `v ∈ (ℤ/3)²`, with `A ≅ ⊕_{c} S (c, c)`
  a twisted group algebra of `L₊ = {(c, c)}`, every free module `S v ⊗ A` is isomorphic to
  `S (a, -a) ⊗ A` for some `(a, -a) ∈ L₋` (with the arithmetic
  `Weights.coset_Lplus_meets_Lminus_once`); `free_biproduct_iso_Lminus`: every free module on
  a finite direct sum of the `S v` is isomorphic to a free module on a finite direct sum of
  the three `S (a, -a)`, **essential surjectivity of induction from `L₋` onto free modules**.

Hypotheses (structural facts about `Rep(B)` and `H/B`, phrased as such; none is the
conclusion): `hfusion` (the `S v` multiply by the group law of `(ℤ/3)²`), `hA` (`H/B ≅ ⊕_{c}
S (c, c)` as an object), and `D : TwistedGroupAlgebra hA` (the multiplication of `H/B` maps
`S (c, c) ⊗ S (d, d)` isomorphically onto the summand `S (c + d, c + d)`; for the simple-
current extension `H` of `B` this is the non-vanishing `Y(u, z) v ≠ 0` for nonzero `u, v` in a
simple VOA (Dong–Lepowsky 1993, Prop. 11.9), transported to the categorical multiplication
through the Huang–Kirillov–Lepowsky correspondence between VOA extensions and commutative
algebras in `Rep(B)`, together with `Hom(S v ⊗ S w, S u) = 0` for `u ≠ v + w`; see
`Category/TwistedGroupAlgebraOfMul.lean`, which derives `D` from `hmul`).  Not formalized: that every module (not only
every free module) is a sum of the three simple modules, which needs, besides
`retractFree` (`Category/FreeModuleSeparable.lean`), the semisimplicity of `𝒞_A`. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

section General

variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
  {E : Type*} [Category E] [Preadditive E] (F : D ⥤ E) [F.Additive]
  {J : Type} [Fintype J] {X Y : J → D}

/-- Componentwise morphisms `a j : F (X j) ⟶ F (Y j)`, `b j : F (Y j) ⟶ F (X j)` with
`a j ≫ b j = 𝟙` assemble to a left inverse pair on `F (⨁ X)`. -/
theorem sum_components_comp (a : ∀ j, F.obj (X j) ⟶ F.obj (Y j))
    (b : ∀ j, F.obj (Y j) ⟶ F.obj (X j)) (hab : ∀ j, a j ≫ b j = 𝟙 _) :
    (∑ j, F.map (biproduct.π X j) ≫ a j ≫ F.map (biproduct.ι Y j)) ≫
        (∑ k, F.map (biproduct.π Y k) ≫ b k ≫ F.map (biproduct.ι X k)) =
      𝟙 (F.obj (⨁ X)) := by
  rw [Preadditive.sum_comp, ← map_biproduct_total F X]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.comp_sum, Finset.sum_eq_single j]
  · have e1 : F.map (biproduct.ι Y j) ≫ F.map (biproduct.π Y j) = 𝟙 _ := by
      rw [← F.map_comp, biproduct.ι_π_self, F.map_id]
    simp only [Category.assoc]
    rw [reassoc_of% e1, reassoc_of% (hab j)]
  · intro k _ hk
    simp only [Category.assoc, ← Functor.map_comp_assoc, biproduct.ι_π_ne Y (Ne.symm hk),
      Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- An additive functor carries componentwise isomorphisms `F (X j) ≅ F (Y j)` to an
isomorphism `F (⨁ X) ≅ F (⨁ Y)`. -/
noncomputable def biproductMapIso (e : ∀ j, F.obj (X j) ≅ F.obj (Y j)) : F.obj (⨁ X) ≅ F.obj (⨁ Y) where
  hom := ∑ j, F.map (biproduct.π X j) ≫ (e j).hom ≫ F.map (biproduct.ι Y j)
  inv := ∑ k, F.map (biproduct.π Y k) ≫ (e k).inv ≫ F.map (biproduct.ι X k)
  hom_inv_id := sum_components_comp F _ _ fun j => (e j).hom_inv_id
  inv_hom_id := sum_components_comp F _ _ fun j => (e j).inv_hom_id

end General

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section Regular

variable (A : Mon C)

/-- The regular right module: `A` acting on itself by multiplication. -/
def regularMod : RightMod A where
  X := A.X
  act := μ[A.X]
  act_one := MonObj.mul_one A.X
  act_assoc := MonObj.mul_assoc_flip A.X

/-- `X ⊗ A`, with `A` the regular module, is the free module on `X`. -/
def tensorLeftRegularIso (X : C) : tensorLeftObj X (regularMod A) ≅ free A X :=
  isoOfIso (Iso.refl (X ⊗ A.X)) (by
    show ((α_ X A.X A.X).hom ≫ X ◁ μ[A.X]) ≫ 𝟙 (X ⊗ A.X) =
      𝟙 (X ⊗ A.X) ▷ A.X ≫ freeAct A X
    rw [Category.comp_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl)

variable {A}

/-- `X ⊗ -` on isomorphisms of right modules. -/
def tensorLeftIso (X : C) {M N : RightMod A} (e : M ≅ N) :
    tensorLeftObj X M ≅ tensorLeftObj X N :=
  isoOfIso (whiskerLeftIso X ((forget A).mapIso e)) (by
    show ((α_ X M.X A.X).hom ≫ X ◁ M.act) ≫ X ◁ e.hom.hom =
      (X ◁ e.hom.hom) ▷ A.X ≫ (α_ X N.X A.X).hom ≫ X ◁ N.act
    rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, e.hom.act_hom,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.associator_naturality_middle_assoc])

end Regular

section Graded

variable [Preadditive C] [HasFiniteBiproducts C] {A : Mon C} {K : Type} [Fintype K]
  {T : K → C} (hA : A.X ≅ ⨁ T)

/-- The inclusion of the summand `T c` of `A`. -/
noncomputable def summandIncl (c : K) : T c ⟶ A.X := biproduct.ι T c ≫ hA.inv

/-- The projection of `A` onto the summand `T c`. -/
noncomputable def summandProj (c : K) : A.X ⟶ T c := hA.hom ≫ biproduct.π T c

@[reassoc]
theorem summandIncl_proj_self (c : K) : summandIncl hA c ≫ summandProj hA c = 𝟙 (T c) := by
  rw [summandIncl, summandProj, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self]

@[reassoc]
theorem summandIncl_proj_ne {c d : K} (h : c ≠ d) :
    summandIncl hA c ≫ summandProj hA d = 0 := by
  rw [summandIncl, summandProj, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_ne T h]

theorem summand_total : ∑ c, summandProj hA c ≫ summandIncl hA c = 𝟙 A.X := by
  calc ∑ c, summandProj hA c ≫ summandIncl hA c
      = hA.hom ≫ (∑ c, biproduct.π T c ≫ biproduct.ι T c) ≫ hA.inv := by
        simp only [summandProj, summandIncl, Preadditive.sum_comp, Preadditive.comp_sum,
          Category.assoc]
    _ = 𝟙 A.X := by rw [biproduct.total, Category.id_comp, Iso.hom_inv_id]

variable [MonoidalPreadditive C]

theorem whisker_summand_total (X : C) :
    ∑ d, X ◁ summandProj hA d ≫ X ◁ summandIncl hA d = 𝟙 (X ⊗ A.X) := by
  rw [← MonoidalCategory.whiskerLeft_id, ← summand_total hA, whiskerLeft_sum]
  simp only [MonoidalCategory.whiskerLeft_comp]

variable [AddGroup K]

/-- Hypothesis structure: `A ≅ ⨁_{c ∈ K} T c` is a twisted group algebra of `K`, i.e. the
multiplication restricted to `T c ⊗ T d` is an isomorphism onto the summand `T (c + d)`. -/
structure TwistedGroupAlgebra where
  /-- The homogeneous multiplication `T c ⊗ T d ≅ T (c + d)`. -/
  m : ∀ c d : K, T c ⊗ T d ≅ T (c + d)
  /-- `μ ∘ (incl_c ⊗ incl_d) = incl_{c+d} ∘ m(c,d)`. -/
  mul_eq : ∀ c d : K,
    (summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] = (m c d).hom ≫ summandIncl hA (c + d)

variable {hA} (D : TwistedGroupAlgebra hA)

omit [MonoidalPreadditive C] in
@[reassoc]
theorem TwistedGroupAlgebra.whiskerLeft_incl_mul (c d : K) :
    T c ◁ summandIncl hA d ≫ summandIncl hA c ▷ A.X ≫ μ[A.X] =
      (D.m c d).hom ≫ summandIncl hA (c + d) := by
  rw [← D.mul_eq, MonoidalCategory.tensorHom_def', Category.assoc]

/-- The inverse of the homogeneous multiplication `T c ⊗ A ⟶ A`. -/
noncomputable def homogMulInv (c : K) : A.X ⟶ T c ⊗ A.X :=
  ∑ d, summandProj hA (c + d) ≫ (D.m c d).inv ≫ T c ◁ summandIncl hA d

omit [MonoidalPreadditive C] in
theorem homogMulInv_hom (c : K) :
    homogMulInv D c ≫ summandIncl hA c ▷ A.X ≫ μ[A.X] = 𝟙 A.X := by
  rw [homogMulInv, Preadditive.sum_comp]
  simp only [Category.assoc, D.whiskerLeft_incl_mul, Iso.inv_hom_id_assoc]
  rw [← summand_total hA]
  exact Equiv.sum_comp (Equiv.addLeft c) (fun e => summandProj hA e ≫ summandIncl hA e)

omit [MonoidalPreadditive C] in
theorem whiskerLeft_incl_homogMul_inv (c d : K) :
    T c ◁ summandIncl hA d ≫ (summandIncl hA c ▷ A.X ≫ μ[A.X]) ≫ homogMulInv D c =
      T c ◁ summandIncl hA d := by
  rw [← Category.assoc, ← Category.assoc, Category.assoc (T c ◁ summandIncl hA d),
    D.whiskerLeft_incl_mul, homogMulInv, Preadditive.comp_sum,
    Finset.sum_eq_single d]
  · simp only [Category.assoc, summandIncl_proj_self_assoc, Iso.hom_inv_id_assoc]
  · intro d' _ hd'
    have hne : c + d ≠ c + d' := fun h => hd' (add_left_cancel h).symm
    simp only [Category.assoc, summandIncl_proj_ne_assoc hA hne, Limits.zero_comp,
      Limits.comp_zero]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem homogMul_homogMulInv (c : K) :
    (summandIncl hA c ▷ A.X ≫ μ[A.X]) ≫ homogMulInv D c = 𝟙 (T c ⊗ A.X) := by
  calc (summandIncl hA c ▷ A.X ≫ μ[A.X]) ≫ homogMulInv D c
      = (∑ d, T c ◁ summandProj hA d ≫ T c ◁ summandIncl hA d) ≫
          (summandIncl hA c ▷ A.X ≫ μ[A.X]) ≫ homogMulInv D c := by
        rw [whisker_summand_total hA, Category.id_comp]
    _ = ∑ d, T c ◁ summandProj hA d ≫ T c ◁ summandIncl hA d ≫
          (summandIncl hA c ▷ A.X ≫ μ[A.X]) ≫ homogMulInv D c := by
        rw [Preadditive.sum_comp]
        simp only [Category.assoc]
    _ = ∑ d, T c ◁ summandProj hA d ≫ T c ◁ summandIncl hA d := by
        simp only [whiskerLeft_incl_homogMul_inv]
    _ = 𝟙 (T c ⊗ A.X) := whisker_summand_total hA (T c)

/-- The homogeneous multiplication `T c ⊗ A ≅ A`, `x ⊗ a ↦ x a`, is an isomorphism. -/
noncomputable def homogMulIso (c : K) : T c ⊗ A.X ≅ A.X where
  hom := summandIncl hA c ▷ A.X ≫ μ[A.X]
  inv := homogMulInv D c
  hom_inv_id := homogMul_homogMulInv D c
  inv_hom_id := homogMulInv_hom D c

/-- **`ℓ ⊗ A ≅ A` as right `A`-modules** for every homogeneous summand `ℓ = T c` of a twisted
group algebra `A`. -/
noncomputable def freeHomogIso (c : K) : free A (T c) ≅ regularMod A :=
  isoOfIso (homogMulIso D c) (by
    show ((α_ (T c) A.X A.X).hom ≫ T c ◁ μ[A.X]) ≫ summandIncl hA c ▷ A.X ≫ μ[A.X] =
      (summandIncl hA c ▷ A.X ≫ μ[A.X]) ▷ A.X ≫ μ[A.X]
    rw [Category.assoc, MonoidalCategory.whisker_exchange_assoc,
      ← MonoidalCategory.associator_naturality_left_assoc, ← MonObj.mul_assoc A.X,
      MonoidalCategory.comp_whiskerRight_assoc])

/-- `(X ⊗ ℓ) ⊗ A ≅ X ⊗ A` as right `A`-modules, for every homogeneous summand `ℓ = T c`. -/
noncomputable def freeTensorHomogIso (X : C) (c : K) : free A (X ⊗ T c) ≅ free A X :=
  (tensorLeftObjFreeIso A X (T c)).symm ≪≫ tensorLeftIso X (freeHomogIso D c) ≪≫
    tensorLeftRegularIso A X

end Graded

section Lminus

variable [Preadditive C] [HasFiniteBiproducts C] [MonoidalPreadditive C]

/-- **Every free module is induced from `L₋`** (manuscript lines 3345–3346): with
`A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` a twisted group algebra of `L₊`, for every `v ∈ (ℤ/3)²` the free
module `S v ⊗ A` is isomorphic to `S (a, -a) ⊗ A` for some `(a, -a) ∈ L₋`. -/
theorem free_iso_Lminus (A : Mon C) (S : ZMod 3 × ZMod 3 → C)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    {hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)} (D : TwistedGroupAlgebra hA)
    (v : ZMod 3 × ZMod 3) : ∃ a : ZMod 3, Nonempty (free A (S v) ≅ free A (S (a, -a))) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (Weights.coset_Lplus_meets_Lminus_once v)
  have hmem : a ∈ Finset.univ.filter
      (fun a : ZMod 3 => ∃ c : ZMod 3, v = (a, -a) + (c, c)) := by
    rw [ha]
    exact Finset.mem_singleton_self a
  obtain ⟨c, hc⟩ := (Finset.mem_filter.1 hmem).2
  refine ⟨a, ⟨?_⟩⟩
  subst hc
  exact (freeFunctor A).mapIso (hfusion (a, -a) (c, c)).symm ≪≫
    freeTensorHomogIso D (S (a, -a)) c

/-- **Essential surjectivity of induction from `L₋` onto free modules**: the free module on a
finite direct sum of the invertibles `S v` is isomorphic to the free module on a finite direct
sum of the three invertibles `S (a, -a)` of `L₋`. -/
theorem free_biproduct_iso_Lminus (A : Mon C) (S : ZMod 3 × ZMod 3 → C)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    {hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)} (D : TwistedGroupAlgebra hA)
    {J : Type} [Fintype J] (v : J → ZMod 3 × ZMod 3) :
    ∃ a : J → ZMod 3, Nonempty
      (free A (⨁ fun j => S (v j)) ≅ free A (⨁ fun j => S (a j, -a j))) := by
  choose a ha using fun j => free_iso_Lminus A S hfusion D (v j)
  exact ⟨a, ⟨biproductMapIso (freeFunctor A) (X := fun j => S (v j))
    (Y := fun j => S (a j, -a j)) fun j => (ha j).some⟩⟩

end Lminus

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.biproductMapIso
#print axioms HaagerupIzumi.C8.RightMod.regularMod
#print axioms HaagerupIzumi.C8.RightMod.tensorLeftIso
#print axioms HaagerupIzumi.C8.RightMod.homogMulIso
#print axioms HaagerupIzumi.C8.RightMod.freeHomogIso
#print axioms HaagerupIzumi.C8.RightMod.freeTensorHomogIso
#print axioms HaagerupIzumi.C8.RightMod.free_iso_Lminus
#print axioms HaagerupIzumi.C8.RightMod.free_biproduct_iso_Lminus
