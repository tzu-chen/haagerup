module

public import HaagerupIzumi.C8.Category.PointedCocycle

@[expose] public section

/-! # Skeletalization of the pointed part on `L₋`: trivial twists ⇒ untwisted and symmetric

Bridge between a pointed braided `𝕜`-linear category and the cocycle statement
`AbelianCocycle.isTrivial_of_trace_eq_one` (`Category/AbelianCocycleZ3.lean`), for the
Tannakian step of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`, lines 3335–3337).

* `normalizedCocycle`: from scalars `(ω, c)` satisfying the pentagon and hexagon equations
  (as produced by `Category/PointedCocycle.lean` for any choice of the isomorphisms
  `φ_{a,b} : S a ⊗ S b ≅ S (a + b)`), the normalized cohomologous pair, an `AbelianCocycle`
  (normalization by the coboundary of `nf`, `nf(x,0) = ω(x,0,0)⁻¹`, `nf(0,y) = ω(0,0,y)`); it has
  the same twists (`normalizedCocycle_c_self`).
* `pointedCocycle 𝕜 S hEnd φ : AbelianCocycle A 𝕜ˣ`: the normalized abelian 3-cocycle of the
  pointed braided category (associator scalars `ωs`, braiding scalars `cs`); its twists are the
  braiding self-scalars `cs φ a a` (`pointedCocycle_c_self`).
* `trivialize` (`A = ℤ/3`): pentagon + hexagons + trivial twists ⇒ the scalars are a coboundary.
* `Lminus_untwisted_symmetric`: **if the self-braidings `β_{S a, S a}` are trivial (`L₋` with
  vanishing quadratic form), there are isomorphisms `φ'_{a,b} : S a ⊗ S b ≅ S (a + b)` for which
  the associator and the braiding are trivial**:
  `α ≫ S a ◁ φ'_{b,c} ≫ φ'_{a,b+c} = φ'_{a,b} ▷ S c ≫ φ'_{a+b,c}` and
  `β ≫ φ'_{b,a} = φ'_{a,b}` (up to the identifications `S (a + (b + c)) = S ((a + b) + c)`,
  `S (b + a) = S (a + b)`).  That is, in the skeletal model given by the `φ'` the associator and
  the braiding of the pointed part on `L₋` are trivial: untwisted and symmetric.  The functor-level
  statements (including the unit) are `Lminus_braided_vec` (`Category/LminusBraidedVec.lean`)
  and `Lminus_closure_braided_functor`; the comparison with the additive envelope as a monoidal
  category is not formalized (`Category/LminusEnvelope.lean`).

Hypotheses: `C` braided, preadditive and `𝕜`-linear with linear whiskering; the objects `S a`
have one-dimensional endomorphism algebras; isomorphisms `S a ⊗ S b ≅ S (a + b)` are given.  No
external-theorem or certificate inputs.  In the application to `Rep(B)` (external input `hθ`):
the twist is `θ = e^{2πi L₀}` (Huang, 2008), for an invertible `ℓ` (dimension `d_ℓ = 1`) the
self-braiding is `c_{ℓ,ℓ} = θ_ℓ`, and the conformal weight satisfies `h_ℓ ≡ q(ℓ) mod 1`;
equivalently, the braiding of the lattice VOA on simple currents is `e^{πi(λ,μ)}`
(Dong–Lepowsky).  With `q = 0` on `L₋` (`Weights.Lminus_symmetric_trivial_twists`) the
self-braidings are trivial. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Module AbelianCocycleZ3

universe v u

namespace PointedCocycle

section Normalize

variable {A : Type*} [AddCommGroup A] [DecidableEq A] {M : Type*} [AddCommGroup M]
  (ω : A → A → A → M) (c : A → A → M)

/-- The normalizing cochain. -/
def nf (x y : A) : M := if y = 0 then -ω x 0 0 else if x = 0 then ω 0 0 y else 0

/-- The normalized associator `ω + ∂ nf`. -/
def nω (x y z : A) : M := ω x y z + nf ω x y + nf ω (x + y) z - nf ω y z - nf ω x (y + z)

/-- The normalized braiding. -/
def nc (x y : A) : M := c x y + nf ω x y - nf ω y x

variable (hP : ∀ w x y z, ω w x y + ω w (x + y) z + ω x y z = ω (w + x) y z + ω w x (y + z))
  (hH1 : ∀ x y z, ω x y z + c x (y + z) + ω y z x = c x y + ω y x z + c x z)
  (hH2 : ∀ x y z, -ω x y z + c (x + y) z + -ω z x y = c y z + -ω x z y + c x z)

include hP in
theorem ω_zero_zero_zero : ω 0 0 0 = 0 := by
  have h := hP 0 0 0 0
  simp only [add_zero] at h
  linear_combination (norm := abel) h

theorem nf_zero_right (x : A) : nf ω x 0 = -ω x 0 0 := if_pos rfl

include hP in
theorem nf_zero_left (y : A) : nf ω 0 y = ω 0 0 y := by
  by_cases hy : y = 0
  · subst hy
    rw [nf_zero_right, ω_zero_zero_zero ω hP, neg_zero]
  · unfold nf
    rw [if_neg hy, if_pos rfl]

theorem nc_self (x : A) : nc ω c x x = c x x := by
  simp [nc]

include hP in
theorem nω_zero_left (y z : A) : nω ω 0 y z = 0 := by
  have h := hP 0 0 y z
  simp only [zero_add] at h
  simp only [nω, zero_add, nf_zero_left ω hP]
  linear_combination (norm := abel) h

include hP in
theorem nω_zero_mid (x z : A) : nω ω x 0 z = 0 := by
  have h := hP x 0 0 z
  simp only [add_zero, zero_add] at h
  simp only [nω, add_zero, zero_add, nf_zero_left ω hP, nf_zero_right]
  linear_combination (norm := abel) h.symm

include hP in
theorem nω_zero_right (x y : A) : nω ω x y 0 = 0 := by
  have h := hP x y 0 0
  simp only [add_zero] at h
  simp only [nω, add_zero, nf_zero_right]
  linear_combination (norm := abel) h

include hP in
theorem nω_pentagon (w x y z : A) :
    nω ω w x y + nω ω w (x + y) z + nω ω x y z = nω ω (w + x) y z + nω ω w x (y + z) := by
  have h := hP w x y z
  simp only [nω]
  rw [add_assoc w x y, add_assoc x y z]
  linear_combination (norm := abel) h

include hH1 in
theorem nω_hexagon₁ (x y z : A) :
    nω ω x y z + nc ω c x (y + z) + nω ω y z x = nc ω c x y + nω ω y x z + nc ω c x z := by
  have h := hH1 x y z
  simp only [nω, nc]
  rw [add_comm y x, add_comm z x]
  linear_combination (norm := abel) h

include hH2 in
theorem nω_hexagon₂ (x y z : A) :
    -nω ω x y z + nc ω c (x + y) z + -nω ω z x y = nc ω c y z + -nω ω x z y + nc ω c x z := by
  have h := hH2 x y z
  simp only [nω, nc]
  rw [add_comm z y, add_comm z x]
  linear_combination (norm := abel) h

end Normalize

section Mul

variable {A : Type*} [AddCommGroup A] [DecidableEq A] {G : Type*} [CommGroup G]
  (ω : A → A → A → G) (c : A → A → G)
  (hP : ∀ w x y z, ω w x y * ω w (x + y) z * ω x y z = ω (w + x) y z * ω w x (y + z))
  (hH1 : ∀ x y z, ω x y z * c x (y + z) * ω y z x = c x y * ω y x z * c x z)
  (hH2 : ∀ x y z, (ω x y z)⁻¹ * c (x + y) z * (ω z x y)⁻¹ = c y z * (ω x z y)⁻¹ * c x z)

/-- The associator in additive notation. -/
abbrev ωA (x y z : A) : Additive G := Additive.ofMul (ω x y z)

/-- The braiding in additive notation. -/
abbrev cA (x y : A) : Additive G := Additive.ofMul (c x y)

include hP in
theorem hPA (w x y z : A) : ωA ω w x y + ωA ω w (x + y) z + ωA ω x y z =
    ωA ω (w + x) y z + ωA ω w x (y + z) := by
  have := congrArg Additive.ofMul (hP w x y z)
  simpa only [ofMul_mul] using this

include hH1 in
theorem hH1A (x y z : A) : ωA ω x y z + cA c x (y + z) + ωA ω y z x =
    cA c x y + ωA ω y x z + cA c x z := by
  have := congrArg Additive.ofMul (hH1 x y z)
  simpa only [ofMul_mul] using this

include hH2 in
theorem hH2A (x y z : A) : -ωA ω x y z + cA c (x + y) z + -ωA ω z x y =
    cA c y z + -ωA ω x z y + cA c x z := by
  have := congrArg Additive.ofMul (hH2 x y z)
  simpa only [ofMul_mul, ofMul_inv] using this

/-- **The normalized abelian cocycle** cohomologous to `(ω, c)`. -/
@[simps]
def normalizedCocycle : AbelianCocycle A G where
  ω x y z := Additive.toMul (nω (ωA ω) x y z)
  c x y := Additive.toMul (nc (ωA ω) (cA c) x y)
  pentagon w x y z := Additive.ofMul.injective (by
    simpa only [ofMul_mul, ofMul_toMul] using nω_pentagon (ωA ω) (hPA ω hP) w x y z)
  hexagon₁ x y z := Additive.ofMul.injective (by
    simpa only [ofMul_mul, ofMul_toMul] using nω_hexagon₁ (ωA ω) (cA c) (hH1A ω c hH1) x y z)
  hexagon₂ x y z := Additive.ofMul.injective (by
    simpa only [ofMul_mul, ofMul_inv, ofMul_toMul] using
      nω_hexagon₂ (ωA ω) (cA c) (hH2A ω c hH2) x y z)
  ω_zero_left y z := by rw [nω_zero_left (ωA ω) (hPA ω hP)]; rfl
  ω_zero_mid x z := by rw [nω_zero_mid (ωA ω) (hPA ω hP)]; rfl
  ω_zero_right x y := by rw [nω_zero_right (ωA ω) (hPA ω hP)]; rfl

theorem normalizedCocycle_c_self (x : A) :
    (normalizedCocycle ω c hP hH1 hH2).c x x = c x x := by
  simp only [normalizedCocycle_c, nc_self]
  rfl

end Mul

/-- **Trivialization on `ℤ/3`**: scalars satisfying the pentagon and hexagon equations with
trivial twists are an abelian coboundary. -/
theorem trivialize {G : Type*} [CommGroup G] (ω : ZMod 3 → ZMod 3 → ZMod 3 → G)
    (c : ZMod 3 → ZMod 3 → G)
    (hP : ∀ w x y z, ω w x y * ω w (x + y) z * ω x y z = ω (w + x) y z * ω w x (y + z))
    (hH1 : ∀ x y z, ω x y z * c x (y + z) * ω y z x = c x y * ω y x z * c x z)
    (hH2 : ∀ x y z, (ω x y z)⁻¹ * c (x + y) z * (ω z x y)⁻¹ = c y z * (ω x z y)⁻¹ * c x z)
    (hc : ∀ x, c x x = 1) :
    ∃ f : ZMod 3 → ZMod 3 → G, (∀ x y z, f y z * f x (y + z) = ω x y z * f x y * f (x + y) z) ∧
      ∀ x y, f y x = c x y * f x y := by
  have hZc : ∀ x, (normalizedCocycle ω c hP hH1 hH2).c x x = 1 := fun x => by
    rw [normalizedCocycle_c_self, hc]
  obtain ⟨f₂, h1, h2, -, -⟩ := (normalizedCocycle ω c hP hH1 hH2).isTrivial_of_trace_eq_one hZc
  refine ⟨fun x y => Additive.toMul (nf (ωA ω) x y) * f₂ x y, fun x y z => ?_, fun x y => ?_⟩
  · apply Additive.ofMul.injective
    have h := congrArg Additive.ofMul (h1 x y z)
    simp only [ofMul_mul, ofMul_toMul, normalizedCocycle_ω, nω] at h ⊢
    linear_combination (norm := abel) h
  · apply Additive.ofMul.injective
    have h := congrArg Additive.ofMul (h2 x y)
    simp only [ofMul_mul, ofMul_toMul, normalizedCocycle_c, nc] at h ⊢
    linear_combination (norm := abel) h

section Category

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C]
  [MonoidalLinear 𝕜 C] {A : Type*} [AddCommGroup A] [DecidableEq A] (S : A → C)
  (hEnd : ∀ a, finrank 𝕜 (S a ⟶ S a) = 1) (φ : ∀ a b : A, S a ⊗ S b ≅ S (a + b))

/-- The associator scalars as units. -/
noncomputable def ωu (a b c : A) : 𝕜ˣ := Units.mk0 _ (ωs_ne_zero 𝕜 S hEnd φ a b c)

/-- The braiding scalars as units. -/
noncomputable def cu (a b : A) : 𝕜ˣ := Units.mk0 _ (cs_ne_zero 𝕜 S hEnd φ a b)

theorem ωu_pentagon (w x y z : A) :
    ωu 𝕜 S hEnd φ w x y * ωu 𝕜 S hEnd φ w (x + y) z * ωu 𝕜 S hEnd φ x y z =
      ωu 𝕜 S hEnd φ (w + x) y z * ωu 𝕜 S hEnd φ w x (y + z) :=
  Units.ext (by simp only [ωu, Units.val_mul, Units.val_mk0, pentagon_scalar])

theorem ωu_hexagon₁ (x y z : A) :
    ωu 𝕜 S hEnd φ x y z * cu 𝕜 S hEnd φ x (y + z) * ωu 𝕜 S hEnd φ y z x =
      cu 𝕜 S hEnd φ x y * ωu 𝕜 S hEnd φ y x z * cu 𝕜 S hEnd φ x z :=
  Units.ext (by simp only [ωu, cu, Units.val_mul, Units.val_mk0, hexagon_forward_scalar])

theorem ωu_hexagon₂ (x y z : A) :
    (ωu 𝕜 S hEnd φ x y z)⁻¹ * cu 𝕜 S hEnd φ (x + y) z * (ωu 𝕜 S hEnd φ z x y)⁻¹ =
      cu 𝕜 S hEnd φ y z * (ωu 𝕜 S hEnd φ x z y)⁻¹ * cu 𝕜 S hEnd φ x z :=
  Units.ext (by
    simp only [ωu, cu, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
      hexagon_reverse_scalar])

/-- **The abelian 3-cocycle of a pointed braided category** (normalized), with associator
scalars `ωs` and braiding scalars `cs` for the chosen `φ`, normalized by a coboundary. -/
noncomputable def pointedCocycle : AbelianCocycle A 𝕜ˣ :=
  normalizedCocycle (ωu 𝕜 S hEnd φ) (cu 𝕜 S hEnd φ) (ωu_pentagon 𝕜 S hEnd φ)
    (ωu_hexagon₁ 𝕜 S hEnd φ) (ωu_hexagon₂ 𝕜 S hEnd φ)

/-- The twists of the pointed cocycle are the braiding self-scalars. -/
theorem pointedCocycle_c_self (a : A) :
    ((pointedCocycle 𝕜 S hEnd φ).c a a : 𝕜) = cs 𝕜 S hEnd φ a a := by
  unfold pointedCocycle
  rw [normalizedCocycle_c_self]
  rfl

include hEnd in
/-- Any other choice of isomorphisms is a rescaling of `φ`. -/
theorem exists_scale (φ₂ : ∀ a b : A, S a ⊗ S b ≅ S (a + b)) :
    ∃ g : A → A → 𝕜ˣ, φ₂ = scaleφ 𝕜 S φ g := by
  refine ⟨fun a b => Units.mk0 _ (scal_ne_zero 𝕜 S hEnd ((φ a b).inv ≫ (φ₂ a b).hom)), ?_⟩
  funext a b
  apply Iso.ext
  rw [scaleφ_hom, Units.val_mk0]
  calc (φ₂ a b).hom = (φ a b).hom ≫ ((φ a b).inv ≫ (φ₂ a b).hom) := by simp
    _ = _ := by
      conv_lhs => rw [← scal_smul 𝕜 S hEnd ((φ a b).inv ≫ (φ₂ a b).hom)]
      rw [Linear.comp_smul, Category.comp_id]

theorem ωu_scale (g : A → A → 𝕜ˣ) (a b c : A) :
    ωu 𝕜 S hEnd (scaleφ 𝕜 S φ g) a b c * (g a b * g (a + b) c) =
      ωu 𝕜 S hEnd φ a b c * (g b c * g a (b + c)) :=
  Units.ext (by
    simp only [ωu, Units.val_mul, Units.val_mk0]
    exact ωs_scale 𝕜 S hEnd φ g a b c)

theorem cu_scale (g : A → A → 𝕜ˣ) (a b : A) :
    cu 𝕜 S hEnd (scaleφ 𝕜 S φ g) a b * g a b = cu 𝕜 S hEnd φ a b * g b a :=
  Units.ext (by
    simp only [cu, Units.val_mul, Units.val_mk0]
    exact cs_scale 𝕜 S hEnd φ g a b)

/-- **The class is well defined**: the pointed cocycles of two choices of the isomorphisms
`φ_{a,b}` are cohomologous. -/
theorem pointedCocycle_cohomologous (φ₂ : ∀ a b : A, S a ⊗ S b ≅ S (a + b)) :
    (pointedCocycle 𝕜 S hEnd φ).Cohomologous (pointedCocycle 𝕜 S hEnd φ₂) := by
  obtain ⟨g, rfl⟩ := exists_scale 𝕜 S hEnd φ φ₂
  refine ⟨fun x y => Additive.toMul (nf (ωA (ωu 𝕜 S hEnd (scaleφ 𝕜 S φ g))) x y -
    nf (ωA (ωu 𝕜 S hEnd φ)) x y) * (g x y)⁻¹, fun x y z => ?_, fun x y => ?_⟩
  · apply Additive.ofMul.injective
    have h := congrArg Additive.ofMul (ωu_scale 𝕜 S hEnd φ g x y z)
    simp only [ofMul_mul] at h
    simp only [pointedCocycle, ofMul_mul, ofMul_inv, ofMul_toMul, normalizedCocycle_ω,
      nω]
    linear_combination (norm := abel) h
  · apply Additive.ofMul.injective
    have h := congrArg Additive.ofMul (cu_scale 𝕜 S hEnd φ g x y)
    simp only [ofMul_mul] at h
    simp only [pointedCocycle, ofMul_mul, ofMul_inv, ofMul_toMul, normalizedCocycle_c, nc]
    linear_combination (norm := abel) h

end Category

/-- **Skeletalization on `L₋`: trivial twists ⇒ untwisted and symmetric.**  For objects `S a`,
`a ∈ ℤ/3`, of a pointed braided `𝕜`-linear category with trivial self-braidings, there are
isomorphisms `φ'_{a,b} : S a ⊗ S b ≅ S (a + b)` in which the associator and the braiding are
trivial. -/
theorem Lminus_untwisted_symmetric {C : Type u} [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type*) [Field 𝕜]
    [Linear 𝕜 C] [MonoidalLinear 𝕜 C] (S : ZMod 3 → C)
    (hEnd : ∀ a, finrank 𝕜 (S a ⟶ S a) = 1) (φ : ∀ a b : ZMod 3, S a ⊗ S b ≅ S (a + b))
    (hθ : ∀ a, (β_ (S a) (S a)).hom = 𝟙 _) :
    ∃ φ' : ∀ a b : ZMod 3, S a ⊗ S b ≅ S (a + b),
      (∀ a b c, (α_ (S a) (S b) (S c)).hom ≫ S a ◁ (φ' b c).hom ≫ (φ' a (b + c)).hom =
        (φ' a b).hom ▷ S c ≫ (φ' (a + b) c).hom ≫ eqToHom (congrArg S (add_assoc a b c))) ∧
      ∀ a b, (β_ (S a) (S b)).hom ≫ (φ' b a).hom =
        (φ' a b).hom ≫ eqToHom (congrArg S (add_comm a b)) := by
  have hcu : ∀ x, cu 𝕜 S hEnd φ x x = 1 := fun x =>
    Units.ext (by simp only [cu, Units.val_mk0, Units.val_one, cs_self_eq_one 𝕜 S hEnd φ x (hθ x)])
  obtain ⟨f, hf1, hf2⟩ := trivialize (ωu 𝕜 S hEnd φ) (cu 𝕜 S hEnd φ) (ωu_pentagon 𝕜 S hEnd φ)
    (ωu_hexagon₁ 𝕜 S hEnd φ) (ωu_hexagon₂ 𝕜 S hEnd φ) hcu
  refine ⟨scaleφ 𝕜 S φ (fun a b => (f a b)⁻¹), fun a b c => ?_, fun a b => ?_⟩
  · have hs := ωs_scale 𝕜 S hEnd φ (fun a b => (f a b)⁻¹) a b c
    have e := congrArg Units.val (hf1 a b c)
    simp only [Units.val_mul, ωu, Units.val_mk0] at e
    simp only [Units.val_inv_eq_inv_val] at hs
    have n1 := Units.ne_zero (f a b)
    have n2 := Units.ne_zero (f (a + b) c)
    have n3 := Units.ne_zero (f b c)
    have n4 := Units.ne_zero (f a (b + c))
    have h1 : ωs 𝕜 S hEnd (scaleφ 𝕜 S φ (fun a b => (f a b)⁻¹)) a b c = 1 := by
      field_simp at hs
      have hne : (f b c : 𝕜) * f a (b + c) ≠ 0 := mul_ne_zero n3 n4
      apply mul_right_cancel₀ hne
      linear_combination hs - e
    rw [ω_rel 𝕜 S hEnd, h1, one_smul]
  · have hs := cs_scale 𝕜 S hEnd φ (fun a b => (f a b)⁻¹) a b
    have e := congrArg Units.val (hf2 a b)
    simp only [Units.val_mul, cu, Units.val_mk0] at e
    simp only [Units.val_inv_eq_inv_val] at hs
    have n1 := Units.ne_zero (f a b)
    have n2 := Units.ne_zero (f b a)
    have h1 : cs 𝕜 S hEnd (scaleφ 𝕜 S φ (fun a b => (f a b)⁻¹)) a b = 1 := by
      field_simp at hs
      apply mul_right_cancel₀ n2
      linear_combination hs - e
    rw [c_rel 𝕜 S hEnd, h1, one_smul]

end PointedCocycle

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PointedCocycle.normalizedCocycle
#print axioms HaagerupIzumi.C8.PointedCocycle.pointedCocycle
#print axioms HaagerupIzumi.C8.PointedCocycle.pointedCocycle_c_self
#print axioms HaagerupIzumi.C8.PointedCocycle.exists_scale
#print axioms HaagerupIzumi.C8.PointedCocycle.pointedCocycle_cohomologous
#print axioms HaagerupIzumi.C8.PointedCocycle.trivialize
#print axioms HaagerupIzumi.C8.PointedCocycle.Lminus_untwisted_symmetric
