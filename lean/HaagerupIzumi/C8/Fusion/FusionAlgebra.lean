module

public import HaagerupIzumi.C8.Fusion.BasedRing
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` gives the two hypotheses of `rank6_ring`

Line 3799 of `c8_expanded_20260929/haagerup_c8_expanded.tex`: the composition
algebra of `End_𝓒(H)` is identified with the complex fusion algebra
(Bischoff–Jones \[BJ, Cor. 3.4\]) and, with `H = 1 ⊕ X ⊕ 2Y`, it is
`ℂ ⊕ ℂ ⊕ M₂(ℂ)`.  That identification is an external categorical input; here it
is recorded as `FusionAlgebraIso R`: a `ℂ`-linear bijection from coefficient
vectors `ι → ℂ` onto `ℂ × ℂ × M₂(ℂ)` which is unital and multiplicative for the
fusion product `BasedRing.mul`.

From it we prove the two consequences used in `rank6_ring`:

* `FusionAlgebraIso.atMostTwoChars`: the fusion ring has at most two complex
  characters (an algebra homomorphism `ℂ × ℂ × M₂(ℂ) → ℂ` kills the matrix block,
  because the matrix units `E₁₂ E₂₁ = E₁₁`, `E₂₁ E₁₂ = E₂₂` force equal values
  on `E₁₁, E₂₂` and then `E₁₁ + E₂₂ = 1` is impossible for idempotents);
* `FusionAlgebraIso.noncomm`: some structure constant satisfies
  `N_{ij}^l ≠ N_{ji}^l`.
-/

namespace HaagerupIzumi.C8.Fusion

open BasedRing

/-- The algebra `ℂ ⊕ ℂ ⊕ M₂(ℂ)`. -/
abbrev CCM2 := ℂ × ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-- The matrix unit `E₁₂`. -/
noncomputable def mP : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The matrix unit `E₂₁`. -/
noncomputable def mQ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

theorem mP_mul_mQ_add : mP * mQ + mQ * mP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, mQ, Matrix.mul_apply, Fin.sum_univ_two]

theorem mPQ_idem : (mP * mQ) * (mP * mQ) = mP * mQ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, mQ, Matrix.mul_apply, Fin.sum_univ_two]

theorem mPQ_ne_mQP : mP * mQ ≠ mQ * mP := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [mP, mQ, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- A unital multiplicative linear functional on `ℂ ⊕ ℂ ⊕ M₂(ℂ)` vanishes on the
matrix block. -/
theorem ccm2_e3 (G : CCM2 →ₗ[ℂ] ℂ) (hmul : ∀ u v, G (u * v) = G u * G v) :
    G ((0, 0, 1) : CCM2) = 0 := by
  have hsum : ((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ) +
      ((0 : ℂ), (0 : ℂ), mQ) * ((0 : ℂ), (0 : ℂ), mP) = ((0 : ℂ), (0 : ℂ), 1) := by
    simp only [Prod.mk_mul_mk, Prod.mk_add_mk, mul_zero, add_zero, mP_mul_mQ_add]
  have hidem : (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) *
      (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) =
      ((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ) := by
    simp only [Prod.mk_mul_mk, mul_zero, mPQ_idem]
  have h3 : ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp only [Prod.mk_mul_mk, mul_zero, mul_one]
  have hx : G (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) *
      G (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) =
      G (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) := by
    rw [← hmul, hidem]
  have hy : G (((0 : ℂ), (0 : ℂ), mQ) * ((0 : ℂ), (0 : ℂ), mP)) =
      G (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) := by
    rw [hmul, hmul, mul_comm]
  have hz : G ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      2 * G (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) := by
    rw [← hsum, map_add, hy]
    ring
  have hzz : G ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      G ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      G ((0 : ℂ), (0 : ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [← hmul, h3]
  rw [hz] at hzz
  rw [hz]
  have h0 : G (((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ)) = 0 := by
    linear_combination (1 / 2 : ℂ) * hzz - 2 * hx
  rw [h0]
  ring

/-- Classification of unital multiplicative linear functionals on `ℂ ⊕ ℂ ⊕ M₂(ℂ)`:
`G(p, q, M) = p c + q (1 - c)` with `c = G(1, 0, 0) ∈ {0, 1}`. -/
theorem ccm2_classify (G : CCM2 →ₗ[ℂ] ℂ) (hmul : ∀ u v, G (u * v) = G u * G v)
    (hone : G 1 = 1) :
    (G ((1, 0, 0) : CCM2) = 0 ∨ G ((1, 0, 0) : CCM2) = 1) ∧
      ∀ u : CCM2, G u = u.1 * G ((1, 0, 0) : CCM2) + u.2.1 * (1 - G ((1, 0, 0) : CCM2)) := by
  have he3 := ccm2_e3 G hmul
  have h1 : ((1, 0, 0) : CCM2) + (0, 1, 0) + (0, 0, 1) = 1 :=
    Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  have h12 : ((1, 0, 0) : CCM2) * (0, 1, 0) = 0 :=
    Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  have hG12 : G ((1, 0, 0) : CCM2) + G ((0, 1, 0) : CCM2) = 1 := by
    have := congrArg G h1
    rw [map_add, map_add, he3, hone] at this
    linear_combination this
  have hprod : G ((1, 0, 0) : CCM2) * G ((0, 1, 0) : CCM2) = 0 := by
    rw [← hmul, h12, map_zero]
  refine ⟨?_, fun u => ?_⟩
  · have h : G ((1, 0, 0) : CCM2) * (G ((1, 0, 0) : CCM2) - 1) = 0 := by
      linear_combination -hprod + G ((1, 0, 0) : CCM2) * hG12
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · have hu : u = u.1 • ((1, 0, 0) : CCM2) + u.2.1 • ((0, 1, 0) : CCM2) + ((0, 0, 1) : CCM2) * u :=
      Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    have hGu := congrArg G hu
    rw [map_add, map_add, map_smul, map_smul, hmul, he3, zero_mul, add_zero, smul_eq_mul,
      smul_eq_mul] at hGu
    rw [hGu]
    linear_combination u.2.1 * hG12

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The external input: `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` as algebras (line 3799). -/
structure FusionAlgebraIso (R : BasedRing ι) where
  Φ : (ι → ℂ) ≃ₗ[ℂ] CCM2
  map_mul : ∀ x y, Φ (R.mul x y) = Φ x * Φ y
  map_one : Φ (Pi.single R.unit 1) = 1

/-- The linear functional `x ↦ ∑ x_i χ_i` attached to a function on the basis. -/
def charLin (χ : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i * χ i
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

theorem charLin_apply (χ x : ι → ℂ) : charLin χ x = ∑ i, x i * χ i := rfl

theorem charLin_single (χ : ι → ℂ) (i : ι) : charLin χ (Pi.single i 1) = χ i := by
  rw [charLin_apply]
  simp [Pi.single_apply]

/-- For a character, `x ↦ ∑ x_i χ_i` is multiplicative for the fusion product. -/
theorem charLin_mul (R : BasedRing ι) {χ : ι → ℂ} (hχ : R.IsCharacter χ) (x y : ι → ℂ) :
    charLin χ (R.mul x y) = charLin χ x * charLin χ y := by
  rw [charLin_apply, charLin_apply, charLin_apply, Fintype.sum_mul_sum]
  have h : ∀ i j, x i * y j * (χ i * χ j) = ∑ l, x i * y j * (R.N i j l : ℂ) * χ l := by
    intro i j
    rw [hχ.map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  calc ∑ l, R.mul x y l * χ l
      = ∑ l, ∑ i, ∑ j, x i * y j * (R.N i j l : ℂ) * χ l := by
        simp only [BasedRing.mul, Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ l, x i * y j * (R.N i j l : ℂ) * χ l := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, x i * χ i * (y j * χ j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [← h i j]
        ring

namespace FusionAlgebraIso

variable {R : BasedRing ι}

/-- Every character is determined by `c ∈ {0, 1}`. -/
theorem char_eq (Ψ : FusionAlgebraIso R) {χ : ι → ℂ} (hχ : R.IsCharacter χ) :
    ∃ c : ℂ, (c = 0 ∨ c = 1) ∧ ∀ i, χ i =
      (Ψ.Φ (Pi.single i 1)).1 * c + (Ψ.Φ (Pi.single i 1)).2.1 * (1 - c) := by
  let G : CCM2 →ₗ[ℂ] ℂ := (charLin χ).comp Ψ.Φ.symm.toLinearMap
  have hG : ∀ u, G u = charLin χ (Ψ.Φ.symm u) := fun u => rfl
  have hsymm : ∀ u v, Ψ.Φ.symm (u * v) = R.mul (Ψ.Φ.symm u) (Ψ.Φ.symm v) := fun u v => by
    apply Ψ.Φ.injective
    rw [LinearEquiv.apply_symm_apply, Ψ.map_mul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hmul : ∀ u v, G (u * v) = G u * G v := fun u v => by
    rw [hG, hG, hG, hsymm, charLin_mul R hχ]
  have hone : G 1 = 1 := by
    rw [hG, ← Ψ.map_one, LinearEquiv.symm_apply_apply, charLin_single, hχ.map_unit]
  obtain ⟨hc, hform⟩ := ccm2_classify G hmul hone
  refine ⟨G ((1, 0, 0) : CCM2), hc, fun i => ?_⟩
  rw [← hform, hG, LinearEquiv.symm_apply_apply, charLin_single]

/-- `ℂ ⊕ ℂ ⊕ M₂(ℂ)` has at most two characters, hence so does the fusion ring. -/
theorem atMostTwoChars (Ψ : FusionAlgebraIso R) (χ₁ χ₂ χ₃ : ι → ℂ) (h₁ : R.IsCharacter χ₁)
    (h₂ : R.IsCharacter χ₂) (h₃ : R.IsCharacter χ₃) : χ₁ = χ₂ ∨ χ₁ = χ₃ ∨ χ₂ = χ₃ := by
  obtain ⟨c₁, hc₁, e₁⟩ := Ψ.char_eq h₁
  obtain ⟨c₂, hc₂, e₂⟩ := Ψ.char_eq h₂
  obtain ⟨c₃, hc₃, e₃⟩ := Ψ.char_eq h₃
  have key : ∀ {χ χ' : ι → ℂ} {c c' : ℂ},
      (∀ i, χ i = (Ψ.Φ (Pi.single i 1)).1 * c + (Ψ.Φ (Pi.single i 1)).2.1 * (1 - c)) →
      (∀ i, χ' i = (Ψ.Φ (Pi.single i 1)).1 * c' + (Ψ.Φ (Pi.single i 1)).2.1 * (1 - c')) →
      c = c' → χ = χ' := by
    intro χ χ' c c' e e' hcc
    funext i
    rw [e i, e' i, hcc]
  rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2 <;> rcases hc₃ with h3 | h3
  · exact Or.inl (key e₁ e₂ (h1.trans h2.symm))
  · exact Or.inl (key e₁ e₂ (h1.trans h2.symm))
  · exact Or.inr (Or.inl (key e₁ e₃ (h1.trans h3.symm)))
  · exact Or.inr (Or.inr (key e₂ e₃ (h2.trans h3.symm)))
  · exact Or.inr (Or.inr (key e₂ e₃ (h2.trans h3.symm)))
  · exact Or.inr (Or.inl (key e₁ e₃ (h1.trans h3.symm)))
  · exact Or.inl (key e₁ e₂ (h1.trans h2.symm))
  · exact Or.inl (key e₁ e₂ (h1.trans h2.symm))

/-- `M₂(ℂ)` is noncommutative, hence so is the fusion ring. -/
theorem noncomm (Ψ : FusionAlgebraIso R) : ∃ i j l, R.N i j l ≠ R.N j i l := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ x y : ι → ℂ, R.mul x y = R.mul y x := by
    intro x y
    funext l
    simp only [BasedRing.mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hcon j i l]
    ring
  apply mPQ_ne_mQP
  have hP := Ψ.Φ.apply_symm_apply ((0 : ℂ), (0 : ℂ), mP)
  have hQ := Ψ.Φ.apply_symm_apply ((0 : ℂ), (0 : ℂ), mQ)
  have h := congrArg (fun z : CCM2 => z.2.2)
    (show ((0 : ℂ), (0 : ℂ), mP) * ((0 : ℂ), (0 : ℂ), mQ) =
        ((0 : ℂ), (0 : ℂ), mQ) * ((0 : ℂ), (0 : ℂ), mP) by
      rw [← hP, ← hQ, ← Ψ.map_mul, ← Ψ.map_mul, hcomm])
  simpa using h

end FusionAlgebraIso

/-- The hypotheses `hchar` and `hnc` of `rank6_ring`, derived from
`K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)`. -/
theorem FusionAlgebraIso.rank6_hypotheses {R : BasedRing ι} (Ψ : FusionAlgebraIso R) :
    (∀ χ₁ χ₂ χ₃ : ι → ℂ, R.IsCharacter χ₁ → R.IsCharacter χ₂ → R.IsCharacter χ₃ →
      χ₁ = χ₂ ∨ χ₁ = χ₃ ∨ χ₂ = χ₃) ∧ ∃ i j l, R.N i j l ≠ R.N j i l :=
  ⟨Ψ.atMostTwoChars, Ψ.noncomm⟩

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.ccm2_classify
#print axioms HaagerupIzumi.C8.Fusion.FusionAlgebraIso.rank6_hypotheses
