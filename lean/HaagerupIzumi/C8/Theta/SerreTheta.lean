module

public import HaagerupIzumi.C8.Theta.WeilBlocks
public import Mathlib.NumberTheory.ModularForms.Derivative

@[expose] public section

/-!
# `F = -6 D₂ Θ`: the `S`- and `T`-laws of the Serre derivative of the theta vectors

W6 plan item 3, the `F` orientations (`Theta/M3Reverse`, `Theta/M6Reverse`; lines 3682–3712
and 3742–3777 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).  The manuscript's modular
derivative `D₂ = q d/dq - E₂/6` is Mathlib's Serre derivative `Derivative.serreDerivative 2`
(`D = (2πi)⁻¹ d/dτ = q d/dq`).  From the weight-two theta laws (`thetaG7m_S`, `thetaG6m_S`, …)
in slash form and Mathlib's `serreDerivative_slash_equivariant`:

* `serre_finset_sum`: the Serre derivative is linear on finite combinations;
* `serreTheta*_S`, `serreTheta*_T`: `∂₂Θ_p(-1/τ) = τ⁴ ∑_q Sθ_{pq} ∂₂Θ_q(τ)` and
  `∂₂Θ_p(τ+1) = e(q(γ_p)) ∂₂Θ_p(τ)` with the **same** matrix `Sθ*` as the harmonic theta
  vectors (`Theta/WeilBlocks`);
* `FF*_S`, `FF*_T`, `FF*_covariant`: the weight-zero vector `F_p = -6 ∂₂Θ_p / η⁸` satisfies
  `F(S•τ) = Sθ F(τ)`, `F(T•τ) = Tθ F(τ)`, hence is `σ`-covariant for any `σ` with
  `σ(S) = Sθ*`, `σ(T) = Tθ*`; so are the combinations `φ F + κ Θ_H/η⁸` of the manuscript.

The `q`-expansion of `∂₂Θ` (the coefficients `minusSixD2Coeff` of `Theta/Basic`) is proved in
`Theta/SerreQExp` and `Theta/E2Theta` (`minusSixSerre_theta_qexp`).  Nothing here is an external
hypothesis.
-/

noncomputable section

open Complex Matrix ModularGroup UpperHalfPlane
open scoped MatrixGroups Real Manifold ModularForm

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Generic facts -/

set_option backward.isDefEq.respectTransparency false in
theorem denom_T_eq_one (z : ℍ) : denom (T : SL(2, ℤ)) z = 1 := by
  simp [T, denom_apply]

theorem serre_zero (k : ℂ) : Derivative.serreDerivative k (0 : ℍ → ℂ) = 0 := by
  ext z
  have h := congrFun (Derivative.normalizedDerivOfComplex_const (0 : ℂ)) z
  simp only [Derivative.serreDerivative_apply, Pi.zero_apply, mul_zero, sub_zero]
  exact h

/-- Linearity of the Serre derivative on finite combinations. -/
theorem serre_finset_sum {ι : Type} (k : ℂ) (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (hf : ∀ i, MDiff (f i)) :
    Derivative.serreDerivative k (∑ i ∈ s, c i • f i) =
      ∑ i ∈ s, c i • Derivative.serreDerivative k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using serre_zero k
  | insert a s ha ih =>
    have hsum : MDiff (∑ i ∈ s, c i • f i) :=
      MDifferentiable.sum (t := s) (f := fun i => c i • f i) fun i _ => (hf i).const_smul (c i)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Derivative.serreDerivative_add k (c a • f a) (∑ i ∈ s, c i • f i)
        ((hf a).const_smul (c a)) hsum,
      Derivative.serreDerivative_smul _ _ _ (hf a), ih]

/-- From a weight-two vector `S`-law in slash form to the weight-four law of `∂₂`. -/
theorem serre_S_of_slash {ι : Type} [Fintype ι] (θ : ι → ℍ → ℂ) (hθ : ∀ i, MDiff (θ i))
    (A : Matrix ι ι ℂ) (hS : ∀ i, θ i ∣[(2 : ℤ)] S = ∑ j, A i j • θ j) (i : ι) (τ : ℍ) :
    Derivative.serreDerivative 2 (θ i) (S • τ) =
      (τ : ℂ) ^ 4 * ∑ j, A i j * Derivative.serreDerivative 2 (θ j) τ := by
  have h := Derivative.serreDerivative_slash_equivariant (k := 2) (hθ i) (γ := S)
  rw [show (2 : ℤ) + 2 = 4 by norm_num, hS i] at h
  push_cast at h
  rw [serre_finset_sum 2 Finset.univ (A i) θ hθ] at h
  have h' := congrFun h τ
  rw [ModularForm.SL_slash_apply, denom_S] at h'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h'
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h4 : (τ : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 hτ
  have hz : (τ : ℂ) ^ (-4 : ℤ) = ((τ : ℂ) ^ 4)⁻¹ := by rw [_root_.zpow_neg, zpow_ofNat]
  rw [← h', hz]
  field_simp

/-- From a weight-two `T`-law in slash form to the law of `∂₂`. -/
theorem serre_T_of_slash (θ : ℍ → ℂ) (hθ : MDiff θ) (c : ℂ) (hT : θ ∣[(2 : ℤ)] T = c • θ)
    (τ : ℍ) : Derivative.serreDerivative 2 θ (T • τ) = c * Derivative.serreDerivative 2 θ τ := by
  have h := Derivative.serreDerivative_slash_equivariant (k := 2) hθ (γ := T)
  rw [show (2 : ℤ) + 2 = 4 by norm_num, hT] at h
  push_cast at h
  rw [Derivative.serreDerivative_smul _ _ _ hθ] at h
  have h' := congrFun h τ
  rw [ModularForm.SL_slash_apply, denom_T_eq_one, _root_.one_zpow, mul_one] at h'
  rw [h']
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The weight-zero `S`-law of `Θ/η⁸` for a weight-four `Θ` on `ℍ`. -/
theorem weight_zero_S_ℍ (Θ : ι → ℍ → ℂ) (Sm : Matrix ι ι ℂ)
    (hΘ : ∀ p (τ : ℍ), Θ p (S • τ) = (τ : ℂ) ^ 4 * ∑ q, Sm p q * Θ q τ) (τ : ℍ) :
    (fun p => Θ p (S • τ) / eta8 ((S • τ : ℍ) : ℂ)) = Sm *ᵥ fun p => Θ p τ / eta8 τ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have h4 : (τ : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 τ.ne_zero
  funext p
  rw [coe_S_smul, hΘ p τ, eta8_S hτ]
  simp only [mulVec, dotProduct]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  calc (τ : ℂ) ^ 4 * (Sm p q * Θ q τ) / ((τ : ℂ) ^ 4 * eta8 τ)
      = Sm p q * (Θ q τ / eta8 τ) * ((τ : ℂ) ^ 4 / (τ : ℂ) ^ 4) := by ring
    _ = Sm p q * (Θ q τ / eta8 τ) := by rw [div_self h4, mul_one]

/-- The weight-zero `T`-law of `Θ/η⁸` for `Θ` on `ℍ`. -/
theorem weight_zero_T_ℍ (Θ : ι → ℍ → ℂ) (e : ι → ℝ)
    (hΘ : ∀ p (τ : ℍ), Θ p (T • τ) = eChar (e p) * Θ p τ) (τ : ℍ) :
    (fun p => Θ p (T • τ) / eta8 ((T • τ : ℍ) : ℂ)) =
      (Matrix.diagonal fun p => eChar (e p - 1 / 3)) *ᵥ fun p => Θ p τ / eta8 τ := by
  funext p
  rw [hΘ, coe_T_smul, eta8_T, mulVec_diagonal, eChar_sub]
  ring

/-! ## `G₇⁻` -/

/-- The weight-two theta vector of `G₇⁻` on `ℍ`. -/
def θG7m (j : Fin 21) : ℍ → ℂ := fun τ => thetaG7m j τ

theorem mdifferentiable_θG7m (j : Fin 21) : MDiff (θG7m j) :=
  mdifferentiable_latticeTheta posDef_G7m _

theorem θG7m_slash_S (j : Fin 21) : θG7m j ∣[(2 : ℤ)] S = ∑ k, SθG7m j k • θG7m k := by
  ext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [ModularForm.SL_slash_apply, denom_S]
  simp only [θG7m, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SθG7m, Matrix.of_apply]
  rw [coe_S_smul, thetaG7m_S j τ.im_pos, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [_root_.zpow_neg, zpow_ofNat]
  field_simp

theorem θG7m_slash_T (j : Fin 21) : θG7m j ∣[(2 : ℤ)] T = eChar (eG7m j) • θG7m j := by
  ext τ
  rw [ModularForm.SL_slash_apply, denom_T_eq_one, _root_.one_zpow, mul_one]
  simp only [θG7m, Pi.smul_apply, smul_eq_mul]
  rw [coe_T_smul, thetaG7m_T]

/-- `∂₂Θ_j(-1/τ) = τ⁴ ∑_k Sθ_{jk} ∂₂Θ_k(τ)`. -/
theorem serreThetaG7m_S (j : Fin 21) (τ : ℍ) :
    Derivative.serreDerivative 2 (θG7m j) (S • τ) =
      (τ : ℂ) ^ 4 * ∑ k, SθG7m j k * Derivative.serreDerivative 2 (θG7m k) τ :=
  serre_S_of_slash θG7m mdifferentiable_θG7m SθG7m θG7m_slash_S j τ

theorem serreThetaG7m_T (j : Fin 21) (τ : ℍ) :
    Derivative.serreDerivative 2 (θG7m j) (T • τ) =
      eChar (eG7m j) * Derivative.serreDerivative 2 (θG7m j) τ :=
  serre_T_of_slash (θG7m j) (mdifferentiable_θG7m j) _ (θG7m_slash_T j) τ

/-- The weight-zero vector `F_j = -6 ∂₂Θ_j / η⁸`. -/
def FFG7m (τ : ℍ) : Fin 21 → ℂ :=
  fun j => -6 * Derivative.serreDerivative 2 (θG7m j) τ / eta8 τ

theorem FFG7m_S (τ : ℍ) : FFG7m (S • τ) = SθG7m *ᵥ FFG7m τ := by
  have h := weight_zero_S_ℍ (fun j τ => -6 * Derivative.serreDerivative 2 (θG7m j) τ) SθG7m
    (fun j τ => by
      rw [serreThetaG7m_S, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring) τ
  exact h

theorem FFG7m_T (τ : ℍ) : FFG7m (T • τ) = TθG7m *ᵥ FFG7m τ := by
  have h := weight_zero_T_ℍ (fun j τ => -6 * Derivative.serreDerivative 2 (θG7m j) τ) eG7m
    (fun j τ => by rw [serreThetaG7m_T]; ring) τ
  exact h

/-- **Covariance of `F = -6 ∂₂Θ/η⁸` for `G₇⁻`**, given `σ(S) = Sθ`, `σ(T) = Tθ`. -/
theorem FFG7m_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 21) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθG7m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FFG7m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FFG7m τ :=
  covariant_of_S_T σ FFG7m (fun τ => by rw [hσS]; exact FFG7m_S τ)
    (fun τ => by rw [hσT]; exact FFG7m_T τ)

/-! ## `G₆⁻` -/

def θG6m (p : Fin 2 × Fin 2 × Fin 3) : ℍ → ℂ := fun τ => thetaG6m p τ

theorem mdifferentiable_θG6m (p : Fin 2 × Fin 2 × Fin 3) : MDiff (θG6m p) :=
  mdifferentiable_latticeTheta posDef_G6m _

theorem θG6m_slash_S (p : Fin 2 × Fin 2 × Fin 3) :
    θG6m p ∣[(2 : ℤ)] S = ∑ q, SθG6m p q • θG6m q := by
  ext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [ModularForm.SL_slash_apply, denom_S]
  simp only [θG6m, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SθG6m, Matrix.of_apply]
  rw [coe_S_smul, thetaG6m_S p τ.im_pos, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [_root_.zpow_neg, zpow_ofNat]
  field_simp

theorem θG6m_slash_T (p : Fin 2 × Fin 2 × Fin 3) :
    θG6m p ∣[(2 : ℤ)] T = eChar (eG6m p) • θG6m p := by
  ext τ
  rw [ModularForm.SL_slash_apply, denom_T_eq_one, _root_.one_zpow, mul_one]
  simp only [θG6m, Pi.smul_apply, smul_eq_mul]
  rw [coe_T_smul, thetaG6m_T]

def FFG6m (τ : ℍ) : Fin 2 × Fin 2 × Fin 3 → ℂ :=
  fun p => -6 * Derivative.serreDerivative 2 (θG6m p) τ / eta8 τ

theorem FFG6m_S (τ : ℍ) : FFG6m (S • τ) = SθG6m *ᵥ FFG6m τ := by
  have h := weight_zero_S_ℍ (fun p τ => -6 * Derivative.serreDerivative 2 (θG6m p) τ) SθG6m
    (fun p τ => by
      rw [serre_S_of_slash θG6m mdifferentiable_θG6m SθG6m θG6m_slash_S p τ, Finset.mul_sum,
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring) τ
  exact h

theorem FFG6m_T (τ : ℍ) : FFG6m (T • τ) = TθG6m *ᵥ FFG6m τ := by
  have h := weight_zero_T_ℍ (fun p τ => -6 * Derivative.serreDerivative 2 (θG6m p) τ) eG6m
    (fun p τ => by
      rw [serre_T_of_slash (θG6m p) (mdifferentiable_θG6m p) _ (θG6m_slash_T p) τ]
      ring) τ
  exact h

/-- **Covariance of `F = -6 ∂₂Θ/η⁸` for `G₆⁻`**, given `σ(S) = Sθ`, `σ(T) = Tθ`. -/
theorem FFG6m_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθG6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FFG6m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FFG6m τ :=
  covariant_of_S_T σ FFG6m (fun τ => by rw [hσS]; exact FFG6m_S τ)
    (fun τ => by rw [hσT]; exact FFG6m_T τ)

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.serre_finset_sum
#print axioms HaagerupIzumi.C8.Theta.serre_S_of_slash
#print axioms HaagerupIzumi.C8.Theta.serreThetaG7m_S
#print axioms HaagerupIzumi.C8.Theta.FFG7m_covariant
#print axioms HaagerupIzumi.C8.Theta.FFG6m_covariant
