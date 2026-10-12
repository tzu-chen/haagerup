module

public import HaagerupIzumi.C8.Theta.SerreTheta
public import HaagerupIzumi.C8.Theta.QExpansion

@[expose] public section

/-!
# The derivative `D Θ = q dΘ/dq` of a coset theta series

W6 plan item 3, `F = -6 D₂ Θ` (`Theta/W6_PLAN.md`), toward the coefficients
`minusSixD2Coeff` of Tables 2 and 4 (lines 3690–3705, 3760–3766 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).

* `deriv_latticeTheta`: termwise differentiation, `dΘ_γ/dτ = πi Θ_{G,γ}` where `Θ_{G,γ}` is the
  theta series with the weight `Q_G` itself (`latticeThetaQ G G γ`);
* `normDeriv_latticeTheta`: Mathlib's normalized derivative `D = (2πi)⁻¹ d/dτ` gives
  `D Θ_γ = Θ_{G,γ}/2`;
* `normDeriv_theta_qexp`: `D Θ_{g+L} = ∑_e e · N_{g+L}(e) q^e` (`N = thetaCount`), the first
  term `-6 e θ(e)` of `minusSixD2Coeff` after multiplication by `-6`;
* `minusSix_serre_eq`: `-6 ∂₂Θ = -6 DΘ + E₂ Θ` (`∂₂ = D - E₂/6`, Mathlib's
  `serreDerivative 2`).

Still to do for the `F` orientations: the Cauchy product of `E₂ = ∑ e2Coeff n qⁿ`
(`EisensteinSeries.E2_eq_tsum_cexp`) with `Θ`.  Nothing here is an external hypothesis.
-/

noncomputable section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

section Deriv

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Termwise derivative**: `dΘ_γ/dτ = πi ∑_m Q_G(γ+m) exp(πiτ Q_G(γ+m))`. -/
theorem deriv_latticeTheta {G : Matrix d d ℝ} (hG : G.PosDef) (γ : d → ℝ) {τ₀ : ℂ}
    (hτ₀ : 0 < τ₀.im) : deriv (latticeTheta G γ) τ₀ = π * I * latticeThetaQ G G γ τ₀ := by
  have hU : IsOpen {τ : ℂ | τ₀.im / 2 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hu := summable_norm_cexp_qf hG (b := ((τ₀.im / 2 : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; linarith) γ
  have hs := hasSum_deriv_of_summable_norm hu
    (F := fun (m : d → ℤ) (τ : ℂ) => cexp (π * I * τ * (qf G (γ + intVec m) : ℂ)))
    (fun m => (by fun_prop : Differentiable ℂ fun τ : ℂ =>
      cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))).differentiableOn) hU
    (fun m τ hτ => by
      rw [norm_cexp_neg_pi_mul, Complex.ofReal_re]
      exact norm_cexp_pi_I_mul_le (le_of_lt hτ) (qf_nonneg_of_posDef hG _))
    (show τ₀.im / 2 < τ₀.im by linarith)
  have hterm : ∀ m : d → ℤ, deriv (fun τ : ℂ => cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))) τ₀ =
      π * I * ((qf G (γ + intVec m) : ℂ) * cexp (π * I * τ₀ * (qf G (γ + intVec m) : ℂ))) := by
    intro m
    have h : HasDerivAt (fun τ : ℂ => cexp (π * I * τ * (qf G (γ + intVec m) : ℂ)))
        (cexp (π * I * τ₀ * (qf G (γ + intVec m) : ℂ)) * (π * I * 1 * (qf G (γ + intVec m) : ℂ)))
        τ₀ :=
      (((hasDerivAt_id τ₀).const_mul ((π : ℂ) * I)).mul_const (qf G (γ + intVec m) : ℂ)).cexp
    rw [h.deriv]
    ring
  show deriv (fun τ : ℂ => ∑' m : d → ℤ, cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))) τ₀ = _
  rw [← hs.tsum_eq]
  simp only [hterm]
  rw [tsum_mul_left]
  rfl

/-- **`D Θ_γ = Θ_{G,γ}/2`** for Mathlib's normalized derivative `D = (2πi)⁻¹ d/dτ`. -/
theorem normDeriv_latticeTheta {G : Matrix d d ℝ} (hG : G.PosDef) (γ : d → ℝ) (z : ℍ) :
    Derivative.normalizedDerivOfComplex (fun τ : ℍ => latticeTheta G γ τ) z =
      (1 / 2 : ℂ) * latticeThetaQ G G γ z := by
  unfold Derivative.normalizedDerivOfComplex
  have heq : ((fun τ : ℍ => latticeTheta G γ τ) ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (z : ℂ)]
      latticeTheta G γ := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rw [heq.deriv_eq, deriv_latticeTheta hG γ z.im_pos]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

end Deriv

/-- On a shell of energy `e`, the weight `quadOf G = (x, x)` is `2e`. -/
theorem thetaCoeff_quadOf_gram (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (e : ℚ) :
    thetaCoeff Gz g (quadOf (Gz.map (Int.cast : ℤ → ℚ))) e = 2 * e * thetaCount Gz g e := by
  unfold thetaCount thetaCoeff
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun n hn => ?_
  rw [← dotProduct_mulVec_eq_quadOf, dotProduct_map_mulVec_eq_gramNorm, mul_one]
  have h : energy Gz (cosetPt g n) = e := hn
  rw [energy] at h
  linarith

/-- **`q`-expansion of `D Θ`**: `D Θ_{g+L} = ∑_e e N_{g+L}(e) q^e`. -/
theorem normDeriv_theta_qexp {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (g : Fin 4 → ℚ) (z : ℍ) :
    Derivative.normalizedDerivOfComplex (fun τ : ℍ => latticeTheta (gramR Gz) (ratVec g) τ) z =
      ∑' e : ℚ, ((e * thetaCount Gz g e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * z) := by
  rw [normDeriv_latticeTheta hG]
  have hM : gramR Gz = (Gz.map (Int.cast : ℤ → ℚ)).map (Rat.cast : ℚ → ℝ) := by
    ext i j
    simp [gramR]
  have h := latticeThetaQ_eq_tsum_thetaCoeff hG (Gz.map (Int.cast : ℤ → ℚ)) g z.im_pos
  rw [← hM] at h
  rw [h, ← tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [thetaCoeff_quadOf_gram]
  push_cast
  ring

/-- `-6 ∂₂Θ = -6 DΘ + E₂ Θ` (`∂₂ = D - (2/12) E₂`). -/
theorem minusSix_serre_eq (F : ℍ → ℂ) (z : ℍ) :
    -6 * Derivative.serreDerivative 2 F z =
      -6 * Derivative.normalizedDerivOfComplex F z + EisensteinSeries.E2 z * F z := by
  rw [Derivative.serreDerivative_apply]
  ring

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.deriv_latticeTheta
#print axioms HaagerupIzumi.C8.Theta.normDeriv_latticeTheta
#print axioms HaagerupIzumi.C8.Theta.normDeriv_theta_qexp
#print axioms HaagerupIzumi.C8.Theta.minusSix_serre_eq
