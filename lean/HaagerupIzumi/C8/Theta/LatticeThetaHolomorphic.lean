module

public import HaagerupIzumi.C8.Theta.LatticeThetaHarmonic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.Notation

@[expose] public section

/-!
# Holomorphy of lattice theta series on the upper half-plane

Part of work item W6 (`C8/ROADMAP.md`).  `Lemma lem:pole-cancellation`
(`Analytic/PoleCancellation.lean`, manuscript lines 3599–3612) needs vector-valued functions
whose components are holomorphic on `ℍ` (`MDiff`).  This file proves that the coset theta
series `latticeTheta G γ` and the weighted series `latticeThetaQ G M γ` are holomorphic on
`{Im τ > 0}` and hence `MDiff` as functions on `ℍ`: on `{Im τ > t}` the terms are bounded by
the summable sequence `exp(-π t Q_G(γ+m))` (times `|Q_M(γ+m)|`), so Mathlib's
`differentiableOn_tsum_of_summable_norm` applies.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex Matrix
open scoped Manifold UpperHalfPlane

namespace HaagerupIzumi.C8
namespace Theta

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem qf_nonneg_of_posDef {G : Matrix d d ℝ} (hG : G.PosDef) (x : d → ℝ) : 0 ≤ qf G x := by
  obtain ⟨P, rfl, -⟩ := exists_factor_of_posDef hG
  rw [qf_transpose_mul_self]
  exact dotProduct_self_nonneg' _

omit [Fintype d] [DecidableEq d] in
/-- Summable translates are pointwise absolutely summable. -/
theorem summable_norm_translates {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f) (x : d → ℝ) :
    Summable fun m : d → ℤ => ‖f (x + intVec m)‖ := by
  let K : TopologicalSpace.Compacts (d → ℝ) := ⟨{x}, isCompact_singleton⟩
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hf K)
  have h := ((f.comp (ContinuousMap.addRight (intVec m))).restrict
    (K : Set (d → ℝ))).norm_coe_le_norm ⟨x, Set.mem_singleton x⟩
  exact h

/-- `‖exp(πiτ r)‖ ≤ exp(-π t r)` for `r ≥ 0` and `Im τ ≥ t`. -/
theorem norm_cexp_pi_I_mul_le {τ : ℂ} {t r : ℝ} (ht : t ≤ τ.im) (hr : 0 ≤ r) :
    ‖cexp (π * I * τ * (r : ℂ))‖ ≤ rexp (-(π * t) * r) := by
  have e : (π : ℂ) * I * τ * (r : ℂ) = -π * (-I * τ) * (r : ℂ) := by ring
  rw [e, norm_cexp_neg_pi_mul, re_neg_I_mul]
  exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg (mul_nonneg pi_pos.le hr) (sub_nonneg.2 ht)])

/-- `Θ_γ` is holomorphic on the upper half-plane. -/
theorem differentiableOn_latticeTheta {G : Matrix d d ℝ} (hG : G.PosDef) (γ : d → ℝ) :
    DifferentiableOn ℂ (latticeTheta G γ) {τ : ℂ | 0 < τ.im} := by
  intro τ₀ hτ₀
  have hτ₀' : 0 < τ₀.im := hτ₀
  have hU : IsOpen {τ : ℂ | τ₀.im / 2 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hu := summable_norm_cexp_qf hG (b := ((τ₀.im / 2 : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; linarith) γ
  have hdiff : DifferentiableOn ℂ
      (fun τ : ℂ => ∑' m : d → ℤ, cexp (π * I * τ * (qf G (γ + intVec m) : ℂ)))
      {τ : ℂ | τ₀.im / 2 < τ.im} := by
    refine differentiableOn_tsum_of_summable_norm hu (fun m => ?_) hU (fun m τ hτ => ?_)
    · exact (by fun_prop : Differentiable ℂ fun τ : ℂ =>
        cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))).differentiableOn
    · rw [norm_cexp_neg_pi_mul, Complex.ofReal_re]
      exact norm_cexp_pi_I_mul_le (le_of_lt hτ) (qf_nonneg_of_posDef hG _)
  exact (hdiff.differentiableAt (hU.mem_nhds (show τ₀.im / 2 < τ₀.im by linarith))
    ).differentiableWithinAt

/-- `Θ_{M,γ}` is holomorphic on the upper half-plane. -/
theorem differentiableOn_latticeThetaQ {G : Matrix d d ℝ} (hG : G.PosDef) (M : Matrix d d ℝ)
    (γ : d → ℝ) : DifferentiableOn ℂ (latticeThetaQ G M γ) {τ : ℂ | 0 < τ.im} := by
  obtain ⟨P, rfl, hdet⟩ := exists_factor_of_posDef hG
  intro τ₀ hτ₀
  have hτ₀' : 0 < τ₀.im := hτ₀
  have hU : IsOpen {τ : ℂ | τ₀.im / 2 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hu := summable_norm_translates (translatesSummable_qgaussCM hdet
    (a := ((τ₀.im / 2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; linarith) M) γ
  have hdiff : DifferentiableOn ℂ
      (fun τ : ℂ => ∑' m : d → ℤ, (qf M (γ + intVec m) : ℂ) *
        cexp (π * I * τ * (qf (Pᵀ * P) (γ + intVec m) : ℂ)))
      {τ : ℂ | τ₀.im / 2 < τ.im} := by
    refine differentiableOn_tsum_of_summable_norm hu (fun m => ?_) hU (fun m τ hτ => ?_)
    · exact (by fun_prop : Differentiable ℂ fun τ : ℂ => (qf M (γ + intVec m) : ℂ) *
        cexp (π * I * τ * (qf (Pᵀ * P) (γ + intVec m) : ℂ))).differentiableOn
    · rw [qgaussCM_apply, gaussCM_apply, norm_mul, norm_mul, norm_cexp_neg_pi_mul,
        Complex.ofReal_re, ← qf_transpose_mul_self]
      exact mul_le_mul_of_nonneg_left
        (norm_cexp_pi_I_mul_le (le_of_lt hτ) (qf_nonneg_of_posDef hG _)) (norm_nonneg _)
  exact (hdiff.differentiableAt (hU.mem_nhds (show τ₀.im / 2 < τ₀.im by linarith))
    ).differentiableWithinAt

/-- `τ ↦ Θ_γ(τ)` is holomorphic on `ℍ` (the hypothesis shape of `pole_cancellation`). -/
theorem mdifferentiable_latticeTheta {G : Matrix d d ℝ} (hG : G.PosDef) (γ : d → ℝ) :
    MDiff (fun τ : ℍ => latticeTheta G γ τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_latticeTheta hG γ).congr fun z hz => ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- `τ ↦ Θ_{M,γ}(τ)` is holomorphic on `ℍ`. -/
theorem mdifferentiable_latticeThetaQ {G : Matrix d d ℝ} (hG : G.PosDef) (M : Matrix d d ℝ)
    (γ : d → ℝ) : MDiff (fun τ : ℍ => latticeThetaQ G M γ τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_latticeThetaQ hG M γ).congr fun z hz => ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.differentiableOn_latticeTheta
#print axioms HaagerupIzumi.C8.Theta.differentiableOn_latticeThetaQ
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_latticeTheta
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_latticeThetaQ
