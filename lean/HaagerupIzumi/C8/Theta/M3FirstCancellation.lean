module

public import HaagerupIzumi.C8.Theta.RemainderBound
public import HaagerupIzumi.C8.Analytic.PoleCancellation

@[expose] public section

/-!
# `m = 3`, first orientation: `dim U₁ = 15 + A + 10B` from pole cancellation

W6 plan items 1–4 assembled for Table 1 (`L₇ ⊕ A₂`) of the proof of Proposition
`prop:near-group-current-obstructions` (lines 3629–3681 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  The identity `hcancel` is *derived* from
`pole_cancellation` (`Analytic/PoleCancellation`) on the even block; its integer-label form,
the hypothesis `hcancel` of `m3_first_obstruction`, is `m3_first_hcancel_table_of_voa`
(`Theta/ObstructionsOfVoa`, via the links of `Theta/TableLinks`), with

* the theta side fully proved: the even-block vector `λ F_{H₁} + μ F_{H₂}` (`GL7A2`,
  `λ = 7 - A + 4B`, `μ = 7 - A - 3B` as in line 3674) is holomorphic, `σ`-covariant for any
  `σ` with `σ(S) = SθEL7A2`, `σ(T) = TθEL7A2`, and has no invariant vector; its complete
  polar part is the vacuum entry and the two Table 1 rows (`polar_L7A2`); the remainder is
  bounded at `i∞` (`isBoundedAtImInfty_tsum_div_eta8`);
* the VOA side as named hypotheses (`m3_first_dimension_of_voa`):
  - `σ : SL(2, ℤ) → GL(E, ℂ)` on the even block `E = Fin 4 × Fin 2` with
    `σ(S) = SθEL7A2`, `σ(T) = TθEL7A2` (`hσS`, `hσT`: the VOA-side identification — Zhu
    modularity of the character vector, Huang's identification of Zhu's `S` with the
    categorical `S`, and the comparison with the modular data) and with finite image (`hfin`);
    since `σ` is pinned at the generators, `hfin` is a property of the explicit Weil-type
    matrices (manuscript lines 3772–3774), not a VOA input;
  - the difference vector `V = δv` (weight `0`), holomorphic (`hVhol`) and covariant
    (`hVcov`);
  - its `η⁸`-multiplied `q`-expansion `η⁸ V_e = ∑ δc e x q^x` (`hVq`), supported on
    `λ_e + ℕ` (`hsupp`), absolutely convergent (`hsum`);
  - the polar data: vacuum `δc (0,0) 0 = 0`, `δc (1,0) (1/7) = -B - 0`,
    `δc (3,0) (2/7) = -A - (-7)` (polar tops `B`, `A`, reference `A = 7`, `B = 0`), and no
    other polar coefficient (`hother`); the vacuum coefficient `δc (0,0) 1 = 2(dim U₁ - 22)`.

Conclusion: `dim U₁ = 15 + A + 10B`.  Also `δc` agrees with the theta coefficients everywhere
(`m3_first_hcancel_of_voa`), i.e. `hcancel` holds on the even block.
-/

noncomputable section

open Complex Matrix ModularGroup
open scoped MatrixGroups UpperHalfPlane Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

/-- The coset of the even-block label `e`. -/
abbrev cosetEL7A2 (e : Fin 4 × Fin 2) : Fin 4 → ℚ :=
  cosetL7A2 (((ιL7A2 e).1 : ℕ) : ℤ) (((ιL7A2 e).2 : ℕ) : ℤ)

theorem thetaQL7A2_ι_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 × Fin 2) {τ : ℂ}
    (hτ : 0 < τ.im) :
    thetaQL7A2 M (ιL7A2 e) τ = ∑' x : ℚ,
      ((thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf M) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  latticeThetaQ_eq_tsum_thetaCoeff posDef_L7A2 M _ hτ

/-- The theta side `λ F_{H₁} + μ F_{H₂}` on the even block. -/
def GL7A2 (l m : ℚ) (τ : ℍ) : Fin 4 × Fin 2 → ℂ :=
  (l : ℂ) • FEL7A2 MH1 τ + (m : ℂ) • FEL7A2 MH2 τ

theorem GL7A2_apply (l m : ℚ) (τ : ℍ) (e : Fin 4 × Fin 2) :
    GL7A2 l m τ e =
      ((l : ℂ) * thetaQL7A2 MH1 (ιL7A2 e) τ + (m : ℂ) * thetaQL7A2 MH2 (ιL7A2 e) τ) /
        eta8 τ := by
  simp only [GL7A2, FEL7A2, FL7A2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem GL7A2_covariant (l m : ℚ)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEL7A2) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), GL7A2 l m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ GL7A2 l m τ := by
  intro γ τ
  rw [GL7A2, GL7A2, FEL7A2_covariant harmonic_quadratics.2.1 iso_MH1 σ hσS hσT γ τ,
    FEL7A2_covariant harmonic_quadratics.2.2.1 iso_MH2 σ hσS hσT γ τ, mulVec_add, mulVec_smul,
    mulVec_smul]

theorem mdifferentiable_GL7A2 (l m : ℚ) (e : Fin 4 × Fin 2) :
    MDiff (fun τ : ℍ => GL7A2 l m τ e) := by
  have h : (fun τ : ℍ => GL7A2 l m τ e) = fun τ : ℍ =>
      (fun z : ℂ => (l : ℂ) * thetaQL7A2 MH1 (ιL7A2 e) z + (m : ℂ) * thetaQL7A2 MH2 (ιL7A2 e) z)
        τ / eta8 τ :=
    funext fun τ => GL7A2_apply l m τ e
  rw [h]
  exact mdifferentiable_div_eta8
    (((differentiableOn_latticeThetaQ posDef_L7A2 _ _).const_mul _).add
      ((differentiableOn_latticeThetaQ posDef_L7A2 _ _).const_mul _))

/-- The polar entries of `polar_L7A2` that lie in the even block (kernel-checked). -/
theorem ι_polar_L7A2 (e : Fin 4 × Fin 2) (x : ℚ)
    (h : (ιL7A2 e = (0, 0) ∧ x = 0) ∨ ((ιL7A2 e = (1, 0) ∨ ιL7A2 e = (6, 0)) ∧ x = 1 / 7) ∨
      ((ιL7A2 e = (3, 0) ∨ ιL7A2 e = (4, 0)) ∧ x = 2 / 7)) :
    (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 7) ∨ (e = (3, 0) ∧ x = 2 / 7) := by
  have hι : ∀ e : Fin 4 × Fin 2, (ιL7A2 e = (0, 0) → e = (0, 0)) ∧
      (ιL7A2 e = (1, 0) → e = (1, 0)) ∧ ιL7A2 e ≠ (6, 0) ∧ (ιL7A2 e = (3, 0) → e = (3, 0)) ∧
        ιL7A2 e ≠ (4, 0) := by
    decide +kernel
  obtain ⟨h0, h1, h6, h3, h4⟩ := hι e
  rcases h with ⟨ha, hb⟩ | ⟨ha | ha, hb⟩ | ⟨ha | ha, hb⟩
  · exact Or.inl ⟨h0 ha, hb⟩
  · exact Or.inr (Or.inl ⟨h1 ha, hb⟩)
  · exact absurd ha h6
  · exact Or.inr (Or.inr ⟨h3 ha, hb⟩)
  · exact absurd ha h4

theorem quadOf_zero (M : Matrix (Fin 4) (Fin 4) ℚ) : quadOf M 0 = 0 := by
  simp [quadOf]

theorem thetaCoeff_L7A2_support_E (M : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 × Fin 2) (x : ℚ)
    (h : thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf M) x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramL7A2 (cosetEL7A2 e) :=
  thetaCoeff_support_nat posDef_L7A2 even_L7A2 (ratVec_cosetL7A2_eq_inv _ _) _
    (lamOf_nonpos _ _) (lamOf_congr _ _) _ x h

/-- **`m = 3`, first orientation, from pole cancellation**: `hcancel` on the even block. -/
theorem m3_first_hcancel_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEL7A2)
    (V : ℍ → Fin 4 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 4 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramL7A2 (cosetEL7A2 e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A B : ℕ) (hvac0 : δc (0, 0) 0 = 0) (hpolarB : δc (1, 0) (1 / 7) = -(B : ℚ) - 0)
    (hpolarA : δc (3, 0) (2 / 7) = -(A : ℚ) - (-7))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 7) ∨ (e = (3, 0) ∧ x = 2 / 7)) :
    ∀ e x, δc e x = lamM3First A B * thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH1) x +
      muM3First A B * thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH2) x := by
  set l := lamM3First A B with hl
  set m := muM3First A B with hm
  -- the remainder coefficients vanish below `1/3`
  have hrem : ∀ e x, x < 1 / 3 →
      δc e x - l * thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH1) x -
        m * thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH2) x = 0 := by
    intro e x hx
    by_contra hne
    have hcases : (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 7) ∨ (e = (3, 0) ∧ x = 2 / 7) := by
      by_cases hd : δc e x = 0
      · have ht : thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH1) x ≠ 0 ∨
            thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH2) x ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hne
          rw [hd, hcon.1, hcon.2]
          ring
        rcases ht with ht | ht
        · exact ι_polar_L7A2 e x (polar_L7A2 (ιL7A2 e) hx ht)
        · exact ι_polar_L7A2 e x (polar_L7A2 (ιL7A2 e) hx ht)
      · exact hother e x hx hd
    apply hne
    obtain ⟨-, hB, hA⟩ := m3First_polar_match A B
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hvac0, thetaCoeff_at_zero posDef_L7A2 _ (quadOf_zero MH1),
        thetaCoeff_at_zero posDef_L7A2 _ (quadOf_zero MH2)]
      ring
    · have hc : cosetEL7A2 (1, 0) = cosetL7A2 1 0 := by decide +kernel
      rw [hc, ← H1_eq_quadOf, ← H2_eq_quadOf, hpolarB]
      linarith
    · have hc : cosetEL7A2 (3, 0) = cosetL7A2 3 0 := by decide +kernel
      rw [hc, ← H1_eq_quadOf, ← H2_eq_quadOf, hpolarA]
      linarith
  -- the remainder as a `q`-series divided by `η⁸`
  have hdiff : ∀ e (τ : ℍ), V τ e - GL7A2 l m τ e =
      (∑' x : ℚ, (((δc e x : ℚ) : ℂ) -
        (l : ℂ) * ((thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH1) x : ℚ) : ℂ) -
        (m : ℂ) * ((thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH2) x : ℚ) : ℂ)) *
          cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ := by
    intro e τ
    have hη := eta8_ne_zero τ.im_pos
    have key := tsum_sub_lincomb (fun x => ((δc e x : ℚ) : ℂ))
      (fun x => ((thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH1) x : ℚ) : ℂ))
      (fun x => ((thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH2) x : ℚ) : ℂ)) (l : ℂ) (m : ℂ)
      (hsum e) (fun y hy => summable_norm_thetaCoeff posDef_L7A2 MH1 _ hy)
      (fun y hy => summable_norm_thetaCoeff posDef_L7A2 MH2 _ hy) τ
    rw [← key, ← hVq e τ, ← thetaQL7A2_ι_eq_tsum MH1 e τ.im_pos,
      ← thetaQL7A2_ι_eq_tsum MH2 e τ.im_pos, GL7A2_apply, eq_div_iff hη, sub_mul,
      div_mul_cancel₀ _ hη]
    ring
  have hpp : ∀ e, UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => V τ e - GL7A2 l m τ e) := by
    intro e
    rw [funext (hdiff e)]
    refine isBoundedAtImInfty_tsum_div_eta8 _ (fun x hx => ?_) (y₀ := 1)
      (summable_lincomb _ _ _ _ _ (hsum e 1 one_pos)
        (summable_norm_thetaCoeff posDef_L7A2 MH1 _ one_pos)
        (summable_norm_thetaCoeff posDef_L7A2 MH2 _ one_pos))
    by_contra hlt
    push Not at hlt
    apply hx
    have h0 := hrem e x hlt
    have h0' : (((δc e x - l * thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH1) x -
        m * thetaCoeff gramL7A2 (cosetEL7A2 e) (quadOf MH2) x : ℚ)) : ℂ) = 0 := by
      rw [h0, Rat.cast_zero]
    push_cast at h0'
    exact h0'
  have hVG : V = GL7A2 l m :=
    pole_cancellation σ hfin (noInvariantE_sigma_L7A2 σ hσS hσT) V (GL7A2 l m) hVhol
      (mdifferentiable_GL7A2 l m) hVcov (GL7A2_covariant l m σ hσS hσT) hpp
  -- coefficient extraction
  intro e
  refine qcoeff_eq_lincomb (lamOf gramL7A2 (cosetEL7A2 e)) (δc e) _ _ l m (hsupp e)
    (thetaCoeff_L7A2_support_E MH1 e) (thetaCoeff_L7A2_support_E MH2 e) (hsum e)
    (fun y hy => summable_norm_thetaCoeff posDef_L7A2 MH1 _ hy)
    (fun y hy => summable_norm_thetaCoeff posDef_L7A2 MH2 _ hy) fun τ => ?_
  have hη := eta8_ne_zero τ.im_pos
  rw [← hVq e τ, hVG, GL7A2_apply, ← thetaQL7A2_ι_eq_tsum MH1 e τ.im_pos,
    ← thetaQL7A2_ι_eq_tsum MH2 e τ.im_pos, mul_div_cancel₀ _ hη]

/-- **`m = 3`, first orientation: `dim U₁ = 15 + A + 10B`**, with `hcancel` derived from pole
cancellation; the remaining hypotheses are the VOA-side inputs listed in the module docstring
and the vacuum coefficient `hvac`. -/
theorem m3_first_dimension_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEL7A2)
    (V : ℍ → Fin 4 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 4 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramL7A2 (cosetEL7A2 e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A B d : ℕ) (hvac0 : δc (0, 0) 0 = 0) (hpolarB : δc (1, 0) (1 / 7) = -(B : ℚ) - 0)
    (hpolarA : δc (3, 0) (2 / 7) = -(A : ℚ) - (-7))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 7) ∨ (e = (3, 0) ∧ x = 2 / 7))
    (hvac : δc (0, 0) 1 = 2 * ((d : ℚ) - 22)) :
    d = 15 + A + 10 * B := by
  have h := m3_first_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A B hvac0
    hpolarB hpolarA hother (0, 0) 1
  have hc : cosetEL7A2 (0, 0) = cosetL7A2 0 0 := by decide +kernel
  rw [hc, ← H1_eq_quadOf, ← H2_eq_quadOf, m3First_H1_00, m3First_H2_00, hvac] at h
  unfold lamM3First muM3First at h
  have hd : (d : ℚ) = 15 + A + 10 * B := by linarith
  exact_mod_cast hd

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.GL7A2_covariant
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_GL7A2
#print axioms HaagerupIzumi.C8.Theta.m3_first_hcancel_of_voa
#print axioms HaagerupIzumi.C8.Theta.m3_first_dimension_of_voa
