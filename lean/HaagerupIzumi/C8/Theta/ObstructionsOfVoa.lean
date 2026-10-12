module

public import HaagerupIzumi.C8.Theta.TableLinks
public import HaagerupIzumi.C8.Theta.M6ReverseSym

@[expose] public section

/-!
# The four near-group current obstructions without `hcancel`

Proposition `prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  The obstruction theorems
`m3_first_obstruction`, `m3_reverse_obstruction`, `m6_first_obstruction`,
`m6_reverse_obstruction` (`Theta/M3First` … `M6Reverse`) assume `hcancel`, the output of
Lemma `lem:pole-cancellation`.  Here `hcancel` is **proved** from the capstones
`m*_hcancel_of_voa` (pole cancellation applied on the even blocks) through the link lemmas of
`Theta/TableLinks`, and the existing obstruction theorems are applied to it:

* `m3_first_obstruction_of_voa`: `dim U₁ = 15 + A + 10B`;
* `m3_reverse_obstruction_of_voa`: `dim U₁ = 14 + 42A`;
* `m6_first_obstruction_of_voa`: `dim U₁ = 8 + A`;
* `m6_reverse_obstruction_of_voa`: `dim U₁ = 5 + 12P`;

and `m*_hcancel_table_of_voa`, the hypotheses `hcancel` in the exact form of the table files.

The table coordinate functions are the VOA coefficients read at the even-block representative
of the integer label: `δcTableL7A2 δc r s = δc (πL7A2 (r mod 7, s mod 3))`,
`δcTableA1A1A2`, `cTableG7m δc r s = δc (πG7m (9r + 7s mod 21))`.  For Table 4, whose `hcancel`
quantifies over **all** `g : Fin 4 → ℚ`, `cTableG6m` is `δc` at the label of `g` when `g + L` is
a coset of `L'` (`IsCosetG6m g`), and the theta side otherwise (no VOA coordinate exists there).
Table 4 uses the 6-dimensional swap-symmetric block `Fin 3 × Fin 2` (`Theta/M6ReverseSym`,
`m6_reverse_hcancel_of_voa_sym`), matching the manuscript's `(v₀, v_A, v_B) ⊗ (even pointed
factor)` (lines 3714–3720, 3762–3766).

Remaining hypotheses (named; exactly those of the capstones): a homomorphism
`σ : SL(2, ℤ) → GL(E, ℂ)` on the even block with `σ(S) = SθE*`, `σ(T) = TθE*` (the VOA-side
identification: Zhu modularity of the character vector, Huang's `S`, and the comparison with the
categorical modular data) and with finite image `hfin`; since `σ` is pinned at the generators,
`hfin` is a property of the explicit Weil-type matrices `SθE*`, `TθE*` (manuscript lines
3772–3774), not a VOA input; the weight-zero VOA vector `V` (holomorphic, `σ`-covariant); its
`η⁸`-multiplied `q`-expansion `δc` (support on `λ + ℕ`, absolute convergence); the polar and
vacuum coefficients of `δc` and the vanishing of `δc` at all other entries below `q^{1/3}`.
-/

noncomputable section

open Complex Matrix ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

/-! ## `m = 3`, first orientation (Table 1) -/

/-- Table 1 coordinates `(r, s) ∈ ℤ²` read from the even-block VOA coefficients. -/
def δcTableL7A2 (δc : Fin 4 × Fin 2 → ℚ → ℚ) (r s : ℤ) (e : ℚ) : ℚ :=
  δc (πL7A2 (modL7A2 r s)) e

/-- **`hcancel` of `m3_first_obstruction`**, proved from pole cancellation. -/
theorem m3_first_hcancel_table_of_voa
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
    ∀ r s e, δcTableL7A2 δc r s e = lamM3First A B * thetaCoeff gramL7A2 (cosetL7A2 r s) H1 e
      + muM3First A B * thetaCoeff gramL7A2 (cosetL7A2 r s) H2 e := by
  have hcap := m3_first_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A B
    hvac0 hpolarB hpolarA hother
  intro r s e
  rw [H1_eq_quadOf, H2_eq_quadOf, thetaCoeff_L7A2_link iso_MH1, thetaCoeff_L7A2_link iso_MH2]
  exact hcap _ e

/-- **`m = 3`, first orientation, without `hcancel`**: `dim U₁ = 15 + A + 10B`, by
`m3_first_obstruction` applied to `hcancel := m3_first_hcancel_table_of_voa`. -/
theorem m3_first_obstruction_of_voa
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
  have hc := m3_first_hcancel_table_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A B
    hvac0 hpolarB hpolarA hother
  have h10 : πL7A2 (modL7A2 1 0) = (1, 0) := by decide +kernel
  have h30 : πL7A2 (modL7A2 3 0) = (3, 0) := by decide +kernel
  have h00 : πL7A2 (modL7A2 0 0) = (0, 0) := by decide +kernel
  refine (m3_first_obstruction (δcTableL7A2 δc) A B d _ _ hc ?_ ?_ ?_).2.2
  · show δc (πL7A2 (modL7A2 1 0)) (1 / 7) = _
    rw [h10]
    exact hpolarB
  · show δc (πL7A2 (modL7A2 3 0)) (2 / 7) = _
    rw [h30]
    exact hpolarA
  · show δc (πL7A2 (modL7A2 0 0)) 1 = _
    rw [h00]
    exact hvac

/-! ## `m = 6`, first orientation (Table 3) -/

/-- Table 3 coordinates `(a, b, s) ∈ ℤ³` read from the even-block VOA coefficients. -/
def δcTableA1A1A2 (δc : Fin 3 × Fin 2 → ℚ → ℚ) (a b s : ℤ) (e : ℚ) : ℚ :=
  δc (πA1A1A2 (modA1A1A2 a b s)) e

/-- **`hcancel` of `m6_first_obstruction`**, proved from pole cancellation. -/
theorem m6_first_hcancel_table_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramA1A1A2 (cosetEA1A1A2 e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A : ℕ) (hvac0 : δc (0, 0) 0 = 0)
    (hpolar : δc (1, 0) (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4)) :
    ∀ a b s e, δcTableA1A1A2 δc a b s e = kappaM6First A * PThetaA1A1A2 a b s e := by
  have hcap := m6_first_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A hvac0
    hpolar hother
  intro a b s e
  rw [PThetaA1A1A2_link]
  exact hcap _ e

/-- **`m = 6`, first orientation, without `hcancel`**: `dim U₁ = 8 + A`, by
`m6_first_obstruction` applied to `hcancel := m6_first_hcancel_table_of_voa`. -/
theorem m6_first_obstruction_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramA1A1A2 (cosetEA1A1A2 e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A d : ℕ) (hvac0 : δc (0, 0) 0 = 0)
    (hpolar : δc (1, 0) (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4))
    (hvac : δc (0, 0) 1 = 2 * ((d : ℚ) - 16)) :
    d = 8 + A := by
  have hc := m6_first_hcancel_table_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A
    hvac0 hpolar hother
  have h100 : πA1A1A2 (modA1A1A2 1 0 0) = (1, 0) := by decide +kernel
  have h000 : πA1A1A2 (modA1A1A2 0 0 0) = (0, 0) := by decide +kernel
  refine (m6_first_obstruction (δcTableA1A1A2 δc) A d _ hc ?_ ?_).2
  · show δc (πA1A1A2 (modA1A1A2 1 0 0)) (1 / 4) = _
    rw [h100]
    exact hpolar
  · show δc (πA1A1A2 (modA1A1A2 0 0 0)) 1 = _
    rw [h000]
    exact hvac

/-! ## `m = 3`, reverse orientation (Table 2) -/

/-- Table 2 coordinates `(r, s) ∈ ℤ²` (the coset `(9r + 7s) ℓ`) read from the even-block VOA
coefficients. -/
def cTableG7m (δc : Fin 4 × Fin 2 → ℚ → ℚ) (r s : ℤ) (e : ℚ) : ℚ :=
  δc (πG7m (modG7m (9 * r + 7 * s))) e

/-- **`hcancel` of `m3_reverse_obstruction`**, proved from pole cancellation. -/
theorem m3_reverse_hcancel_table_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m)
    (V : ℍ → Fin 4 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 4 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 →
      ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (2 / 21) = -(A : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21)) :
    ∀ r s e, cTableG7m δc r s e = phiM3Reverse * PFG7m r s e + kappaM3Reverse A * PThetaG7m r s e := by
  have hcap := m3_reverse_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A hvac0
    hpolar hother
  intro r s e
  rw [PFG7m_link, PThetaG7m_link]
  exact hcap _ e

/-- **`m = 3`, reverse orientation, without `hcancel`**: `dim U₁ = 14 + 42A`, by
`m3_reverse_obstruction` applied to `hcancel := m3_reverse_hcancel_table_of_voa`. -/
theorem m3_reverse_obstruction_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m)
    (V : ℍ → Fin 4 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 4 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 →
      ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A d : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (2 / 21) = -(A : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21))
    (hvac1 : δc (0, 0) 1 = 2 * (d : ℚ) - 94) :
    d = 14 + 42 * A := by
  have hc := m3_reverse_hcancel_table_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A
    hvac0 hpolar hother
  have h00 : πG7m (modG7m (9 * 0 + 7 * 0)) = (0, 0) := by decide +kernel
  have h21 : πG7m (modG7m (9 * 2 + 7 * 1)) = (2, 1) := by decide +kernel
  refine (m3_reverse_obstruction (cTableG7m δc) A d _ _ hc ?_ ?_ ?_).2.2
  · show δc (πG7m (modG7m (9 * 0 + 7 * 0))) 0 = _
    rw [h00]
    exact hvac0
  · show δc (πG7m (modG7m (9 * 0 + 7 * 0))) 1 = _
    rw [h00]
    exact hvac1
  · show δc (πG7m (modG7m (9 * 2 + 7 * 1))) (2 / 21) = _
    rw [h21]
    exact hpolar

/-! ## `m = 6`, reverse orientation (Table 4) -/

/-- `g + L` is a coset of `L'`, in the coordinates of Table 4: `g ∈ cosetG6m p + ℤ⁴`. -/
def IsCosetG6m (g : Fin 4 → ℚ) : Prop :=
  ∃ p : Fin 2 × Fin 2 × Fin 3, ∃ n : Fin 4 → ℤ,
    g = cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n

open Classical in
/-- Table 4 coordinates `g : Fin 4 → ℚ`: the VOA coefficient at the label (in the
swap-symmetric block) of `g + L` when it is a coset of `L'`; elsewhere (where `hcancel` of
`m6_reverse_obstruction` also quantifies, but no VOA coordinate exists) the theta side. -/
def cTableG6m (δc : Fin 3 × Fin 2 → ℚ → ℚ) (φ κ : ℚ) (g : Fin 4 → ℚ) (e : ℚ) : ℚ :=
  if h : IsCosetG6m g then δc (πA1A1A2 (Classical.choose h)) e
  else φ * PFG6m g e + κ * PThetaG6m g e

theorem cTableG6m_hcancel (δc : Fin 3 × Fin 2 → ℚ → ℚ) (P : ℕ)
    (hcap : ∀ e x, δc e x = phiM6Reverse * minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x +
      kappaM6Reverse P * thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x) :
    ∀ g e, cTableG6m δc phiM6Reverse (kappaM6Reverse P) g e =
      phiM6Reverse * PFG6m g e + kappaM6Reverse P * PThetaG6m g e := by
  intro g e
  by_cases h : IsCosetG6m g
  · rw [cTableG6m, dif_pos h]
    obtain ⟨n, hn⟩ := Classical.choose_spec h
    rw [hcap, PFG6m_link_sym hn, PThetaG6m_link_sym hn]
  · rw [cTableG6m, dif_neg h]

theorem cTableG6m_at (δc : Fin 3 × Fin 2 → ℚ → ℚ) (P : ℕ)
    (hcap : ∀ e x, δc e x = phiM6Reverse * minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x +
      kappaM6Reverse P * thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x)
    {g : Fin 4 → ℚ} {p : Fin 2 × Fin 2 × Fin 3} {n : Fin 4 → ℤ}
    (hg : g = cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n)
    (x : ℚ) : cTableG6m δc phiM6Reverse (kappaM6Reverse P) g x = δc (πA1A1A2 p) x := by
  rw [cTableG6m_hcancel δc P hcap, PFG6m_link_sym hg, PThetaG6m_link_sym hg, hcap]

/-- **`hcancel` of `m6_reverse_obstruction`**, proved from pole cancellation on the
6-dimensional swap-symmetric block. -/
theorem m6_reverse_hcancel_table_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (P : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (1 / 6) = -(P : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6)) :
    ∀ g e, cTableG6m δc phiM6Reverse (kappaM6Reverse P) g e =
      phiM6Reverse * PFG6m g e + kappaM6Reverse P * PThetaG6m g e :=
  cTableG6m_hcancel δc P (m6_reverse_hcancel_of_voa_sym σ hfin hσS hσT V hVhol hVcov δc hVq
    hsupp hsum P hvac0 hpolar hother)

/-- **`m = 6`, reverse orientation, without `hcancel`**: `dim U₁ = 5 + 12P`, by
`m6_reverse_obstruction` applied to `hcancel := m6_reverse_hcancel_table_of_voa`. -/
theorem m6_reverse_obstruction_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (P d : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (1 / 6) = -(P : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6))
    (hvac1 : δc (0, 0) 1 = 2 * (d : ℚ) - 94) :
    d = 5 + 12 * P := by
  have hcap := m6_reverse_hcancel_of_voa_sym σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum P
    hvac0 hpolar hother
  have h0 : (0 : Fin 4 → ℚ) = cosetPt (cosetG6m (((0 : Fin 2) : ℕ) : ℤ) (((0 : Fin 2) : ℕ) : ℤ)
      (((0 : Fin 3) : ℕ) : ℤ)) 0 := by decide +kernel
  have hp : polarG6m = cosetPt (cosetG6m (((1 : Fin 2) : ℕ) : ℤ) (((1 : Fin 2) : ℕ) : ℤ)
      (((1 : Fin 3) : ℕ) : ℤ)) ![-1, -1, -1, -1] := by decide +kernel
  have hπ0 : πA1A1A2 ((0, 0, 0) : Fin 2 × Fin 2 × Fin 3) = (0, 0) := by decide +kernel
  have hπ1 : πA1A1A2 ((1, 1, 1) : Fin 2 × Fin 2 × Fin 3) = (2, 1) := by decide +kernel
  refine (m6_reverse_obstruction (cTableG6m δc phiM6Reverse (kappaM6Reverse P)) P d _ _
    (cTableG6m_hcancel δc P hcap) ?_ ?_ ?_).2.2
  · rw [cTableG6m_at δc P hcap (p := (0, 0, 0)) h0, hπ0, hvac0]
  · rw [cTableG6m_at δc P hcap (p := (0, 0, 0)) h0, hπ0, hvac1]
  · rw [cTableG6m_at δc P hcap (p := (1, 1, 1)) hp, hπ1, hpolar]

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.m3_first_hcancel_table_of_voa
#print axioms HaagerupIzumi.C8.Theta.m3_first_obstruction_of_voa
#print axioms HaagerupIzumi.C8.Theta.m6_first_hcancel_table_of_voa
#print axioms HaagerupIzumi.C8.Theta.m6_first_obstruction_of_voa
#print axioms HaagerupIzumi.C8.Theta.m3_reverse_hcancel_table_of_voa
#print axioms HaagerupIzumi.C8.Theta.m3_reverse_obstruction_of_voa
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_hcancel_table_of_voa
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_obstruction_of_voa
