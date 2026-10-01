module

public import HaagerupIzumi.C8.Theta.Basic

@[expose] public section

/-!
# Table 3: `m = 6`, first orientation, `L = A₁ ⊕ A₁ ⊕ A₂`

Kernel-checked coefficients of lines 3714–3730 of
`c8_expanded_20260929/haagerup_c8_expanded.tex` and the arithmetic of lines
3731–3740, giving `dim U₁ = 8 + A`.

Conventions fixed here: the coset `(εε', s)` is `(ε α/2, ε' α'/2, s ω) + L`
(`cosetA1A1A2`); the restriction by the interchange of the two `A₁` factors and
the conjugation of the `A₂` charge is the *average* over that group
(`symA1A1A2`).

External hypotheses (only in `m6_first_obstruction`): `hcancel` (pole
cancellation, `η⁸ δv = κ Θ_H`) and the character values `-A/2 + 8/2`,
`2(dim U₁ - 16)`.
-/

namespace HaagerupIzumi.C8
namespace Theta

/-! ## `m = 6`, first orientation: `L = A₁ ⊕ A₁ ⊕ A₂` (lines 3714–3740) -/

/-- The coset `(εε', s)`: representative `(ε α/2, ε' α'/2, s ω)`. -/
def cosetA1A1A2 (a b s : ℤ) : Fin 4 → ℚ :=
  ![(a : ℚ) / 2, (b : ℚ) / 2, 2 * (s : ℚ) / 3, (s : ℚ) / 3]

/-- `H = ‖x_{A₁²}‖²/2 - ‖y_{A₂}‖²/2`. -/
def HA1A1A2 (x : Fin 4 → ℚ) : ℚ :=
  (2 * x 0 ^ 2 + 2 * x 1 ^ 2) / 2 - (2 * x 2 ^ 2 - 2 * x 2 * x 3 + 2 * x 3 ^ 2) / 2

/-- The restriction by the interchange of the two `A₁` factors and the
conjugation of the `A₂` charge: the average over that group. -/
def symA1A1A2 (f : ℤ → ℤ → ℤ → ℚ) (a b s : ℤ) : ℚ :=
  (f a b s + f b a s + f a b (-s) + f b a (-s)) / 4

/-- Projected `[q^e] Θ_H` in the coordinate `(ab, s)`. -/
noncomputable def PThetaA1A1A2 (a b s : ℤ) (e : ℚ) : ℚ :=
  symA1A1A2 (fun a b s => thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) HA1A1A2 e) a b s

/-- `α/2 ∈ A₁*` (pairings `(1,0,0,0)`) has energy `1/4` (twist `i`). -/
theorem m6First_discriminant :
    (fun i => gramBil gramA1A1A2 (cosetA1A1A2 1 0 0) (basisVec i)) = ![1, 0, 0, 0] ∧
    energy gramA1A1A2 (cosetA1A1A2 1 0 0) = 1 / 4 ∧
    energy gramA1A1A2 (cosetA1A1A2 1 1 0) = 1 / 2 := by
  decide +kernel

def shA_10 : List (Fin 4 → ℤ) := [![0, 0, 0, 0], ![-1, 0, 0, 0]]

def shA_01 : List (Fin 4 → ℤ) := [![0, 0, 0, 0], ![0, -1, 0, 0]]

/-- Four `A₁` roots, then six `A₂` roots. -/
def shA_vac : List (Fin 4 → ℤ) :=
  [![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0],
    ![0, 0, -1, 0], ![0, 0, 0, 1], ![0, 0, 0, -1], ![0, 0, 1, 1], ![0, 0, -1, -1]]

theorem shell_A_10 : shell gramA1A1A2 (cosetA1A1A2 1 0 0) (1 / 4) = {n | n ∈ shA_10} :=
  shell_eq_of_box coord_A1A1A2 ![-1, 0, 0, 0] ![0, 0, 0, 0] (by decide +kernel) shA_10
    (by decide +kernel) (by decide +kernel)

theorem shell_A_01 : shell gramA1A1A2 (cosetA1A1A2 0 1 0) (1 / 4) = {n | n ∈ shA_01} :=
  shell_eq_of_box coord_A1A1A2 ![0, -1, 0, 0] ![0, 0, 0, 0] (by decide +kernel) shA_01
    (by decide +kernel) (by decide +kernel)

theorem shell_A_vac : shell gramA1A1A2 (cosetA1A1A2 0 0 0) 1 = {n | n ∈ shA_vac} :=
  shell_eq_of_box coord_A1A1A2 ![-1, -1, -1, -1] ![1, 1, 1, 1] (by decide +kernel) shA_vac
    (by decide +kernel) (by decide +kernel)

/-- Provenance (lines 3729–3730): the two half-roots `±α/2`; four `A₁` roots
(`H = 1`) and six `A₂` roots (`H = -1`). -/
theorem m6First_provenance :
    (shA_10.map (cosetPt (cosetA1A1A2 1 0 0))) = [![1/2, 0, 0, 0], ![-1/2, 0, 0, 0]] ∧
    shA_vac.length = 10 ∧
    (∀ n ∈ shA_vac.take 4, HA1A1A2 (cosetPt (cosetA1A1A2 0 0 0) n) = 1 ∧ n 2 = 0 ∧ n 3 = 0) ∧
    (∀ n ∈ shA_vac.drop 4, HA1A1A2 (cosetPt (cosetA1A1A2 0 0 0) n) = -1 ∧ n 0 = 0 ∧ n 1 = 0) := by
  decide +kernel

theorem H_A_10 : thetaCoeff gramA1A1A2 (cosetA1A1A2 1 0 0) HA1A1A2 (1 / 4) = 1 / 2 := by
  rw [thetaCoeff_eq_list_sum shell_A_10 (by decide +kernel)]
  decide +kernel

theorem H_A_01 : thetaCoeff gramA1A1A2 (cosetA1A1A2 0 1 0) HA1A1A2 (1 / 4) = 1 / 2 := by
  rw [thetaCoeff_eq_list_sum shell_A_01 (by decide +kernel)]
  decide +kernel

theorem H_A_vac : thetaCoeff gramA1A1A2 (cosetA1A1A2 0 0 0) HA1A1A2 1 = -2 := by
  rw [thetaCoeff_eq_list_sum shell_A_vac (by decide +kernel)]
  decide +kernel

theorem m6First_H_polar : PThetaA1A1A2 1 0 0 (1 / 4) = 1 / 2 := by
  simp only [PThetaA1A1A2, symA1A1A2, neg_zero]
  rw [H_A_10, H_A_01]
  norm_num

theorem m6First_H_vac : PThetaA1A1A2 0 0 0 1 = -2 := by
  simp only [PThetaA1A1A2, symA1A1A2, neg_zero]
  rw [H_A_vac]
  norm_num

/-- **Table 3** (line 3727): `[q^{1/4}] Θ_{H,(10,0)} = 1/2`, `[q] Θ_{H,(00,0)} = -2`;
the unprojected values agree with the projected ones. -/
theorem m6First_table :
    PThetaA1A1A2 1 0 0 (1 / 4) = 1 / 2 ∧ PThetaA1A1A2 0 0 0 1 = -2 ∧
    thetaCoeff gramA1A1A2 (cosetA1A1A2 1 0 0) HA1A1A2 (1 / 4) = 1 / 2 ∧
    thetaCoeff gramA1A1A2 (cosetA1A1A2 0 0 0) HA1A1A2 1 = -2 :=
  ⟨m6First_H_polar, m6First_H_vac, H_A_10, H_A_vac⟩

/-- **`m = 6`, first orientation** (lines 3731–3740).  `δc a b s e` is the
coefficient of `q^e` in the projected coordinate `(ab, s)` of `η⁸ δv`, the
difference from the reference (`16` currents, `A = 8`).

External hypotheses: `hcancel` (pole cancellation: `η⁸ δv = κ Θ_H`);
`hpolar`: projected polar coefficient `-A/2 - (-8/2)`; `hvac`: `2(dim U₁ - 16)`.
Conclusion: `κ = 8 - A`, `dim U₁ = 8 + A`. -/
theorem m6_first_obstruction (δc : ℤ → ℤ → ℤ → ℚ → ℚ) (A d : ℕ) (κ : ℚ)
    (hcancel : ∀ a b s e, δc a b s e = κ * PThetaA1A1A2 a b s e)
    (hpolar : δc 1 0 0 (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2))
    (hvac : δc 0 0 0 1 = 2 * ((d : ℚ) - 16)) :
    κ = 8 - A ∧ d = 8 + A := by
  rw [hcancel, m6First_H_polar] at hpolar
  rw [hcancel, m6First_H_vac] at hvac
  have hκ : κ = 8 - A := by linarith
  refine ⟨hκ, ?_⟩
  have hd : (d : ℚ) = 8 + A := by linarith
  exact_mod_cast hd

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.m6First_table
#print axioms HaagerupIzumi.C8.Theta.m6_first_obstruction
#print axioms HaagerupIzumi.C8.Theta.m6First_discriminant
#print axioms HaagerupIzumi.C8.Theta.m6First_provenance
