module

public import HaagerupIzumi.C8.Theta.ThetaSupport

@[expose] public section

/-!
# The pole-matching coefficients `λ, μ` (`κ, φ`) as functions of `A, B` (`P`)

W6 plan item 1 (`Theta/W6_PLAN.md`, audit item 4), for the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).

In `Theta/M3First` … `M6Reverse` the coefficients `λ, μ, κ, φ` of the identity
`η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}` (resp. `φ F + κ Θ_H`) are free variables, solved from `hcancel`
and the polar data.  The manuscript proceeds in the other order: it *defines* them from the
polar top dimensions `A, B` (`P`) by pole matching, then applies `lem:pole-cancellation` to the
remainder.  Here:

* the coefficients as functions of the polar data (lines 3674, 3708, 3736, 3767):
  `lamM3First A B = 7 - A + 4B`, `muM3First A B = 7 - A - 3B`; `phiM3Reverse = 1`,
  `kappaM3Reverse A = (3 + 14A)/4`; `kappaM6First A = 8 - A`; `phiM6Reverse = 1`,
  `kappaM6Reverse P = P`;
* `*_polar_match`: with these coefficients the theta combination has, at the table's polar
  and vacuum entries, exactly the coefficients of `η⁸ δv` (resp. `η⁸ v`) stated in the
  manuscript: e.g. `-B - 0` at `((1,0), q^{1/7})` and `-A - (-7)` at `((3,0), q^{2/7})`;
  for `M3First` also the vacuum `q⁰` entry (`0`, since `H(0) = 0`; `thetaCoeff_at_zero`);
* `*_remainder_polar_zero`: hence, given the VOA polar data, the remainder
  `η⁸ δv - λ Θ_{H₁} - μ Θ_{H₂}` has zero coefficient at these entries (the input of pole
  cancellation at the table entries; that these are *all* polar entries is W6 plan item 3);
* `*_polar_unique`: these are the only coefficients with this property;
* `*_obstruction_of_defined`: the obstruction theorems with `hcancel` stated for the defined
  coefficients; the polar hypotheses are then consequences and only the vacuum coefficient
  is needed to obtain `dim U₁`.

No file outside this one is changed.  External hypotheses: `hcancel` (the conclusion of pole
cancellation) and the VOA-side vacuum/polar coefficients, exactly as in the table files.
-/

noncomputable section

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Vanishing at energy zero -/

/-- The only vector of energy `0` of a positive definite lattice is `0`. -/
theorem eq_zero_of_energy_eq_zero {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    {x : Fin 4 → ℚ} (hx : energy Gz x = 0) : x = 0 := by
  by_contra hne
  have hne' : ratVec x ≠ 0 := by
    intro h0
    apply hne
    funext i
    have h := congrFun h0 i
    simpa [ratVec] using h
  have hpos := hG.dotProduct_mulVec_pos hne'
  rw [star_trivial] at hpos
  have hq := qf_gramR_ratVec_eq_energy Gz x
  rw [hx, qf, Rat.cast_zero, mul_zero] at hq
  linarith

/-- `[q⁰] Θ_{H, g+L} = 0` whenever `H(0) = 0` (e.g. `H = quadOf M`). -/
theorem thetaCoeff_at_zero {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (g : Fin 4 → ℚ) {H : (Fin 4 → ℚ) → ℚ} (hH : H 0 = 0) : thetaCoeff Gz g H 0 = 0 := by
  unfold thetaCoeff
  refine finsum_mem_eq_zero_of_forall_eq_zero fun n hn => ?_
  rw [eq_zero_of_energy_eq_zero hG (show energy Gz (cosetPt g n) = 0 from hn), hH]

theorem H1_zero : H1 0 = 0 := by norm_num [H1, aL7, bL7]

theorem H2_zero : H2 0 = 0 := by norm_num [H2, aL7, bL7, cA2]

theorem HA1A1A2_zero : HA1A1A2 0 = 0 := by norm_num [HA1A1A2]

/-! ## `m = 3`, first orientation (`L₇ ⊕ A₂`, line 3674) -/

/-- `λ = 7 - A + 4B`. -/
def lamM3First (A B : ℕ) : ℚ := 7 - A + 4 * B

/-- `μ = 7 - A - 3B`. -/
def muM3First (A B : ℕ) : ℚ := 7 - A - 3 * B

/-- **Pole matching, `m = 3` first orientation.**  With `λ = 7 - A + 4B`, `μ = 7 - A - 3B`,
the combination `λ Θ_{H₁} + μ Θ_{H₂}` has the coefficients `0` at the vacuum `q⁰`,
`-B - 0` at `((1,0), q^{1/7})` and `-A - (-7)` at `((3,0), q^{2/7})`, i.e. those of `η⁸ δv`
(polar tops `B`, `A`, reference `A = 7`, `B = 0`). -/
theorem m3First_polar_match (A B : ℕ) :
    lamM3First A B * thetaCoeff gramL7A2 (cosetL7A2 0 0) H1 0 +
        muM3First A B * thetaCoeff gramL7A2 (cosetL7A2 0 0) H2 0 = 0 ∧
    lamM3First A B * thetaCoeff gramL7A2 (cosetL7A2 1 0) H1 (1 / 7) +
        muM3First A B * thetaCoeff gramL7A2 (cosetL7A2 1 0) H2 (1 / 7) = -(B : ℚ) - 0 ∧
    lamM3First A B * thetaCoeff gramL7A2 (cosetL7A2 3 0) H1 (2 / 7) +
        muM3First A B * thetaCoeff gramL7A2 (cosetL7A2 3 0) H2 (2 / 7) = -(A : ℚ) - (-7) := by
  rw [thetaCoeff_at_zero posDef_L7A2 _ H1_zero, thetaCoeff_at_zero posDef_L7A2 _ H2_zero,
    m3First_H1_10, m3First_H2_10, m3First_H1_30, m3First_H2_30]
  unfold lamM3First muM3First
  refine ⟨by ring, by ring, by ring⟩

/-- The remainder `η⁸ δv - λ Θ_{H₁} - μ Θ_{H₂}` has zero coefficient at the vacuum `q⁰` and
the two polar entries, given the VOA-side values there. -/
theorem m3First_remainder_polar_zero (δc : ℤ → ℤ → ℚ → ℚ) (A B : ℕ)
    (hvac0 : δc 0 0 0 = 0) (hpolarB : δc 1 0 (1 / 7) = -(B : ℚ) - 0)
    (hpolarA : δc 3 0 (2 / 7) = -(A : ℚ) - (-7)) :
    ∀ rse ∈ ({(0, 0, 0), (1, 0, 1 / 7), (3, 0, 2 / 7)} : Set (ℤ × ℤ × ℚ)),
      δc rse.1 rse.2.1 rse.2.2 -
        (lamM3First A B * thetaCoeff gramL7A2 (cosetL7A2 rse.1 rse.2.1) H1 rse.2.2 +
          muM3First A B * thetaCoeff gramL7A2 (cosetL7A2 rse.1 rse.2.1) H2 rse.2.2) = 0 := by
  obtain ⟨h0, hB, hA⟩ := m3First_polar_match A B
  rintro ⟨r, s, e⟩ hrse
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hrse
  rcases hrse with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [hvac0, h0, sub_self]
  · rw [hpolarB, hB, sub_self]
  · rw [hpolarA, hA, sub_self]

/-- Uniqueness: the polar entries determine `λ, μ`. -/
theorem m3First_polar_unique (A B : ℕ) (lam mu : ℚ)
    (hB : lam * thetaCoeff gramL7A2 (cosetL7A2 1 0) H1 (1 / 7) +
      mu * thetaCoeff gramL7A2 (cosetL7A2 1 0) H2 (1 / 7) = -(B : ℚ) - 0)
    (hA : lam * thetaCoeff gramL7A2 (cosetL7A2 3 0) H1 (2 / 7) +
      mu * thetaCoeff gramL7A2 (cosetL7A2 3 0) H2 (2 / 7) = -(A : ℚ) - (-7)) :
    lam = lamM3First A B ∧ mu = muM3First A B := by
  rw [m3First_H1_10, m3First_H2_10] at hB
  rw [m3First_H1_30, m3First_H2_30] at hA
  unfold lamM3First muM3First
  constructor <;> linarith

/-- **`m = 3`, first orientation, with the manuscript's coefficients.**  If pole cancellation
gives `η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}` with `λ, μ` *defined* from `A, B`, then the polar
coefficients of `η⁸ δv` are `-B`, `7 - A` and the vacuum coefficient gives
`dim U₁ = 15 + A + 10B`. -/
theorem m3_first_obstruction_of_defined (δc : ℤ → ℤ → ℚ → ℚ) (A B d : ℕ)
    (hcancel : ∀ r s e, δc r s e = lamM3First A B * thetaCoeff gramL7A2 (cosetL7A2 r s) H1 e
        + muM3First A B * thetaCoeff gramL7A2 (cosetL7A2 r s) H2 e)
    (hvac : δc 0 0 1 = 2 * ((d : ℚ) - 22)) :
    δc 1 0 (1 / 7) = -(B : ℚ) - 0 ∧ δc 3 0 (2 / 7) = -(A : ℚ) - (-7) ∧
      d = 15 + A + 10 * B := by
  obtain ⟨-, hB, hA⟩ := m3First_polar_match A B
  have hpB := (hcancel 1 0 (1 / 7)).trans hB
  have hpA := (hcancel 3 0 (2 / 7)).trans hA
  exact ⟨hpB, hpA, (m3_first_obstruction δc A B d _ _ hcancel hpB hpA hvac).2.2⟩

/-! ## `m = 3`, reverse orientation (`G₇⁻`, line 3708) -/

/-- `φ = 1`. -/
def phiM3Reverse : ℚ := 1

/-- `κ = (3 + 14A)/4`. -/
def kappaM3Reverse (A : ℕ) : ℚ := (3 + 14 * A) / 4

/-- **Pole matching, `m = 3` reverse orientation.**  `φ F + κ Θ_H` has vacuum coefficient `1`
at `q⁰` and polar coefficient `-A` at `((2,1), q^{2/21})`. -/
theorem m3Reverse_polar_match (A : ℕ) :
    phiM3Reverse * PFG7m 0 0 0 + kappaM3Reverse A * PThetaG7m 0 0 0 = 1 ∧
    phiM3Reverse * PFG7m 2 1 (2 / 21) + kappaM3Reverse A * PThetaG7m 2 1 (2 / 21) =
      -(A : ℚ) := by
  rw [m3Reverse_F_vac0, m3Reverse_H_vac0, m3Reverse_F_polar, m3Reverse_H_polar]
  unfold phiM3Reverse kappaM3Reverse
  refine ⟨by ring, by ring⟩

theorem m3Reverse_remainder_polar_zero (c : ℤ → ℤ → ℚ → ℚ) (A : ℕ) (hvac0 : c 0 0 0 = 1)
    (hpolar : c 2 1 (2 / 21) = -(A : ℚ)) :
    c 0 0 0 - (phiM3Reverse * PFG7m 0 0 0 + kappaM3Reverse A * PThetaG7m 0 0 0) = 0 ∧
    c 2 1 (2 / 21) -
      (phiM3Reverse * PFG7m 2 1 (2 / 21) + kappaM3Reverse A * PThetaG7m 2 1 (2 / 21)) = 0 := by
  obtain ⟨h0, h1⟩ := m3Reverse_polar_match A
  rw [hvac0, h0, hpolar, h1]
  exact ⟨sub_self _, sub_self _⟩

theorem m3Reverse_polar_unique (A : ℕ) (φ κ : ℚ)
    (h0 : φ * PFG7m 0 0 0 + κ * PThetaG7m 0 0 0 = 1)
    (h1 : φ * PFG7m 2 1 (2 / 21) + κ * PThetaG7m 2 1 (2 / 21) = -(A : ℚ)) :
    φ = phiM3Reverse ∧ κ = kappaM3Reverse A := by
  rw [m3Reverse_F_vac0, m3Reverse_H_vac0] at h0
  rw [m3Reverse_F_polar, m3Reverse_H_polar] at h1
  unfold phiM3Reverse kappaM3Reverse
  constructor <;> linarith

theorem m3_reverse_obstruction_of_defined (c : ℤ → ℤ → ℚ → ℚ) (A d : ℕ)
    (hcancel : ∀ r s e, c r s e = phiM3Reverse * PFG7m r s e + kappaM3Reverse A * PThetaG7m r s e)
    (hvac1 : c 0 0 1 = 2 * (d : ℚ) - 94) :
    c 0 0 0 = 1 ∧ c 2 1 (2 / 21) = -(A : ℚ) ∧ d = 14 + 42 * A := by
  obtain ⟨h0, h1⟩ := m3Reverse_polar_match A
  have hv0 := (hcancel 0 0 0).trans h0
  have hp := (hcancel 2 1 (2 / 21)).trans h1
  exact ⟨hv0, hp, (m3_reverse_obstruction c A d _ _ hcancel hv0 hvac1 hp).2.2⟩

/-! ## `m = 6`, first orientation (`A₁ ⊕ A₁ ⊕ A₂`, line 3737) -/

/-- `κ = 8 - A`. -/
def kappaM6First (A : ℕ) : ℚ := 8 - A

/-- **Pole matching, `m = 6` first orientation.**  `κ Θ_H` has coefficient `0` at the vacuum
`q⁰` and the projected polar coefficient `-A/2 - (-8/2)` at `((10,0), q^{1/4})`. -/
theorem m6First_polar_match (A : ℕ) :
    kappaM6First A * PThetaA1A1A2 0 0 0 0 = 0 ∧
    kappaM6First A * PThetaA1A1A2 1 0 0 (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2) := by
  have h := thetaCoeff_at_zero posDef_A1A1A2 (cosetA1A1A2 0 0 0) HA1A1A2_zero
  rw [m6First_H_polar]
  simp only [PThetaA1A1A2, symA1A1A2, neg_zero, h]
  unfold kappaM6First
  refine ⟨by ring, by ring⟩

theorem m6First_remainder_polar_zero (δc : ℤ → ℤ → ℤ → ℚ → ℚ) (A : ℕ)
    (hvac0 : δc 0 0 0 0 = 0) (hpolar : δc 1 0 0 (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2)) :
    δc 0 0 0 0 - kappaM6First A * PThetaA1A1A2 0 0 0 0 = 0 ∧
    δc 1 0 0 (1 / 4) - kappaM6First A * PThetaA1A1A2 1 0 0 (1 / 4) = 0 := by
  obtain ⟨h0, h1⟩ := m6First_polar_match A
  rw [hvac0, h0, hpolar, h1]
  exact ⟨sub_self _, sub_self _⟩

theorem m6First_polar_unique (A : ℕ) (κ : ℚ)
    (h : κ * PThetaA1A1A2 1 0 0 (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2)) :
    κ = kappaM6First A := by
  rw [m6First_H_polar] at h
  unfold kappaM6First
  linarith

theorem m6_first_obstruction_of_defined (δc : ℤ → ℤ → ℤ → ℚ → ℚ) (A d : ℕ)
    (hcancel : ∀ a b s e, δc a b s e = kappaM6First A * PThetaA1A1A2 a b s e)
    (hvac : δc 0 0 0 1 = 2 * ((d : ℚ) - 16)) :
    δc 1 0 0 (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2) ∧ d = 8 + A := by
  obtain ⟨-, h1⟩ := m6First_polar_match A
  have hp := (hcancel 1 0 0 (1 / 4)).trans h1
  exact ⟨hp, (m6_first_obstruction δc A d _ hcancel hp hvac).2⟩

/-! ## `m = 6`, reverse orientation (`G₆⁻`, line 3769) -/

/-- `φ = 1`. -/
def phiM6Reverse : ℚ := 1

/-- `κ = P`. -/
def kappaM6Reverse (P : ℕ) : ℚ := P

/-- **Pole matching, `m = 6` reverse orientation.**  `φ F + κ Θ_H` has vacuum coefficient `1`
at `q⁰` and polar coefficient `-P` at `(-w/3, q^{1/6})`. -/
theorem m6Reverse_polar_match (P : ℕ) :
    phiM6Reverse * PFG6m 0 0 + kappaM6Reverse P * PThetaG6m 0 0 = 1 ∧
    phiM6Reverse * PFG6m polarG6m (1 / 6) + kappaM6Reverse P * PThetaG6m polarG6m (1 / 6) =
      -(P : ℚ) := by
  rw [m6Reverse_F_vac0, m6Reverse_H_vac0, m6Reverse_F_polar, m6Reverse_H_polar]
  unfold phiM6Reverse kappaM6Reverse
  refine ⟨by ring, by ring⟩

theorem m6Reverse_remainder_polar_zero (c : (Fin 4 → ℚ) → ℚ → ℚ) (P : ℕ) (hvac0 : c 0 0 = 1)
    (hpolar : c polarG6m (1 / 6) = -(P : ℚ)) :
    c 0 0 - (phiM6Reverse * PFG6m 0 0 + kappaM6Reverse P * PThetaG6m 0 0) = 0 ∧
    c polarG6m (1 / 6) -
      (phiM6Reverse * PFG6m polarG6m (1 / 6) + kappaM6Reverse P * PThetaG6m polarG6m (1 / 6)) =
        0 := by
  obtain ⟨h0, h1⟩ := m6Reverse_polar_match P
  rw [hvac0, h0, hpolar, h1]
  exact ⟨sub_self _, sub_self _⟩

theorem m6Reverse_polar_unique (P : ℕ) (φ κ : ℚ)
    (h0 : φ * PFG6m 0 0 + κ * PThetaG6m 0 0 = 1)
    (h1 : φ * PFG6m polarG6m (1 / 6) + κ * PThetaG6m polarG6m (1 / 6) = -(P : ℚ)) :
    φ = phiM6Reverse ∧ κ = kappaM6Reverse P := by
  rw [m6Reverse_F_vac0, m6Reverse_H_vac0] at h0
  rw [m6Reverse_F_polar, m6Reverse_H_polar] at h1
  unfold phiM6Reverse kappaM6Reverse
  constructor <;> linarith

theorem m6_reverse_obstruction_of_defined (c : (Fin 4 → ℚ) → ℚ → ℚ) (P d : ℕ)
    (hcancel : ∀ g e, c g e = phiM6Reverse * PFG6m g e + kappaM6Reverse P * PThetaG6m g e)
    (hvac1 : c 0 1 = 2 * (d : ℚ) - 94) :
    c 0 0 = 1 ∧ c polarG6m (1 / 6) = -(P : ℚ) ∧ d = 5 + 12 * P := by
  obtain ⟨h0, h1⟩ := m6Reverse_polar_match P
  have hv0 := (hcancel 0 0).trans h0
  have hp := (hcancel polarG6m (1 / 6)).trans h1
  exact ⟨hv0, hp, (m6_reverse_obstruction c P d _ _ hcancel hv0 hvac1 hp).2.2⟩

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_at_zero
#print axioms HaagerupIzumi.C8.Theta.m3First_polar_match
#print axioms HaagerupIzumi.C8.Theta.m3First_remainder_polar_zero
#print axioms HaagerupIzumi.C8.Theta.m3First_polar_unique
#print axioms HaagerupIzumi.C8.Theta.m3_first_obstruction_of_defined
#print axioms HaagerupIzumi.C8.Theta.m3Reverse_polar_match
#print axioms HaagerupIzumi.C8.Theta.m3Reverse_polar_unique
#print axioms HaagerupIzumi.C8.Theta.m3_reverse_obstruction_of_defined
#print axioms HaagerupIzumi.C8.Theta.m6First_polar_match
#print axioms HaagerupIzumi.C8.Theta.m6First_polar_unique
#print axioms HaagerupIzumi.C8.Theta.m6_first_obstruction_of_defined
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_polar_match
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_polar_unique
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_obstruction_of_defined
