module

public import HaagerupIzumi.C8.Theta.Basic

@[expose] public section

/-!
# Table 1: `m = 3`, first orientation, `L = L₇ ⊕ A₂`

Kernel-checked coefficient table of lines 3645–3667 of
`c8_expanded_20260929/haagerup_c8_expanded.tex` (proof of Proposition
`prop:near-group-current-obstructions`) and the pole-matching arithmetic of
lines 3668–3680, giving `dim U₁ = 15 + A + 10B`.

Conventions fixed here: coordinates in the basis `u, v` of `L₇` (Gram
`[[2,1],[1,4]]`) and the simple roots `α₁, α₂` of `A₂`; `q`-exponent
`(x,x)/2`; the coset `(r, s)` is `r·(2w/7) + s·ω + L` with `w = v - u/2` and
`ω = (2α₁ + α₂)/3` (`cosetL7A2`), which is forced up to sign by the twist
exponents `r²/7 + s²/3` (`energy_cosetPt_L7A2`, `m3First_dual_generated`);
`a = p²`, `b = 7t²/4` for `x_{L₇} = p u + t w`, `c = (y,y)/2` on `A₂`.

External hypotheses (only in `m3_first_obstruction`): `hcancel`, the output of
Lemma `lem:pole-cancellation` (`η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}` coefficientwise),
and the character values `-B`, `7 - A`, `2(dim U₁ - 22)` of `η⁸ δv` printed in
the proof.  Everything else is proved; shells are identified by kernel
evaluation (`decide +kernel`).
-/

namespace HaagerupIzumi.C8
namespace Theta

/-! ## `m = 3`, first orientation: `L = L₇ ⊕ A₂` (lines 3645–3680) -/

/-- `u` in the basis `u, v, α₁, α₂`. -/
def uL7 : Fin 4 → ℚ := ![1, 0, 0, 0]

/-- `w = v - u/2`. -/
def wL7 : Fin 4 → ℚ := ![-1/2, 1, 0, 0]

/-- The fundamental weight `ω = (2α₁ + α₂)/3` of `A₂`. -/
def omegaA2 : Fin 4 → ℚ := ![0, 0, 2/3, 1/3]

/-- The coset `(r, s)`: representative `r · (2w/7) + s · ω`. -/
def cosetL7A2 (r s : ℤ) : Fin 4 → ℚ :=
  ![-(r : ℚ) / 7, 2 * (r : ℚ) / 7, 2 * (s : ℚ) / 3, (s : ℚ) / 3]

/-- `a = p²`, where `x_{L₇} = p u + t w`; since `x_{L₇} = x₀ u + x₁ v`, `p = x₀ + x₁/2`. -/
def aL7 (x : Fin 4 → ℚ) : ℚ := (x 0 + x 1 / 2) ^ 2

/-- `b = 7t²/4`, `t = x₁`. -/
def bL7 (x : Fin 4 → ℚ) : ℚ := 7 * x 1 ^ 2 / 4

/-- `c = (y, y)/2` on the `A₂` factor. -/
def cA2 (x : Fin 4 → ℚ) : ℚ := x 2 ^ 2 - x 2 * x 3 + x 3 ^ 2

/-- `H₁ = a - b`. -/
def H1 (x : Fin 4 → ℚ) : ℚ := aL7 x - bL7 x

/-- `H₂ = a + b - c`. -/
def H2 (x : Fin 4 → ℚ) : ℚ := aL7 x + bL7 x - cA2 x

/-- `x_{L₇} = p u + t w` with `p = x₀ + x₁/2`, `t = x₁`. -/
theorem L7_decomposition (x : Fin 4 → ℚ) :
    x 0 = (x 0 + x 1 / 2) * uL7 0 + x 1 * wL7 0 ∧
      x 1 = (x 0 + x 1 / 2) * uL7 1 + x 1 * wL7 1 := by
  refine ⟨?_, ?_⟩ <;> simp [uL7, wL7] <;> ring1

/-- The energy is `a + b + c`. -/
theorem energy_L7A2_eq (x : Fin 4 → ℚ) : energy gramL7A2 x = aL7 x + bL7 x + cA2 x := by
  rw [energy, gramNorm_L7A2]
  unfold aL7 bL7 cA2
  ring

/-- Discriminant data: `u ⊥ w`, `(u,u) = 2`, `(w,w) = 7/2`; the representative of
`(1,0)` is `2w/7`, lies in `L*` (pairings `(0,1,0,0)` with the basis), has
energy `1/7`, and `7 · (2w/7) = 2w ∈ L`; `ω ∈ L*` (pairings `(0,0,1,0)`) has
energy `1/3`, and `3ω ∈ L`. -/
theorem m3First_discriminant :
    gramBil gramL7A2 uL7 wL7 = 0 ∧ gramNorm gramL7A2 uL7 = 2 ∧
    gramNorm gramL7A2 wL7 = 7 / 2 ∧
    cosetL7A2 1 0 = (fun i => 2 / 7 * wL7 i) ∧
    (fun i => gramBil gramL7A2 (cosetL7A2 1 0) (basisVec i)) = ![0, 1, 0, 0] ∧
    energy gramL7A2 (cosetL7A2 1 0) = 1 / 7 ∧
    (fun i => 7 * cosetL7A2 1 0 i) = ![-1, 2, 0, 0] ∧
    cosetL7A2 0 1 = omegaA2 ∧
    (fun i => gramBil gramL7A2 omegaA2 (basisVec i)) = ![0, 0, 1, 0] ∧
    energy gramL7A2 omegaA2 = 1 / 3 ∧
    (fun i => 3 * omegaA2 i) = ![0, 0, 2, 1] := by
  decide +kernel

/-- The inverse Gram matrix of `L₇ ⊕ A₂`; its columns span `L*`. -/
def invL7A2 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4/7, -1/7, 0, 0; -1/7, 2/7, 0, 0; 0, 0, 2/3, 1/3; 0, 0, 1/3, 2/3]

/-- `L* = G⁻¹ ℤ⁴ = ℤ (2w/7) + ℤ ω + L`: each column of `G⁻¹` is an integral
combination of `2w/7`, `ω` modulo `ℤ⁴`.  Hence `L*/L ≅ ℤ/7 × ℤ/3` with generators
`2w/7` (order `7`) and `ω` (order `3`). -/
theorem m3First_dual_generated :
    (∀ i j : Fin 4, ∑ k : Fin 4, (gramL7A2 i k : ℚ) * invL7A2 k j = if i = j then 1 else 0) ∧
    (fun i => invL7A2 i 0 + 4 * cosetL7A2 1 0 i) = ![0, 1, 0, 0] ∧
    (fun i => invL7A2 i 1 - cosetL7A2 1 0 i) = ![0, 0, 0, 0] ∧
    (fun i => invL7A2 i 2 - omegaA2 i) = ![0, 0, 0, 0] ∧
    (fun i => invL7A2 i 3 + omegaA2 i) = ![0, 0, 1, 1] := by
  decide +kernel

/-- Which coset is which: every vector of the coset `(r, s)` has energy
`r²/7 + s²/3` modulo `1` (the discriminant form `ℤ₇(r²/7) ⊕ ℤ₃(s²/3)`). -/
theorem energy_cosetPt_L7A2 (r s : ℤ) (n : Fin 4 → ℤ) :
    energy gramL7A2 (cosetPt (cosetL7A2 r s) n) =
      (r : ℚ) ^ 2 / 7 + (s : ℚ) ^ 2 / 3 +
        ((r * n 1 + s * n 2 + n 0 ^ 2 + n 0 * n 1 + 2 * n 1 ^ 2 + n 2 ^ 2 - n 2 * n 3
          + n 3 ^ 2 : ℤ) : ℚ) := by
  rw [energy, gramNorm_L7A2]
  first
  | (simp [cosetPt, cosetL7A2] <;> ring1)
  | (norm_num [cosetPt, cosetL7A2] <;> ring1)

/-- The shell `(1,0)`, energy `1/7`: only `2w/7`. -/
def shL7A2_10 : List (Fin 4 → ℤ) := [![0, 0, 0, 0]]

/-- The shell `(3,0)`, energy `2/7`: two vectors. -/
def shL7A2_30 : List (Fin 4 → ℤ) := [![0, -1, 0, 0], ![1, -1, 0, 0]]

/-- The shell `(0,0)`, energy `1`: two `L₇` roots `±u`, then six `A₂` roots. -/
def shL7A2_00 : List (Fin 4 → ℤ) :=
  [![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, -1, 0], ![0, 0, 0, 1],
    ![0, 0, 0, -1], ![0, 0, 1, 1], ![0, 0, -1, -1]]

theorem shell_L7A2_10 : shell gramL7A2 (cosetL7A2 1 0) (1 / 7) = {n | n ∈ shL7A2_10} :=
  shell_eq_of_box coord_L7A2 ![0, 0, 0, 0] ![0, 0, 0, 0] (by decide +kernel) shL7A2_10
    (by decide +kernel) (by decide +kernel)

theorem shell_L7A2_30 : shell gramL7A2 (cosetL7A2 3 0) (2 / 7) = {n | n ∈ shL7A2_30} :=
  shell_eq_of_box coord_L7A2 ![0, -1, 0, 0] ![1, -1, 0, 0] (by decide +kernel) shL7A2_30
    (by decide +kernel) (by decide +kernel)

theorem shell_L7A2_00 : shell gramL7A2 (cosetL7A2 0 0) 1 = {n | n ∈ shL7A2_00} :=
  shell_eq_of_box coord_L7A2 ![-1, 0, -1, -1] ![1, 0, 1, 1] (by decide +kernel) shL7A2_00
    (by decide +kernel) (by decide +kernel)

/-- Provenance (line 3668): the first row comes from `2w/7`; the second from two
vectors with `a = 1/4`, `b = 1/28` (and `c = 0`); the last from the two `L₇`
roots (`a = 1`, `b = c = 0`) and six `A₂` roots (`c = 1`, `a = b = 0`). -/
theorem m3First_provenance :
    (shL7A2_10.map (cosetPt (cosetL7A2 1 0))) = [fun i => 2 / 7 * wL7 i] ∧
    (∀ n ∈ shL7A2_30, aL7 (cosetPt (cosetL7A2 3 0) n) = 1 / 4 ∧
      bL7 (cosetPt (cosetL7A2 3 0) n) = 1 / 28 ∧ cA2 (cosetPt (cosetL7A2 3 0) n) = 0) ∧
    shL7A2_30.length = 2 ∧ shL7A2_00.length = 8 ∧
    (∀ n ∈ shL7A2_00.take 2, aL7 (cosetPt (cosetL7A2 0 0) n) = 1 ∧
      bL7 (cosetPt (cosetL7A2 0 0) n) = 0 ∧ cA2 (cosetPt (cosetL7A2 0 0) n) = 0) ∧
    (∀ n ∈ shL7A2_00.drop 2, aL7 (cosetPt (cosetL7A2 0 0) n) = 0 ∧
      bL7 (cosetPt (cosetL7A2 0 0) n) = 0 ∧ cA2 (cosetPt (cosetL7A2 0 0) n) = 1) := by
  decide +kernel

theorem m3First_H1_10 : thetaCoeff gramL7A2 (cosetL7A2 1 0) H1 (1 / 7) = -1 / 7 := by
  rw [thetaCoeff_eq_list_sum shell_L7A2_10 (by decide +kernel)]
  decide +kernel

theorem m3First_H2_10 : thetaCoeff gramL7A2 (cosetL7A2 1 0) H2 (1 / 7) = 1 / 7 := by
  rw [thetaCoeff_eq_list_sum shell_L7A2_10 (by decide +kernel)]
  decide +kernel

theorem m3First_H1_30 : thetaCoeff gramL7A2 (cosetL7A2 3 0) H1 (2 / 7) = 3 / 7 := by
  rw [thetaCoeff_eq_list_sum shell_L7A2_30 (by decide +kernel)]
  decide +kernel

theorem m3First_H2_30 : thetaCoeff gramL7A2 (cosetL7A2 3 0) H2 (2 / 7) = 4 / 7 := by
  rw [thetaCoeff_eq_list_sum shell_L7A2_30 (by decide +kernel)]
  decide +kernel

theorem m3First_H1_00 : thetaCoeff gramL7A2 (cosetL7A2 0 0) H1 1 = 2 := by
  rw [thetaCoeff_eq_list_sum shell_L7A2_00 (by decide +kernel)]
  decide +kernel

theorem m3First_H2_00 : thetaCoeff gramL7A2 (cosetL7A2 0 0) H2 1 = -4 := by
  rw [thetaCoeff_eq_list_sum shell_L7A2_00 (by decide +kernel)]
  decide +kernel

/-- **Table 1** (lines 3661–3667), all six entries. -/
theorem m3First_table :
    thetaCoeff gramL7A2 (cosetL7A2 1 0) H1 (1 / 7) = -1 / 7 ∧
    thetaCoeff gramL7A2 (cosetL7A2 1 0) H2 (1 / 7) = 1 / 7 ∧
    thetaCoeff gramL7A2 (cosetL7A2 3 0) H1 (2 / 7) = 3 / 7 ∧
    thetaCoeff gramL7A2 (cosetL7A2 3 0) H2 (2 / 7) = 4 / 7 ∧
    thetaCoeff gramL7A2 (cosetL7A2 0 0) H1 1 = 2 ∧
    thetaCoeff gramL7A2 (cosetL7A2 0 0) H2 1 = -4 :=
  ⟨m3First_H1_10, m3First_H2_10, m3First_H1_30, m3First_H2_30, m3First_H1_00, m3First_H2_00⟩

/-- **`m = 3`, first orientation** (lines 3673–3680).  `δc r s e` is the coefficient
of `q^e` in the coordinate `(r, s)` of `η⁸ δv`, the difference from the affine
reference (`22` currents, `A = 7`, `B = 0`).

External hypotheses: `hcancel` is the conclusion of pole cancellation
(Lemma `lem:pole-cancellation`) for `η⁸ δv - λ Θ_{H₁} - μ Θ_{H₂}`; `hpolarB`,
`hpolarA` are the polar coefficients `-B - (-0)` at `(1,0), q^{1/7}` and
`-A - (-7)` at `(3,0), q^{2/7}`; `hvac` is `δv₀ = 2 δχ_U` at `q¹`.
Conclusion: `λ = 7 - A + 4B`, `μ = 7 - A - 3B`, `dim U₁ = 15 + A + 10B`. -/
theorem m3_first_obstruction (δc : ℤ → ℤ → ℚ → ℚ) (A B d : ℕ) (lam mu : ℚ)
    (hcancel : ∀ r s e, δc r s e = lam * thetaCoeff gramL7A2 (cosetL7A2 r s) H1 e
        + mu * thetaCoeff gramL7A2 (cosetL7A2 r s) H2 e)
    (hpolarB : δc 1 0 (1 / 7) = -(B : ℚ) - 0)
    (hpolarA : δc 3 0 (2 / 7) = -(A : ℚ) - (-7))
    (hvac : δc 0 0 1 = 2 * ((d : ℚ) - 22)) :
    lam = 7 - A + 4 * B ∧ mu = 7 - A - 3 * B ∧ d = 15 + A + 10 * B := by
  rw [hcancel, m3First_H1_10, m3First_H2_10] at hpolarB
  rw [hcancel, m3First_H1_30, m3First_H2_30] at hpolarA
  rw [hcancel, m3First_H1_00, m3First_H2_00] at hvac
  have hl : lam = 7 - A + 4 * B := by linarith
  have hm : mu = 7 - A - 3 * B := by linarith
  refine ⟨hl, hm, ?_⟩
  have hd : (d : ℚ) = 15 + A + 10 * B := by linarith
  exact_mod_cast hd

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.m3First_table
#print axioms HaagerupIzumi.C8.Theta.m3_first_obstruction
#print axioms HaagerupIzumi.C8.Theta.m3First_discriminant
#print axioms HaagerupIzumi.C8.Theta.m3First_dual_generated
#print axioms HaagerupIzumi.C8.Theta.m3First_provenance
#print axioms HaagerupIzumi.C8.Theta.energy_cosetPt_L7A2
