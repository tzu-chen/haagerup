module

public import HaagerupIzumi.C8.Fusion.Rank6
public import HaagerupIzumi.C8.Fusion.FusionAlgebra

@[expose] public section

/-!
# `eq:rank6-ring` from `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)`, and the dimension equation

* `rank6_ring_of_fusionAlgebraIso` — `rank6_ring` with its two algebra hypotheses
  (at most two characters, noncommutativity) replaced by the single external input
  `FusionAlgebraIso R` (`K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)`, line 3799 of
  `c8_expanded_20260929/haagerup_c8_expanded.tex`).
* `IsHIRing.char_rho_sq` — on the ring `eq:rank6-ring`, every real character with
  `χ(a) = 1` (e.g. the Frobenius–Perron dimension) satisfies
  `χ(ρ)² = 3m χ(ρ) + 1`; this is the equation `d² = 3md + 1` used in
  `rank6_center_count` (line 3831).
-/

namespace HaagerupIzumi.C8.Fusion

open BasedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **eq:rank6-ring** from the explicit algebra identification
`K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (external input `Ψ`), exactly three invertibles
`1, a, a² = a*`, and a positive Frobenius–Perron character `d`. -/
theorem rank6_ring_of_fusionAlgebraIso (R : BasedRing ι) (hcard : Fintype.card ι = 6) {a : ι}
    (ha : R.IsInvertible a) (ha1 : a ≠ R.unit)
    (haa : ∀ l, R.N a a l = if l = R.dual a then 1 else 0)
    (hinv : ∀ x, R.IsInvertible x → x = R.unit ∨ x = a ∨ x = R.dual a)
    (d : ι → ℝ) (hFP : R.IsCharacter d) (hFPpos : ∀ i, 0 < d i)
    (Ψ : FusionAlgebraIso R) :
    ∃ ρ ρ₁ ρ₂ m, IsHIRing R a ρ ρ₁ ρ₂ m :=
  rank6_ring R hcard ha ha1 haa hinv d hFP hFPpos Ψ.atMostTwoChars Ψ.noncomm

/-- On `eq:rank6-ring`, a character with `χ(a) = 1` satisfies `χ(ρ)² = 3m χ(ρ) + 1`. -/
theorem IsHIRing.char_rho_sq {R : BasedRing ι} {a ρ ρ₁ ρ₂ : ι} {m : ℕ}
    (H : IsHIRing R a ρ ρ₁ ρ₂ m) {χ : ι → ℝ} (hχ : R.IsCharacter χ) (ha : χ a = 1) :
    χ ρ ^ 2 = 3 * m * χ ρ + 1 := by
  have hρu : ρ ≠ R.unit := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have hρ₁u : ρ₁ ≠ R.unit := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have hρ₂u : ρ₂ ≠ R.unit := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have h01 : ρ ≠ ρ₁ := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have h02 : ρ ≠ ρ₂ := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have h12 : ρ₁ ≠ ρ₂ := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have hl1 : R.lmul a ρ = ρ₁ :=
    H.a_inv.lmul_eq (by rw [H.a_mul_ρ, if_pos rfl]; exact one_ne_zero)
  have hl2 : R.lmul (R.dual a) ρ = ρ₂ :=
    H.a_inv.dual.lmul_eq (by rw [H.a2_mul_ρ, if_pos rfl]; exact one_ne_zero)
  have hlaa : R.lmul a a = R.dual a :=
    H.a_inv.lmul_eq (by rw [H.a_mul_a, if_pos rfl]; exact one_ne_zero)
  have hb : χ (R.dual a) = 1 := by
    have h := hχ.map_lmul H.a_inv a
    rw [hlaa, ha, one_mul] at h
    exact h.symm
  have hρ₁ : χ ρ₁ = χ ρ := by
    have h := hχ.map_lmul H.a_inv ρ
    rw [hl1, ha, one_mul] at h
    exact h.symm
  have hρ₂ : χ ρ₂ = χ ρ := by
    have h := hχ.map_lmul H.a_inv.dual ρ
    rw [hl2, hb, one_mul] at h
    exact h.symm
  have hN : ∀ l, (R.N ρ ρ l : ℝ) = (if l = R.unit then 1 else 0) + (if l = ρ then (m : ℝ) else 0) +
      (if l = ρ₁ then (m : ℝ) else 0) + (if l = ρ₂ then (m : ℝ) else 0) := by
    intro l
    rw [H.ρ_mul_ρ]
    by_cases e1 : l = ρ
    · rw [e1]
      simp [h01, h02, hρu]
    · by_cases e2 : l = ρ₁
      · rw [e2]
        simp [h01.symm, h12, hρ₁u]
      · by_cases e3 : l = ρ₂
        · rw [e3]
          simp [h02.symm, h12.symm, hρ₂u]
        · simp [e1, e2, e3]
  have h := hχ.map_mul ρ ρ
  simp only [hN, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [hχ.map_unit, hρ₁, hρ₂] at h
  linear_combination h

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.rank6_ring_of_fusionAlgebraIso
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.char_rho_sq
