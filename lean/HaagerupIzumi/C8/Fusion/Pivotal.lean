module

public import HaagerupIzumi.C8.Fusion.Rank6

@[expose] public section

/-!
# Uniqueness of the pivotal structure on the rank-six ring

Proposition `prop:optional-algebraic-identification`, lines 4109–4118 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`.

The ratio of two pivotal structures on a categorification of `eq:rank6-ring` is
a tensor automorphism of the identity functor; on simples it is a function
`t : ι → G` (scalars in `G = ℂˣ`) with `t_i t_j = t_l` whenever `l ⊂ i ⊗ j`.
That this is how monoidal automorphisms of the identity act on simples is
categorical and not formalized; the based-ring statement proved here is that
every such `t` is identically one (for any `m ≥ 1`, in particular `m = 1`):
`ρ² ∋ 1, ρ` gives `t_ρ² = 1 = t_ρ`, `ρ² ∋ aρ, a²ρ` gives their scalars, and
`a ⊗ ρ = aρ` gives `t_a = 1`.
-/

namespace HaagerupIzumi.C8.Fusion

open BasedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pivotal uniqueness (lines 4109–4115): a function `t` on the six simples of
`eq:rank6-ring` with `t_i t_j = t_l` whenever `N_{ij}^l > 0` is identically `1`. -/
theorem IsHIRing.pivotal_unique {R : BasedRing ι} {a ρ ρ₁ ρ₂ : ι} {m : ℕ}
    (H : IsHIRing R a ρ ρ₁ ρ₂ m) {G : Type*} [Group G] (t : ι → G)
    (ht : ∀ i j l, R.N i j l ≠ 0 → t i * t j = t l) : ∀ x, t x = 1 := by
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
  have hm : m ≠ 0 := by
    have := H.one_le
    omega
  have hu : t R.unit = 1 := by
    have h := ht R.unit R.unit R.unit (by rw [R.unit_mul, if_pos rfl]; exact one_ne_zero)
    simpa using congrArg (· * (t R.unit)⁻¹) h
  have hρρ1 : t ρ * t ρ = 1 := by
    rw [← hu]
    exact ht ρ ρ R.unit (by rw [H.ρ_mul_ρ]; simp)
  have hρρρ : t ρ * t ρ = t ρ := ht ρ ρ ρ (by rw [H.ρ_mul_ρ]; simp [hρu, hm])
  have htρ : t ρ = 1 := hρρρ.symm.trans hρρ1
  have htρ₁ : t ρ₁ = 1 := by
    have h := ht ρ ρ ρ₁ (by rw [H.ρ_mul_ρ]; simp [hρ₁u, hm])
    rw [← h, htρ, one_mul]
  have htρ₂ : t ρ₂ = 1 := by
    have h := ht ρ ρ ρ₂ (by rw [H.ρ_mul_ρ]; simp [hρ₂u, hm])
    rw [← h, htρ, one_mul]
  have hta : t a = 1 := by
    have h := ht a ρ ρ₁ (by rw [H.a_mul_ρ, if_pos rfl]; exact one_ne_zero)
    rw [htρ, htρ₁, mul_one] at h
    exact h
  have htb : t (R.dual a) = 1 := by
    have h := ht (R.dual a) ρ ρ₂ (by rw [H.a2_mul_ρ, if_pos rfl]; exact one_ne_zero)
    rw [htρ, htρ₂, mul_one] at h
    exact h
  intro x
  rcases H.exhaust x with e | e | e | e | e | e <;> rw [e]
  · exact hu
  · exact hta
  · exact htb
  · exact htρ
  · exact htρ₁
  · exact htρ₂

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.pivotal_unique
