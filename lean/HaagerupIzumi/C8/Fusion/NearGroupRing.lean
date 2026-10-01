module

public import HaagerupIzumi.C8.Fusion.BasedRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The near-group dimension equation from a character

Line 3358 of `c8_expanded_20260929/haagerup_c8_expanded.tex`: in a based ring with
`ρ² = 1 + a + a² + mρ`, every character `χ` with `χ(a) = χ(a²) = 1` (for instance the
Frobenius–Perron dimension, which is `1` on invertibles) satisfies
`χ(ρ)² = 3 + m χ(ρ)`.  With `m = 3k` this is `d² = 3 + 3kd`, the hypothesis of
`nearGroup_length`.
-/

namespace HaagerupIzumi.C8.Fusion

open BasedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nearGroup_char_sq (R : BasedRing ι) {a b ρ : ι} (m : ℕ)
    (hρρ : ∀ l, R.N ρ ρ l = (if l = R.unit then 1 else 0) + (if l = a then 1 else 0) +
      (if l = b then 1 else 0) + (if l = ρ then m else 0))
    {χ : ι → ℝ} (hχ : R.IsCharacter χ) (ha : χ a = 1) (hb : χ b = 1) :
    χ ρ ^ 2 = 3 + m * χ ρ := by
  have h := hχ.map_mul ρ ρ
  simp [hρρ, add_mul, Finset.sum_add_distrib, hχ.map_unit, ha, hb] at h
  linear_combination h

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.nearGroup_char_sq
