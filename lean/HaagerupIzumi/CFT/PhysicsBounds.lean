module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Algebraic comparison steps in the c=8 thermal bounds

These two lemmas isolate real-number implications in the physics section.
They do not define a partition function, prove convergence or modular
invariance, differentiate an infinite series, establish the positive-energy
tail comparison, or verify the Python interval implementation.

In the intended application, `L,H` are the retained and omitted sums at
the colder inverse temperature, `Ld,Hd` are the corresponding sums at
the modular-dual temperature, and `r = exp (-(b-b') * Ecut)`.  The analytic
argument must supply both `hbalance` and `hcomparison`.  The hypotheses
remain explicit in the kernel-checked statements below.
-/

namespace HaagerupIzumi.CFT

/-- Modular equality and a strict contraction comparison imply the
algebraic heavy-tail bound.  Nonnegativity of `r` is retained to display
the physical range, although the rearrangement itself only uses `r < 1`.
No positivity or convergence of an underlying spectral sum is asserted. -/
theorem modular_heavy_tail_comparison
    (L H Ld Hd r : ℝ)
    (hbalance : L + H = Ld + Hd)
    (hcomparison : H ≤ r * Hd)
    (_hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    H ≤ r * (L - Ld) / (1 - r) := by
  have hden : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hscaled : r * (L + H) = r * (Ld + Hd) :=
    congrArg (fun x : ℝ => r * x) hbalance
  apply (le_div_iff₀ hden).2
  nlinarith only [hcomparison, hscaled]

/-- The algebraic division step of the self-dual thermal bound.
The spectral first-moment inequality is an assumption; this lemma does
not derive it by differentiating the modular functional equation. -/
theorem selfdual_tail_first_moment_comparison
    (Ecut H Lprime : ℝ)
    (hEcut : 0 < Ecut) (hmoment : Ecut * H ≤ Lprime) :
    H ≤ Lprime / Ecut := by
  apply (le_div_iff₀ hEcut).2
  simpa only [mul_comm] using hmoment

#print axioms modular_heavy_tail_comparison
#print axioms selfdual_tail_first_moment_comparison

end HaagerupIzumi.CFT
