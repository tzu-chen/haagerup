module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The linear certificate for the central-charge-eight top bound

This file formalizes the nonnegative linear identity in the manuscript's
order-thirteen core argument. The fourteen variables stand for top-space
multiplicities. Two inequalities are supplied by the finite sl₂ characters.

The VOA embedding, the charge-minimum formulas, the derivation of the table,
and identification of the stress trace with conformal energy are not asserted
here. Those are separate hypotheses in the paper. The theorem is the exact
real linear implication after those inputs have been supplied.
-/

namespace HaagerupIzumi.CFT

/-- Dimension from the fourteen displayed core top dimensions. -/
def coreTopDimension (x y : Fin 7 → ℝ) : ℝ :=
  x 0 + x 1 + 5 * x 2 + 9 * x 3 + 2 * x 4 + 14 * x 5 + 6 * x 6
  + y 0 + 7 * y 1 + 15 * y 2 + 2 * y 3 + 14 * y 4 + 6 * y 5 + 2 * y 6

/-- The integer-scaled trace `4680 W`, using the printed table. -/
def coreTopScaledTrace (x y : Fin 7 → ℝ) : ℝ :=
  600 * x 1 + 10440 * x 2 + 56640 * x 3 + 5520 * x 4
  + 148560 * x 5 + 54240 * x 6 + 7800 * y 0 + 36960 * y 1
  + 110880 * y 2 + 4080 * y 3 + 81480 * y 4 + 18240 * y 5 + 4920 * y 6

/-- The displayed dual certificate is an exact polynomial identity. -/
theorem core_top_deficit_identity (x y : Fin 7 → ℝ) :
    4680 * ((17 / 10 : ℝ) * coreTopDimension x y) - coreTopScaledTrace x y =
      8460 * (y 2 - x 5) + 28716 * (y 4 - x 5 - x 6)
      + 7956 * x 0 + 7356 * x 1 + 29340 * x 2 + 14964 * x 3
      + 10392 * x 4 + 22212 * x 6 + 156 * y 0 + 18732 * y 1
      + 11832 * y 3 + 1188 * y 4 + 29496 * y 5 + 10992 * y 6 := by
  unfold coreTopDimension coreTopScaledTrace
  ring

/-- Nonnegative multiplicities and the two sl₂ character inequalities imply
the universal top bound, with denominators cleared. -/
theorem core_top_bound (x y : Fin 7 → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h10_12 : x 5 ≤ y 2) (h7_9 : x 5 + x 6 ≤ y 4) :
    10 * coreTopScaledTrace x y ≤ 17 * 4680 * coreTopDimension x y := by
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have hx3 := hx 3
  have hx4 := hx 4
  have hx6 := hx 6
  have hy0 := hy 0
  have hy1 := hy 1
  have hy3 := hy 3
  have hy4 := hy 4
  have hy5 := hy 5
  have hy6 := hy 6
  have hc1 : 0 ≤ y 2 - x 5 := sub_nonneg.mpr h10_12
  have hc2 : 0 ≤ y 4 - x 5 - x 6 := by linarith only [h7_9]
  have hcertificate :
      0 ≤ 4680 * ((17 / 10 : ℝ) * coreTopDimension x y)
        - coreTopScaledTrace x y := by
    rw [core_top_deficit_identity]
    positivity
  linarith only [hcertificate]

#print axioms core_top_deficit_identity
#print axioms core_top_bound

end HaagerupIzumi.CFT
