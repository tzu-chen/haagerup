module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import HaagerupIzumi.C8.Data.CoreTops
public import HaagerupIzumi.CFT.TopBound

@[expose] public section

/-!
# The derived top table feeds the universal top bound

`HaagerupIzumi.CFT.core_top_bound` (file `CFT/TopBound.lean`) uses the printed top
dimensions `d` and trace contributions `4680 W` of lines 3153–3162 of
`c8_expanded_20260929/haagerup_c8_expanded.tex` as coefficients.  Here these coefficients
are identified with the values derived from the charge data in
`HaagerupIzumi.C8.CoreCharges` (file `Data/CoreTops.lean`)
(`coreTopDimension_eq_topDim`, `coreTopScaledTrace_eq_topW13`), and the bound is restated
with the derived coefficients (`core_top_bound_derived`, eq:sharp-top-bound).

The hypotheses of `core_top_bound_derived` are those of `core_top_bound`: nonnegative
multiplicities and the two sl₂-character inequalities `y₂ ≥ x₅`, `y₄ ≥ x₅ + x₆`
(line 3186), which are inputs about complete right `sl₂` characters.
-/

namespace HaagerupIzumi.C8
namespace CoreCharges

theorem coreTopDimension_eq_topDim (x y : Fin 7 → ℝ) :
    HaagerupIzumi.CFT.coreTopDimension x y =
      ∑ a : Fin 7, (topDim false a : ℝ) * x a + ∑ a : Fin 7, (topDim true a : ℝ) * y a := by
  have hx : ∀ a : Fin 7, topDim false a = topDimTable false a :=
    fun a => topDim_eq_table (false, a)
  have hy : ∀ a : Fin 7, topDim true a = topDimTable true a :=
    fun a => topDim_eq_table (true, a)
  simp only [hx, hy, Fin.sum_univ_seven, topDimTable, HaagerupIzumi.CFT.coreTopDimension,
    Matrix.cons_val, Int.cast_ofNat, Int.cast_one]
  ring

theorem coreTopScaledTrace_eq_topW13 (x y : Fin 7 → ℝ) :
    13 * HaagerupIzumi.CFT.coreTopScaledTrace x y =
      ∑ a : Fin 7, (topW13 false a : ℝ) * x a + ∑ a : Fin 7, (topW13 true a : ℝ) * y a := by
  have hx : ∀ a : Fin 7, topW13 false a = 13 * topWTable false a :=
    fun a => topW13_eq_table (false, a)
  have hy : ∀ a : Fin 7, topW13 true a = 13 * topWTable true a :=
    fun a => topW13_eq_table (true, a)
  simp only [hx, hy, Fin.sum_univ_seven, topWTable, HaagerupIzumi.CFT.coreTopScaledTrace,
    Matrix.cons_val, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
  ring

/-- eq:sharp-top-bound with the coefficients derived from the charge data:
`10 · (4680 W_total) ≤ 17 · 4680 · D`, scaled by `13`. -/
theorem core_top_bound_derived (x y : Fin 7 → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h10_12 : x 5 ≤ y 2) (h7_9 : x 5 + x 6 ≤ y 4) :
    10 * (∑ a : Fin 7, (topW13 false a : ℝ) * x a + ∑ a : Fin 7, (topW13 true a : ℝ) * y a) ≤
      13 * (17 * 4680) *
        (∑ a : Fin 7, (topDim false a : ℝ) * x a + ∑ a : Fin 7, (topDim true a : ℝ) * y a) := by
  rw [← coreTopDimension_eq_topDim, ← coreTopScaledTrace_eq_topW13]
  have h := HaagerupIzumi.CFT.core_top_bound x y hx hy h10_12 h7_9
  linarith

#print axioms coreTopDimension_eq_topDim
#print axioms coreTopScaledTrace_eq_topW13
#print axioms core_top_bound_derived

end CoreCharges
end HaagerupIzumi.C8
