module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# Pivot checks without rational arithmetic

The triangularity checks of the echelon basis of `S₂` (`S2Tri*.lean`) evaluated `Vec4.coeff`,
i.e. sums of rationals, in the kernel; this exhausted 4 GiB (job `121449-cb0bbd`).  Here the
coefficient of a state is read off the *list* of coefficients attached to it
(`coeffsAt`, a filter on states), so that the kernel only compares states:

* `coeffOf_eq_sum_coeffsAt`: `coeffOf v s` is the sum of `coeffsAt v s`;
* `Vec4.PivotAt x s`: `s` occurs once in `x`, in the rational component, with coefficient `1`;
  then `Vec4.coeff x s = QA.one` (`Vec4.coeff_of_pivotAt`);
* `Vec4.AbsentAt x s`: `s` does not occur in `x`; then `Vec4.coeff x s = QA.zero`
  (`Vec4.coeff_of_absentAt`).

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- The coefficients attached to the state `s` in a sparse list. -/
def coeffsAt (v : Vec) (s : State) : List ℚ :=
  (v.filter fun p => decide (p.1 = s)).map Prod.snd

theorem coeffOf_eq_sum_coeffsAt (v : Vec) (s : State) : coeffOf v s = (coeffsAt v s).sum := by
  induction v with
  | nil => simp [coeffOf, coeffsAt]
  | cons p v ih =>
    have e1 : coeffOf (p :: v) s = (if p.1 = s then p.2 else 0) + coeffOf v s := by
      simp [coeffOf]
    rw [e1, ih]
    by_cases h : p.1 = s
    · simp [coeffsAt, List.filter_cons, h]
    · simp [coeffsAt, List.filter_cons, h]

/-- `s` occurs exactly once in `x`, in the rational component, with coefficient `1`. -/
def Vec4.PivotAt (x : Vec4) (s : State) : Prop :=
  coeffsAt x.c0 s = [1] ∧ coeffsAt x.c1 s = [] ∧ coeffsAt x.c2 s = [] ∧ coeffsAt x.c3 s = []

/-- `s` does not occur in `x`. -/
def Vec4.AbsentAt (x : Vec4) (s : State) : Prop :=
  coeffsAt x.c0 s = [] ∧ coeffsAt x.c1 s = [] ∧ coeffsAt x.c2 s = [] ∧ coeffsAt x.c3 s = []

instance (x : Vec4) (s : State) : Decidable (x.PivotAt s) :=
  inferInstanceAs (Decidable (coeffsAt x.c0 s = [1] ∧ coeffsAt x.c1 s = [] ∧
    coeffsAt x.c2 s = [] ∧ coeffsAt x.c3 s = []))

instance (x : Vec4) (s : State) : Decidable (x.AbsentAt s) :=
  inferInstanceAs (Decidable (coeffsAt x.c0 s = [] ∧ coeffsAt x.c1 s = [] ∧
    coeffsAt x.c2 s = [] ∧ coeffsAt x.c3 s = []))

theorem Vec4.coeff_of_pivotAt {x : Vec4} {s : State} (h : x.PivotAt s) :
    Vec4.coeff x s = QA.one := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [Vec4.coeff, coeffOf_eq_sum_coeffsAt, h0, h1, h2, h3, List.sum_cons, List.sum_nil,
    add_zero, QA.one]

theorem Vec4.coeff_of_absentAt {x : Vec4} {s : State} (h : x.AbsentAt s) :
    Vec4.coeff x s = QA.zero := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [Vec4.coeff, coeffOf_eq_sum_coeffsAt, h0, h1, h2, h3, List.sum_nil, QA.zero]

/-- A small check of the decision procedure. -/
example : (Vec4.ofVec [((Mom.zero, [0]), 1)]).PivotAt (Mom.zero, [0]) := by
  decide +kernel

#print axioms Vec4.coeff_of_pivotAt
#print axioms Vec4.coeff_of_absentAt

end LatticeVOA
end HaagerupIzumi.C8
