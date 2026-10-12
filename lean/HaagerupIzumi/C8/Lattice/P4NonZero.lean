module

public import HaagerupIzumi.C8.Lattice.P4Link

@[expose] public section
/-!
# The triplet `q₊, q₀, q₋` is nonzero

The controls of `P4Link.lean`, `P4Left.lean`, `P4RFR*.lean` would hold trivially for a zero
triplet; this file checks in the kernel that the exported vectors are not zero.  For each of
`qpV`, `q0V`, `qmV` one pure exponential state `e^β` (no oscillators; the first state of data
chunk 0, which occurs in no other chunk) is evaluated: the coefficient (summed over the four
chunks, `Vec4.coeff`) is the printed element of `ℚ(√13, √-3)`, and it has a kernel-checked
inverse (`QA.toC_ne_zero_of_mul_eq_one`).

* `qpV_ne_zero`, `q0V_ne_zero`, `qmV_ne_zero`; for the closure data,
  `qp_ne_zero_latticeDP`, `q0_ne_zero_latticeDP`, `qm_ne_zero_latticeDP`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem allValid_of_good {x : Vec4} {μ : ℤ} (h : x.AllStates (P4Good μ)) :
    x.AllStates Valid := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨fun p hp => (h0 p hp).1, fun p hp => (h1 p hp).1, fun p hp => (h2 p hp).1,
    fun p hp => (h3 p hp).1⟩

/-- The value at a state of a sum of chunks. -/
theorem sum_toV4_apply (s : ValidState) : ∀ l : List Vec4, (∀ x ∈ l, x.AllStates Valid) →
    (l.map toV4).sum s = (l.foldr (fun x acc => QA.add (Vec4.coeff x s.1) acc) QA.zero).toC
  | [], _ => by simp [QA.toC_zero]
  | x :: l, h => by
    have ih := sum_toV4_apply s l fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons, Finsupp.add_apply,
      toV4_apply x (h x List.mem_cons_self), ih, List.foldr_cons, QA.toC_add]

theorem p4P_valid : ∀ x ∈ p4P, x.AllStates Valid := by
  intro x hx
  simp only [p4P, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [allValid_of_good p4P_0_good, allValid_of_good p4P_1_good,
    allValid_of_good p4P_2_good, allValid_of_good p4P_3_good]

theorem p4Z_valid : ∀ x ∈ p4Z, x.AllStates Valid := by
  intro x hx
  simp only [p4Z, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [allValid_of_good p4Z_0_good, allValid_of_good p4Z_1_good,
    allValid_of_good p4Z_2_good, allValid_of_good p4Z_3_good]

theorem p4M_valid : ∀ x ∈ p4M, x.AllStates Valid := by
  intro x hx
  simp only [p4M, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [allValid_of_good p4M_0_good, allValid_of_good p4M_1_good,
    allValid_of_good p4M_2_good, allValid_of_good p4M_3_good]

/-- The coefficient of `s` in a list of chunks. -/
def chunksCoeff (l : List Vec4) (s : State) : QA :=
  l.foldr (fun x acc => QA.add (Vec4.coeff x s) acc) QA.zero

/-- Probe state of `q₊`: `e^β`, `β` with zig-zag code `[1, 1, 1, 2, 2, 0, 2, 2]`. -/
def probeP : ValidState := ⟨decState [1, 1, 1, 2, 2, 0, 2, 2], by decide⟩

/-- Probe state of `q₀`: `e^β`, `β` with zig-zag code `[1, 1, 1, 0, 0, 0, 2, 4]`. -/
def probeZ : ValidState := ⟨decState [1, 1, 1, 0, 0, 0, 2, 4], by decide⟩

/-- Probe state of `q₋`: `e^β`, `β` with zig-zag code `[3, 1, 0, 0, 0, 0, 2, 2]`. -/
def probeM : ValidState := ⟨decState [3, 1, 0, 0, 0, 0, 2, 2], by decide⟩

/-- The coefficient of `probeP` in `q₊`. -/
def coeffP : QA :=
  ⟨-756809937135399643439 / 1973668845645937440000,
    -1089966405136230686819 / 10263077997358874688000,
    752759136775251919 / 87718615362041664000,
    1069269501333691573703 / 25657694993397186720000⟩

/-- The coefficient of `probeZ` in `q₀`. -/
def coeffZ : QA :=
  ⟨-133280176055222513441 / 39473376912918748800,
    26546623768980651311 / 36653849990567409600,
    5298307104625930621 / 506068934781009600,
    -609932354426016758407 / 513153899867943734400⟩

/-- The coefficient of `probeM` in `q₋`. -/
def coeffM : QA :=
  ⟨-4367510736689498611 / 1644724038038281200,
    -3193579314029459479 / 1221794999685580320,
    -22976058086121558175 / 1184201307387562464,
    71508990336585682019 / 96216356225239450200⟩

theorem chunksCoeff_P : chunksCoeff p4P probeP.1 = coeffP := by decide +kernel

theorem chunksCoeff_Z : chunksCoeff p4Z probeZ.1 = coeffZ := by decide +kernel

theorem chunksCoeff_M : chunksCoeff p4M probeM.1 = coeffM := by decide +kernel

theorem coeffP_inv : QA.mul coeffP (QA.inv coeffP) = QA.one := by decide +kernel

theorem coeffZ_inv : QA.mul coeffZ (QA.inv coeffZ) = QA.one := by decide +kernel

theorem coeffM_inv : QA.mul coeffM (QA.inv coeffM) = QA.one := by decide +kernel

theorem qpV_apply_probe : qpV probeP = coeffP.toC := by
  have h := sum_toV4_apply probeP p4P p4P_valid
  rw [← chunksCoeff_P]
  exact h

theorem q0V_apply_probe : q0V probeZ = coeffZ.toC := by
  have h := sum_toV4_apply probeZ p4Z p4Z_valid
  rw [← chunksCoeff_Z]
  exact h

theorem qmV_apply_probe : qmV probeM = coeffM.toC := by
  have h := sum_toV4_apply probeM p4M p4M_valid
  rw [← chunksCoeff_M]
  exact h

/-- `q₊ ≠ 0`. -/
theorem qpV_ne_zero : qpV ≠ 0 := by
  intro h
  have e : qpV probeP = 0 := by rw [h, Finsupp.zero_apply]
  rw [qpV_apply_probe] at e
  exact QA.toC_ne_zero_of_mul_eq_one coeffP_inv e

/-- `q₀ ≠ 0`. -/
theorem q0V_ne_zero : q0V ≠ 0 := by
  intro h
  have e : q0V probeZ = 0 := by rw [h, Finsupp.zero_apply]
  rw [q0V_apply_probe] at e
  exact QA.toC_ne_zero_of_mul_eq_one coeffZ_inv e

/-- `q₋ ≠ 0`. -/
theorem qmV_ne_zero : qmV ≠ 0 := by
  intro h
  have e : qmV probeM = 0 := by rw [h, Finsupp.zero_apply]
  rw [qmV_apply_probe] at e
  exact QA.toC_ne_zero_of_mul_eq_one coeffM_inv e

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3)

theorem qp_ne_zero_latticeDP : (latticeDP hF S₃ hS₃).qp ≠ 0 := qpV_ne_zero

theorem q0_ne_zero_latticeDP : (latticeDP hF S₃ hS₃).q0 ≠ 0 := q0V_ne_zero

theorem qm_ne_zero_latticeDP : (latticeDP hF S₃ hS₃).qm ≠ 0 := qmV_ne_zero

end

#print axioms qpV_ne_zero
#print axioms q0V_ne_zero
#print axioms qmV_ne_zero
#print axioms qp_ne_zero_latticeDP

end LatticeVOA
end HaagerupIzumi.C8
