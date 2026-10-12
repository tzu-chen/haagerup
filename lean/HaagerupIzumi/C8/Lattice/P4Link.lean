module

public import HaagerupIzumi.C8.Lattice.S2Link
public import HaagerupIzumi.C8.Lattice.P4Defs
public import HaagerupIzumi.C8.Lattice.P4StP0
public import HaagerupIzumi.C8.Lattice.P4StP1
public import HaagerupIzumi.C8.Lattice.P4StP2
public import HaagerupIzumi.C8.Lattice.P4StP3
public import HaagerupIzumi.C8.Lattice.P4StZ0
public import HaagerupIzumi.C8.Lattice.P4StZ1
public import HaagerupIzumi.C8.Lattice.P4StZ2
public import HaagerupIzumi.C8.Lattice.P4StZ3
public import HaagerupIzumi.C8.Lattice.P4StM0
public import HaagerupIzumi.C8.Lattice.P4StM1
public import HaagerupIzumi.C8.Lattice.P4StM2
public import HaagerupIzumi.C8.Lattice.P4StM3

@[expose] public section

/-!
# The actual triplet `P₄` in the closure data, and its six Cartan controls

Record `hi_cft_20260923_next_structure_p4_controls.json` (manuscript certificate `cert:lower`,
lines 2253–2259: "the actual `P₄` vectors satisfy 18 current-zero-mode identities"; the triplet
of line 2210, joint current highest weight `(0, 2)`).  The data `q₊ = P4_plus`, `q₀ = P4_zero`,
`q₋ = P4_minus` are `qpV`, `q0V`, `qmV` (`P4Defs.lean`, chunks `P4Data*.lean`), with every
state checked canonical of grade four and with its Cartan eigenvalues (`P4St*.lean`).

* `qpV_mem`, `q0V_mem`, `qmV_mem`: `q ∈ V₄`; `latticeDP hF S₃ hS₃`: the closure data
  `latticeD` of `S2Link.lean` with the actual triplet (only `S₃` remains a parameter).
* The six Cartan controls of `LowerCertificate`, proved (no mode computation in the kernel:
  Cartan zero modes act diagonally, `modeC_cartan_toV4`):
  `hL_q_latticeDP` (`H_L q = 0` for the three vectors), `hR_qp_latticeDP` (`H_R q₊ = 2 q₊`),
  `hR_q0_latticeDP` (`H_R q₀ = 0`), `hR_qm_latticeDP` (`H_R q₋ = -2 q₋`).

The other twelve current identities (`E_L, F_L, E_R, F_R`) and the six Virasoro controls need
mode computations on the 9,300-row vectors; see `Lattice/Benchmark.md` §5.

No hypotheses beyond `FLMInput` (only to have the algebra).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

theorem p4_chunks_facts (μ : ℤ) : ∀ l : List Vec4, (∀ x ∈ l, x.AllStates (P4Good μ)) →
    (l.map toV4).sum ∈ gradeC 4 ∧ modeC 0 (toV hL) (l.map toV4).sum = 0 ∧
      modeC 0 (toV hR) (l.map toV4).sum = ((μ : ℚ) : ℂ) • (l.map toV4).sum
  | [], _ => by simp
  | x :: l, h => by
    obtain ⟨hL', hR', hg⟩ := P4Good.cartan (h x List.mem_cons_self)
    obtain ⟨ih1, ih2, ih3⟩ := p4_chunks_facts μ l fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨Submodule.add_mem _ (toV4_mem_gradeC x hg) ih1, ?_, ?_⟩
    · rw [map_add, modeC_cartan_toV4 hL hL_cartan _ x hL', ih2]
      simp
    · rw [map_add, modeC_cartan_toV4 hR hR_cartan _ x hR', ih3, smul_add]

theorem qpV_facts : qpV ∈ gradeC 4 ∧ modeC 0 (toV hL) qpV = 0 ∧
    modeC 0 (toV hR) qpV = (((2 : ℤ) : ℚ) : ℂ) • qpV :=
  p4_chunks_facts 2 p4P (by
    intro x hx
    simp only [p4P, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [p4P_0_good, p4P_1_good, p4P_2_good, p4P_3_good])

theorem q0V_facts : q0V ∈ gradeC 4 ∧ modeC 0 (toV hL) q0V = 0 ∧
    modeC 0 (toV hR) q0V = (((0 : ℤ) : ℚ) : ℂ) • q0V :=
  p4_chunks_facts 0 p4Z (by
    intro x hx
    simp only [p4Z, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [p4Z_0_good, p4Z_1_good, p4Z_2_good, p4Z_3_good])

theorem qmV_facts : qmV ∈ gradeC 4 ∧ modeC 0 (toV hL) qmV = 0 ∧
    modeC 0 (toV hR) qmV = (((-2 : ℤ) : ℚ) : ℂ) • qmV :=
  p4_chunks_facts (-2) p4M (by
    intro x hx
    simp only [p4M, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [p4M_0_good, p4M_1_good, p4M_2_good, p4M_3_good])

/-- The actual triplet lies in `V₄`. -/
theorem triplet_grade_P4 : ∀ q ∈ ({qpV, q0V, qmV} : Set V), q ∈ gradeC 4 := by
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  exacts [qpV_facts.1, q0V_facts.1, qmV_facts.1]

/-- The closure data of the lattice VOA with `S₂ = S2span` and the actual triplet `P₄`;
`S₃` is the remaining parameter. -/
noncomputable def latticeDP (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3) :
    ClosureData (latticeVOA hF) :=
  latticeD hF S₃ hS₃ qpV q0V qmV triplet_grade_P4

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3)

/-- **Control `hL_q`**: `H_L(0)` kills the triplet. -/
theorem hL_q_latticeDP : ∀ q ∈ (latticeDP hF S₃ hS₃).triplet,
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).hL q = 0 := by
  intro q hq
  simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  exacts [qpV_facts.2.1, q0V_facts.2.1, qmV_facts.2.1]

/-- **Control `hR_qp`**: `H_R(0) q₊ = 2 q₊`. -/
theorem hR_qp_latticeDP :
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).hR (latticeDP hF S₃ hS₃).qp =
      (2 : ℂ) • (latticeDP hF S₃ hS₃).qp := by
  have h := qpV_facts.2.2
  push_cast at h
  exact h

/-- **Control `hR_q0`**: `H_R(0) q₀ = 0`. -/
theorem hR_q0_latticeDP :
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).hR (latticeDP hF S₃ hS₃).q0 = 0 := by
  have h := q0V_facts.2.2
  simp only [Int.cast_zero, Rat.cast_zero, zero_smul] at h
  exact h

/-- **Control `hR_qm`**: `H_R(0) q₋ = -2 q₋`. -/
theorem hR_qm_latticeDP :
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).hR (latticeDP hF S₃ hS₃).qm =
      (-2 : ℂ) • (latticeDP hF S₃ hS₃).qm := by
  have h := qmV_facts.2.2
  push_cast at h
  exact h

end

#print axioms triplet_grade_P4
#print axioms hL_q_latticeDP
#print axioms hR_qp_latticeDP
#print axioms hR_q0_latticeDP
#print axioms hR_qm_latticeDP

end LatticeVOA
end HaagerupIzumi.C8
