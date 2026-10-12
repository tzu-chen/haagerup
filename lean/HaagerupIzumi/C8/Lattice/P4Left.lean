module

public import HaagerupIzumi.C8.Lattice.P4Link
public import HaagerupIzumi.C8.Lattice.P4ELP0
public import HaagerupIzumi.C8.Lattice.P4ELP1
public import HaagerupIzumi.C8.Lattice.P4ELP2
public import HaagerupIzumi.C8.Lattice.P4ELP3
public import HaagerupIzumi.C8.Lattice.P4ELZ0
public import HaagerupIzumi.C8.Lattice.P4ELZ1
public import HaagerupIzumi.C8.Lattice.P4ELZ2
public import HaagerupIzumi.C8.Lattice.P4ELZ3
public import HaagerupIzumi.C8.Lattice.P4ELM0
public import HaagerupIzumi.C8.Lattice.P4ELM1
public import HaagerupIzumi.C8.Lattice.P4ELM2
public import HaagerupIzumi.C8.Lattice.P4ELM3
public import HaagerupIzumi.C8.Lattice.P4FLP0
public import HaagerupIzumi.C8.Lattice.P4FLP1
public import HaagerupIzumi.C8.Lattice.P4FLP2
public import HaagerupIzumi.C8.Lattice.P4FLP3
public import HaagerupIzumi.C8.Lattice.P4FLZ0
public import HaagerupIzumi.C8.Lattice.P4FLZ1
public import HaagerupIzumi.C8.Lattice.P4FLZ2
public import HaagerupIzumi.C8.Lattice.P4FLZ3
public import HaagerupIzumi.C8.Lattice.P4FLM0
public import HaagerupIzumi.C8.Lattice.P4FLM1
public import HaagerupIzumi.C8.Lattice.P4FLM2
public import HaagerupIzumi.C8.Lattice.P4FLM3
@[expose] public section

/-!
# The left currents kill the triplet: controls `eL_q`, `fL_q`

Record `hi_cft_20260923_next_structure_p4_controls.json` (manuscript `cert:lower`): six more of
the 18 current-zero-mode identities, `E_L(0) q = 0` and `F_L(0) q = 0` for `q = q₊, q₀, q₋`,
from the kernel checks `P4EL*.lean`, `P4FL*.lean` (one per chunk of the triplet data) and the
link `toV4_mode`.  With `P4Link.lean` this gives the `LowerCertificate` fields `hL_q`, `eL_q`,
`fL_q`, `hR_qp`, `hR_q0`, `hR_qm` for `latticeDP`; the six right-current identities
(`E_R`, `F_R`) and the Virasoro controls remain (`Lattice/Benchmark.md` §5).

No hypotheses beyond `FLMInput` (only to have the algebra).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

theorem p4_kill_sum {c : Vec} (hc : ∀ p ∈ c, Valid p.1) (μ : ℤ) :
    ∀ l : List Vec4, (∀ x ∈ l, Vec4.mode (Vec4.ofVec c) 0 x = Vec4.zero ∧ x.AllStates (P4Good μ)) →
      modeC 0 (toV c) (l.map toV4).sum = 0
  | [], _ => by simp
  | x :: l, h => by
    obtain ⟨hx, hg⟩ := h x List.mem_cons_self
    have ih := p4_kill_sum hc μ l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hv : x.AllStates Valid := hg.mono fun _ h => h.1
    have e := toV4_mode 0 (Vec4.ofVec c) x (ofVec_allStates hc) hv
    rw [hx, toV4_zero, toV4_ofVec] at e
    simp only [List.map_cons, List.sum_cons]
    rw [map_add, ← e, ih, add_zero]

theorem eL_qpV : modeC 0 (toV eL) qpV = 0 :=
  p4_kill_sum eL_valid 2 p4P (by
    intro x hx
    simp only [p4P, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨p4P_0_eL, p4P_0_good⟩, ⟨p4P_1_eL, p4P_1_good⟩, ⟨p4P_2_eL, p4P_2_good⟩,
      ⟨p4P_3_eL, p4P_3_good⟩])

theorem eL_q0V : modeC 0 (toV eL) q0V = 0 :=
  p4_kill_sum eL_valid 0 p4Z (by
    intro x hx
    simp only [p4Z, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨p4Z_0_eL, p4Z_0_good⟩, ⟨p4Z_1_eL, p4Z_1_good⟩, ⟨p4Z_2_eL, p4Z_2_good⟩,
      ⟨p4Z_3_eL, p4Z_3_good⟩])

theorem eL_qmV : modeC 0 (toV eL) qmV = 0 :=
  p4_kill_sum eL_valid (-2) p4M (by
    intro x hx
    simp only [p4M, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨p4M_0_eL, p4M_0_good⟩, ⟨p4M_1_eL, p4M_1_good⟩, ⟨p4M_2_eL, p4M_2_good⟩,
      ⟨p4M_3_eL, p4M_3_good⟩])

theorem fL_qpV : modeC 0 (toV fL) qpV = 0 :=
  p4_kill_sum fL_valid 2 p4P (by
    intro x hx
    simp only [p4P, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨p4P_0_fL, p4P_0_good⟩, ⟨p4P_1_fL, p4P_1_good⟩, ⟨p4P_2_fL, p4P_2_good⟩,
      ⟨p4P_3_fL, p4P_3_good⟩])

theorem fL_q0V : modeC 0 (toV fL) q0V = 0 :=
  p4_kill_sum fL_valid 0 p4Z (by
    intro x hx
    simp only [p4Z, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨p4Z_0_fL, p4Z_0_good⟩, ⟨p4Z_1_fL, p4Z_1_good⟩, ⟨p4Z_2_fL, p4Z_2_good⟩,
      ⟨p4Z_3_fL, p4Z_3_good⟩])

theorem fL_qmV : modeC 0 (toV fL) qmV = 0 :=
  p4_kill_sum fL_valid (-2) p4M (by
    intro x hx
    simp only [p4M, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨p4M_0_fL, p4M_0_good⟩, ⟨p4M_1_fL, p4M_1_good⟩, ⟨p4M_2_fL, p4M_2_good⟩,
      ⟨p4M_3_fL, p4M_3_good⟩])

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3)

/-- **Control `eL_q`**: `E_L(0)` kills the triplet. -/
theorem eL_q_latticeDP : ∀ q ∈ (latticeDP hF S₃ hS₃).triplet,
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).eL q = 0 := by
  intro q hq
  simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  exacts [eL_qpV, eL_q0V, eL_qmV]

/-- **Control `fL_q`**: `F_L(0)` kills the triplet. -/
theorem fL_q_latticeDP : ∀ q ∈ (latticeDP hF S₃ hS₃).triplet,
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).fL q = 0 := by
  intro q hq
  simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  exacts [fL_qpV, fL_q0V, fL_qmV]

end

#print axioms eL_q_latticeDP
#print axioms fL_q_latticeDP

end LatticeVOA
end HaagerupIzumi.C8
