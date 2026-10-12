module

public import HaagerupIzumi.C8.Lattice.P4RFRP
public import HaagerupIzumi.C8.Lattice.P4RFRZ
public import HaagerupIzumi.C8.Lattice.P4RERP

@[expose] public section

/-!
# The controls `eR_q0`, `eR_qm` from the `𝔰𝔩₂` relations

`E_R(0) q₀ = 2 q₊` and `E_R(0) q₋ = 2 q₀` follow from `F_R(0) q₊ = q₀`, `F_R(0) q₀ = q₋`,
`E_R(0) q₊ = 0` (`P4R*.lean`), `H_R(0) q₊ = 2 q₊`, `H_R(0) q₀ = 0` (`P4Link.lean`) and the
commutator formula `[E_R(0), F_R(0)] = (E_R(0) F_R)(0) = H_R(0)` of the lattice VOA (this step
uses `FLMInput`).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- `[e_(0), f_(0)] = (e_(0) f)_(0)` for weight-one vectors (commutator formula). -/
theorem bracket_zero_modeC (hF : FLMInput) {e f h : Vec} (he : ∀ p ∈ e, Valid p.1 ∧ grade p.1 = 1)
    (hf : ∀ p ∈ f, Valid p.1 ∧ grade p.1 = 1) (hef : mode e 0 f = h) (w : V) :
    modeC 0 (toV e) (modeC 0 (toV f) w) =
      modeC 0 (toV f) (modeC 0 (toV e) w) + modeC 0 (toV h) w := by
  have hc := (latticeBVA hF).commutator (i := 1) (j := 1) (toV_mem_gradeC e he)
    (toV_mem_gradeC f hf) 0 0 w
  have hbr : modeC 0 (toV e) (toV f) = toV h :=
    modeC_toV_of_mode (fun p hp => (he p hp).1) (fun p hp => (hf p hp).1) hef
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, sub_zero, zbinom_zero_right, zbinom_zero_left_of_pos ℂ one_pos, zero_smul,
    add_zero, one_smul] at hc
  change modeC 0 (toV e) (modeC 0 (toV f) w) - modeC 0 (toV f) (modeC 0 (toV e) w) =
    modeC 0 (modeC 0 (toV e) (toV f)) w at hc
  rw [hbr] at hc
  rw [← hc]
  abel

theorem eR_q0V (hF : FLMInput) : modeC 0 (toV eR) q0V = (2 : ℂ) • qpV := by
  have hb := bracket_zero_modeC hF (e := eR) (f := fR) (h := hR) (currents_basisStates 4)
    (currents_basisStates 5) right_sl2.2.2.1 qpV
  have h2 := qpV_facts.2.2
  push_cast at h2
  rw [fR_qpV, eR_qpV, map_zero, h2, zero_add] at hb
  exact hb

theorem eR_qmV (hF : FLMInput) : modeC 0 (toV eR) qmV = (2 : ℂ) • q0V := by
  have hb := bracket_zero_modeC hF (e := eR) (f := fR) (h := hR) (currents_basisStates 4)
    (currents_basisStates 5) right_sl2.2.2.1 q0V
  have h0 := q0V_facts.2.2
  simp only [Int.cast_zero, Rat.cast_zero, zero_smul] at h0
  rw [fR_q0V, eR_q0V hF, map_smul, fR_qpV, h0, add_zero] at hb
  exact hb

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3)

/-- **Control `eR_q0`**: `E_R(0) q₀ = 2 q₊`. -/
theorem eR_q0_latticeDP :
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).eR (latticeDP hF S₃ hS₃).q0 =
      (2 : ℂ) • (latticeDP hF S₃ hS₃).qp :=
  eR_q0V hF

/-- **Control `eR_qm`**: `E_R(0) q₋ = 2 q₀`. -/
theorem eR_qm_latticeDP :
    (latticeVOA hF).mode 0 (latticeDP hF S₃ hS₃).eR (latticeDP hF S₃ hS₃).qm =
      (2 : ℂ) • (latticeDP hF S₃ hS₃).q0 :=
  eR_qmV hF

end

#print axioms eR_q0_latticeDP
#print axioms eR_qm_latticeDP

end LatticeVOA
end HaagerupIzumi.C8
