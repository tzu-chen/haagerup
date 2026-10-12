module

public import HaagerupIzumi.C8.Lattice.P4RFRP
public import HaagerupIzumi.C8.Lattice.P4RFRZ
public import HaagerupIzumi.C8.Lattice.S2Closure
public import HaagerupIzumi.C8.Lattice.Relations

@[expose] public section

/-!
# `L(2) P₄ ⊂ S₂` reduces to `L(2) q₊ ∈ S₂`

Written 4 October 2026 (16:45).  `L(2) = ω_(3)` commutes with `F_R(0)`: by the commutator formula
`[ω_(3), f_(0)] = (ω_(0) f)_(3) + 3 (ω_(1) f)_(2) + 3 (ω_(2) f)_(1)`, with `ω_(0) f = T f`
(`FLMInput.Lm1`), `(T f)_(3) = -3 f_(2)` (`mode_T`), `ω_(1) f = f` (`FLMInput.L0`) and
`ω_(2) f = 0` (kernel check `omega_two_fR`).  Since `q₀ = F_R(0) q₊`, `q₋ = F_R(0) q₀`
(`fR_qpV`, `fR_q0V`) and `S₂` is `F_R(0)`-stable (`fR_mem`), the `LowerCertificate` field
`L2_P₄` for `latticeDP` follows from the single membership `ω_(3) q₊ ∈ S2span`
(`L2_P4_latticeDP_of_qp`).  The membership itself (the record: `L(2) q₊ = c · r2_000017`, saved
basis, see `S2Saved.lean`) is not replayed here.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- `L(1) F_R = 0` (kernel check). -/
theorem omega_two_fR : mode omega 2 fR = [] := by
  decide +kernel

theorem zbinom_three (t : ℕ) : zbinom ℂ 3 t = (Nat.choose 3 t : ℂ) := by
  unfold zbinom
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, Ring.choose_natCast]
  exact Int.cast_natCast _

/-- **`[L(2), F_R(0)] = 0`** on the Fock model. -/
theorem L2_fR_comm (hF : FLMInput) (w : V) :
    modeC 3 omegaV (modeC 0 (toV fR) w) = modeC 0 (toV fR) (modeC 3 omegaV w) := by
  have hc : modeC 3 omegaV (modeC 0 (toV fR) w) - modeC 0 (toV fR) (modeC 3 omegaV w) =
      ∑ t ∈ Finset.range (2 + 1), zbinom ℂ 3 t • modeC (3 + 0 - t) (modeC t omegaV (toV fR)) w :=
    (latticeBVA hF).commutator (i := 2) (j := 1) (toV_mem_gradeC omega omega_states)
      (toV_mem_gradeC fR (currents_basisStates 5)) 3 0 w
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hc
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hc
  rw [show (3 : ℤ) + 0 - 0 = 3 by norm_num, show (3 : ℤ) + 0 - 1 = 2 by norm_num,
    show (3 : ℤ) + 0 - 2 = 1 by norm_num] at hc
  have h0 : modeC 0 omegaV (toV fR) = modeC (-2) (toV fR) vacV := hF.Lm1 _
  have h1 : modeC 1 omegaV (toV fR) = toV fR := by
    rw [hF.L0 (d := 1) (toV_mem_gradeC fR (currents_basisStates 5))]
    simp
  have h2 : modeC 2 omegaV (toV fR) = 0 := by
    have h := modeC_toV_of_mode (a := omega) (b := fR) (m := 2) (fun p hp => (omega_states p hp).1)
      (fun p hp => (currents_basisStates 5 p hp).1) omega_two_fR
    rw [omegaV, h]
    simp [toV]
  have hT : modeC 3 (modeC (-2) (toV fR) vacV) w = -((3 : ℂ) • modeC 2 (toV fR) w) := by
    have h := (latticeBVA hF).mode_T 3 (toV fR) w
    rw [BorcherdsVertexAlgebra.T_apply] at h
    change modeC 3 (modeC (-2) (toV fR) vacV) w = -(((3 : ℤ) : ℂ) • modeC (3 - 1) (toV fR) w) at h
    rw [h]
    norm_num
  rw [h0, h1, h2, hT, map_zero, LinearMap.zero_apply, smul_zero, add_zero, zbinom_three,
    zbinom_three, show Nat.choose 3 0 = 1 by decide, show Nat.choose 3 1 = 3 by decide] at hc
  rw [← sub_eq_zero, hc]
  simp

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3)

/-- **`L2_P₄` from `L(2) q₊ ∈ S₂`.** -/
theorem L2_P4_latticeDP_of_qp (h : modeC 3 omegaV qpV ∈ S2span) :
    ∀ q ∈ (latticeDP hF S₃ hS₃).triplet,
      (latticeVOA hF).mode 3 (latticeVOA hF).ω q ∈ (latticeDP hF S₃ hS₃).S₂ := by
  have h0 : modeC 3 omegaV q0V ∈ S2span := by
    rw [← fR_qpV, L2_fR_comm hF]
    exact fR_mem _ h
  have hm : modeC 3 omegaV qmV ∈ S2span := by
    rw [← fR_q0V, L2_fR_comm hF]
    exact fR_mem _ h0
  intro q hq
  simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  exacts [h, h0, hm]

end

#print axioms L2_fR_comm
#print axioms L2_P4_latticeDP_of_qp

end LatticeVOA
end HaagerupIzumi.C8
