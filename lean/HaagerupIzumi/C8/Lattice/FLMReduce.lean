module

public import HaagerupIzumi.C8.Lattice.VOA
public import HaagerupIzumi.C8.Lattice.FLMGen
public import HaagerupIzumi.C8.Lattice.FLMChecks

@[expose] public section

/-!
# `FLMInput` reduces to the Borcherds identity

Benchmark item 4 (`Lattice/Benchmark.md` §5).  `FLMInput` (`Lattice/VOA.lean`) assumes three
things about the modes `modeC` of the Fock model: the Borcherds identity, `L(0) = ω_(1)` acts on
`V_d` by `d`, and `L(-1) = ω_(0)` is `a ↦ a_(-2)𝟏`.  Here the last two are **proved** from the
first:

* `lm1_of_borcherds`: `ω_(0) a = a_(-2)𝟏` for all `a`;
* `l0_of_borcherds`: `ω_(1) a = d a` for `a ∈ V_d`;
* `flmInput_of_borcherds : FLMBorcherds → FLMInput`, `flmInput_iff_borcherds`.

`FLMBorcherds` is exactly the field `FLMInput.borcherds` (the Borcherds identity for `modeC` on
homogeneous vectors, FLM Theorem 8.10.2), which remains the one assumed input.

**Proof.**  Let `B` be the Borcherds vertex algebra built from `FLMBorcherds` alone
(`bvaOfBorcherds`; all other fields are theorems about the model).  For each of the 24 fields
`b ∈ {hᵢ(-1)𝟏, e^{±αᵢ}}` the kernel checks `b ∈ V₁`, `ω_(0) b = b_(-2)𝟏` and `ω_(1) b = b`
(`genList_checks`, `FLMChecks.lean`).  The commutator formula of `B` then gives, for every `w`,
`[ω_(0), b_(n)] w = (ω_(0) b)_(n) w = (T b)_(n) w = [T, b_(n)] w` and
`[ω_(1), b_(n)] w = (ω_(0) b)_(n+1) w + (ω_(1) b)_(n) w = -n b_(n) w = [deg, b_(n)] w`
(`omega_zero_comm`, `omega_one_comm`, `degOp_modeC`, with `mode_T`, `T_mode` of `B`).  Hence
the kernels of `ω_(0) - T` and `ω_(1) - deg` contain `𝟏` and are stable under the modes of the 24
fields, so they are all of `V` (`eq_top_of_genClosed`, `FLMGen.lean`).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## The generators in `V` -/

theorem toV_hgen (i : ℕ) : toV (hgen i) = hV i := by
  rw [hgen, toV_cons_mk, toV_nil, add_zero,
    canon_of_valid (s := (Mom.zero, [i])) (List.pairwise_singleton _ _), Rat.cast_one]
  rfl

theorem toV_egen (α : Mom) : toV (egen α) = eV α := by
  rw [egen, toV_cons_mk, toV_nil, add_zero, canon_of_valid (s := (α, [])) List.Pairwise.nil,
    Rat.cast_one]
  rfl

theorem genSet_eq_toV : ∀ b ∈ GenSet, ∃ v ∈ genList, toV v = b := by
  rintro b ⟨i, hi, rfl | rfl | rfl⟩
  · exact ⟨hgen i, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩, toV_hgen i⟩
  · exact ⟨egen (Mom.simple i), List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩,
      toV_egen _⟩
  · exact ⟨egen (Mom.neg (Mom.simple i)), List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩,
      toV_egen _⟩

/-- The kernel checks, in `V`: the 24 fields have weight one, `ω_(0) b = b_(-2)𝟏`,
`ω_(1) b = b`. -/
theorem genSet_facts : ∀ b ∈ GenSet, b ∈ gradeC 1 ∧ modeC 0 omegaV b = modeC (-2) b vacV ∧
    modeC 1 omegaV b = b := by
  intro b hb
  obtain ⟨v, hv, rfl⟩ := genSet_eq_toV b hb
  obtain ⟨hst, h0, h1⟩ := genList_checks v hv
  have hval : ∀ p ∈ v, Valid p.1 := fun p hp => (hst p hp).1
  have hω : ∀ p ∈ omega, Valid p.1 := fun p hp => (omega_states p hp).1
  have hvac : ∀ p ∈ vac, Valid p.1 := by
    intro p hp
    simp only [vac, List.mem_singleton] at hp
    rw [hp]
    exact List.Pairwise.nil
  refine ⟨toV_mem_gradeC v hst, ?_, ?_⟩
  · have e := congrArg toV h0
    rw [toV_canonVec, toV_canonVec, toV_mode 0 omega v hω hval, toV_mode (-2) v vac hval hvac,
      toV_vac_eq] at e
    exact e
  · have e := congrArg toV h1
    rw [toV_canonVec, toV_canonVec, toV_mode 1 omega v hω hval] at e
    exact e

/-! ## The Borcherds identity alone -/

/-- **The Borcherds identity for the modes of the Fock model** (FLM Theorem 8.10.2): exactly the
field `FLMInput.borcherds`. -/
abbrev FLMBorcherds : Prop :=
  ∀ {i j l : ℕ} {a b c : V}, a ∈ gradeC i → b ∈ gradeC j → c ∈ gradeC l →
    ∀ p q r : ℤ,
    ∑ t ∈ Finset.range (i + j + l + p.natAbs + q.natAbs + r.natAbs + 1),
        zbinom ℂ p t • modeC (p + q - t) (modeC (r + t) a b) c =
      ∑ t ∈ Finset.range (i + j + l + p.natAbs + q.natAbs + r.natAbs + 1),
        ((-1 : ℂ) ^ t * zbinom ℂ r t) •
          (modeC (p + r - t) a (modeC (q + t) b c) -
            (-1 : ℂ) ^ r • modeC (q + r - t) b (modeC (p + t) a c))

/-- The Borcherds vertex algebra of the Fock model from the Borcherds identity alone. -/
noncomputable def bvaOfBorcherds (hB : FLMBorcherds) : BorcherdsVertexAlgebra ℂ V where
  mode := modeC
  vac := vacV
  grade := gradeC
  grade_internal := gradeC_internal
  grade_zero := gradeC_zero
  mode_grade := modeC_mem_gradeC
  mode_trunc := modeC_eq_zero_of_le
  vac_mode := modeC_vac
  mode_vac_nonneg := modeC_vac_nonneg
  mode_vac_neg_one := modeC_vac_neg_one
  borcherds := fun ha hb hc p q r => hB ha hb hc p q r

theorem zbinom_one_two : zbinom ℂ 1 2 = 0 := by
  have h := zbinom_natCast_of_lt ℂ (n := 1) (t := 2) (by norm_num)
  rwa [Nat.cast_one] at h

/-- `[ω_(0), b_(n)] = (ω_(0) b)_(n)` for `b ∈ V₁` (commutator formula). -/
theorem omega_zero_comm (hB : FLMBorcherds) {b : V} (hb : b ∈ gradeC 1) (n : ℤ) (w : V) :
    modeC 0 omegaV (modeC n b w) =
      modeC n b (modeC 0 omegaV w) + modeC n (modeC 0 omegaV b) w := by
  have h := (bvaOfBorcherds hB).commutator (i := 2) (j := 1) omegaV_mem hb 0 n w
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, sub_zero, zbinom_zero_right, zbinom_zero_left_of_pos ℂ one_pos,
    zbinom_zero_left_of_pos ℂ two_pos, zero_smul, add_zero, one_smul] at h
  change modeC 0 omegaV (modeC n b w) - modeC n b (modeC 0 omegaV w) =
    modeC n (modeC 0 omegaV b) w at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- `[ω_(1), b_(n)] = -n b_(n)` for `b ∈ V₁` with `ω_(0) b = b_(-2)𝟏` and `ω_(1) b = b`. -/
theorem omega_one_comm (hB : FLMBorcherds) {b : V} (hb : b ∈ gradeC 1)
    (h0 : modeC 0 omegaV b = modeC (-2) b vacV) (h1 : modeC 1 omegaV b = b) (n : ℤ) (w : V) :
    modeC 1 omegaV (modeC n b w) = modeC n b (modeC 1 omegaV w) - (n : ℂ) • modeC n b w := by
  have h := (bvaOfBorcherds hB).commutator (i := 2) (j := 1) omegaV_mem hb 1 n w
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, sub_zero, zbinom_zero_right, zbinom_one_right, Int.cast_one, zbinom_one_two,
    zero_smul, add_zero, one_smul, add_sub_cancel_left] at h
  change modeC 1 omegaV (modeC n b w) - modeC n b (modeC 1 omegaV w) =
    modeC (1 + n) (modeC 0 omegaV b) w + modeC n (modeC 1 omegaV b) w at h
  have hT := (bvaOfBorcherds hB).mode_T (1 + n) b w
  change modeC (1 + n) (modeC (-2) b vacV) w = -(((1 + n : ℤ) : ℂ) • modeC (1 + n - 1) b w)
    at hT
  rw [h0, h1, hT, add_sub_cancel_left, sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

/-! ## The grading operator -/

/-- `deg`: multiplication by the weight on each canonical monomial. -/
noncomputable def degOp : V →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun s : ValidState => (grade s.1 : ℂ) • Finsupp.single s (1 : ℂ)

theorem degOp_single (s : ValidState) (c : ℂ) :
    degOp (Finsupp.single s c) = (grade s.1 : ℂ) • Finsupp.single s c := by
  rw [degOp, Finsupp.linearCombination_single, smul_comm, Finsupp.smul_single, smul_eq_mul,
    mul_one]

theorem degOp_of_mem {d : ℕ} {a : V} (ha : a ∈ gradeC d) : degOp a = (d : ℂ) • a := by
  rw [gradeC_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    have hs' : grade s.1 = d := hs
    rw [degOp_single, hs']
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- `[deg, b_(n)] = -n b_(n)` for `b ∈ V₁` (the weight rule `mode_grade`). -/
theorem degOp_modeC {b : V} (hb : b ∈ gradeC 1) (n : ℤ) (w : V) :
    degOp (modeC n b w) = modeC n b (degOp w) - (n : ℂ) • modeC n b w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, smul_add]
    abel
  | single s c =>
    have hw : Finsupp.single s c ∈ gradeC (grade s.1) := single_mem_gradeC rfl c
    rw [degOp_single, map_smul]
    by_cases hn : n + 1 ≤ ((1 : ℕ) : ℤ) + (grade s.1 : ℤ)
    · rw [degOp_of_mem (modeC_mem_gradeC n hb hw hn)]
      have hnn : 0 ≤ ((1 : ℕ) : ℤ) + (grade s.1 : ℤ) - n - 1 := by omega
      have e : ((((1 : ℕ) : ℤ) + (grade s.1 : ℤ) - n - 1).toNat : ℂ) = (grade s.1 : ℂ) - n := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
        push_cast
        ring
      rw [e, sub_smul]
    · rw [modeC_eq_zero_of_le n hb hw (by omega)]
      simp

/-! ## `L(-1)` and `L(0)` -/

/-- **`L(-1) = ω_(0)` is the translation**, from the Borcherds identity and the kernel checks. -/
theorem lm1_of_borcherds (hB : FLMBorcherds) (a : V) : modeC 0 omegaV a = modeC (-2) a vacV := by
  let D : V →ₗ[ℂ] V := modeC 0 omegaV - (modeC (-2)).flip vacV
  have hD : ∀ x, D x = modeC 0 omegaV x - modeC (-2) x vacV := fun x => rfl
  have hW : GenClosed (LinearMap.ker D) := by
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, hD, modeC_vac_nonneg 0 omegaV le_rfl, modeC_vac,
        if_neg (by norm_num), sub_zero]
    · intro b hb n w hw
      obtain ⟨hb1, hb0, -⟩ := genSet_facts b hb
      rw [LinearMap.mem_ker, hD] at hw ⊢
      have hT := (bvaOfBorcherds hB).T_mode n b w
      change modeC (-2) (modeC n b w) vacV =
        modeC n (modeC (-2) b vacV) w + modeC n b (modeC (-2) w vacV) at hT
      rw [omega_zero_comm hB hb1 n w, hT, hb0, sub_eq_zero.1 hw]
      abel
  have ha : a ∈ LinearMap.ker D := by
    rw [eq_top_of_genClosed hW]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hD, sub_eq_zero] at ha
  exact ha

/-- **`L(0) = ω_(1)` acts on `V_d` by `d`**, from the Borcherds identity and the kernel checks. -/
theorem l0_of_borcherds (hB : FLMBorcherds) {d : ℕ} {a : V} (ha : a ∈ gradeC d) :
    modeC 1 omegaV a = (d : ℂ) • a := by
  let E : V →ₗ[ℂ] V := modeC 1 omegaV - degOp
  have hE : ∀ x, E x = modeC 1 omegaV x - degOp x := fun x => rfl
  have hW : GenClosed (LinearMap.ker E) := by
    refine ⟨?_, ?_⟩
    · have hv : vacV ∈ gradeC 0 := by
        rw [gradeC_zero]
        exact Submodule.mem_span_singleton_self vacV
      rw [LinearMap.mem_ker, hE, modeC_vac_nonneg 1 omegaV zero_le_one, degOp_of_mem hv,
        Nat.cast_zero, zero_smul, sub_zero]
    · intro b hb n w hw
      obtain ⟨hb1, hb0, hb1'⟩ := genSet_facts b hb
      rw [LinearMap.mem_ker, hE] at hw ⊢
      rw [omega_one_comm hB hb1 hb0 hb1' n w, degOp_modeC hb1 n w, sub_eq_zero.1 hw]
      abel
  have ha' : a ∈ LinearMap.ker E := by
    rw [eq_top_of_genClosed hW]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hE, sub_eq_zero, degOp_of_mem ha] at ha'
  exact ha'

/-- **Item 4: `FLMInput` follows from the Borcherds identity alone.** -/
theorem flmInput_of_borcherds (hB : FLMBorcherds) : FLMInput :=
  ⟨fun ha hb hc p q r => hB ha hb hc p q r, fun ha => l0_of_borcherds hB ha,
    lm1_of_borcherds hB⟩

theorem flmInput_iff_borcherds : FLMInput ↔ FLMBorcherds :=
  ⟨fun hF => fun ha hb hc p q r => hF.borcherds ha hb hc p q r, flmInput_of_borcherds⟩

/-- The lattice vertex operator algebra from the Borcherds identity alone. -/
noncomputable def latticeVOAOfBorcherds (hB : FLMBorcherds) : VertexOperatorAlgebra ℂ V :=
  latticeVOA (flmInput_of_borcherds hB)

#print axioms genSet_facts
#print axioms lm1_of_borcherds
#print axioms l0_of_borcherds
#print axioms flmInput_of_borcherds
#print axioms flmInput_iff_borcherds

end LatticeVOA
end HaagerupIzumi.C8
