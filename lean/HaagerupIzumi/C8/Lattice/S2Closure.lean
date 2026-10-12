module

public import HaagerupIzumi.C8.Lattice.S2ClosureOps

@[expose] public section

/-!
# The minimal-generation record, closure half: `S₂` equals the closure space

Work item W2 (`C8/ROADMAP.md`, `Lattice/Benchmark.md` §5): the 524 relations of the record
that create no basis vector (`S2Close*.lean`), together with the 120 that do (`S2Rel*.lean`),
show that the span `S2span` of the 120 echelon vectors

* contains `ω`, `u`, `T c = c_(-2)𝟏` and `c_(-1) d` for all currents `c, d` (the 44 initial
  vectors of the record, `s2src_mem_0` … `s2src_mem_43`);
* is stable under `E_L(0), F_L(0), E_R(0), F_R(0)` and `u_(1)` (`s2op_mem`: the 600 operator
  relations), hence under all current zero modes: `H_L(0) = [E_L(0), F_L(0)]`,
  `H_R(0) = [E_R(0), F_R(0)]` by the commutator formula of the lattice VOA (this step uses
  `FLMInput`).

So `S2span` satisfies the closure conditions (`S2Closed_S2span`) and, with `S2span_le`
(`S2Link.lean`), **`S₂ = closureSpace u`** (`S2span_eq_closureSpace`): the record's claim that
the 120-dimensional `S₂` is exactly the closure of the generators, as a theorem about
`latticeVOA hF`.  Manuscript: certificate `cert:initial` and the minimal-generation record
(`hi_cft_20260923_c8_minimal_generators.json`, lines 2022–2055 of the expanded draft).

No hypotheses beyond `FLMInput`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

/-! ## Operators on the basis -/

theorem mode_mem_of (c d : Vec) (hc : ∀ p ∈ c, Valid p.1) (hd : ∀ p ∈ d, Valid p.1) (m : ℤ)
    (h : toV4 (Vec4.mode (Vec4.ofVec c) m (Vec4.ofVec d)) ∈ S2span) :
    modeC m (toV c) (toV d) ∈ S2span := by
  rwa [toV4_mode _ _ _ (ofVec_allStates hc) (ofVec_allStates hd), toV4_ofVec, toV4_ofVec] at h

/-- `op_o` on all of `S₂`, for the four zero-mode operators and `u_(1)`. -/
theorem s2op_span (o : ℕ) (ho : o ≤ 4) (hu : (s2op o).AllStates Valid) :
    ∀ w ∈ S2span, modeC (s2opIdx o) (toV4 (s2op o)) w ∈ S2span := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have h := s2op_mem _ (s2basis_getD_mem k) o ho
    rwa [toV4_mode _ _ _ hu (s2vec_allValid k)] at h
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact S2span.add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact S2span.smul_mem c hy


theorem eL_mem : ∀ w ∈ S2span, modeC 0 (toV eL) w ∈ S2span := fun w hw => by
  have h := s2op_span 0 (by norm_num) (ofVec_allStates eL_valid) w hw
  rwa [show s2op 0 = Vec4.ofVec eL from rfl, toV4_ofVec, show s2opIdx 0 = 0 from rfl] at h

theorem fL_mem : ∀ w ∈ S2span, modeC 0 (toV fL) w ∈ S2span := fun w hw => by
  have h := s2op_span 1 (by norm_num) (ofVec_allStates fL_valid) w hw
  rwa [show s2op 1 = Vec4.ofVec fL from rfl, toV4_ofVec, show s2opIdx 1 = 0 from rfl] at h

theorem eR_mem : ∀ w ∈ S2span, modeC 0 (toV eR) w ∈ S2span := fun w hw => by
  have h := s2op_span 2 (by norm_num) (ofVec_allStates eR_valid) w hw
  rwa [show s2op 2 = Vec4.ofVec eR from rfl, toV4_ofVec, show s2opIdx 2 = 0 from rfl] at h

theorem fR_mem : ∀ w ∈ S2span, modeC 0 (toV fR) w ∈ S2span := fun w hw => by
  have h := s2op_span 3 (by norm_num) (ofVec_allStates fR_valid) w hw
  rwa [show s2op 3 = Vec4.ofVec fR from rfl, toV4_ofVec, show s2opIdx 3 = 0 from rfl] at h

theorem u_one_mem : ∀ w ∈ S2span, modeC 1 uV w ∈ S2span :=
  s2op_span 4 le_rfl s2u_valid

/-! ## The Cartan zero modes, by the commutator formula -/

theorem cartan_mem (hF : FLMInput) {e f h : Vec} (he : ∀ p ∈ e, Valid p.1 ∧ grade p.1 = 1)
    (hf : ∀ p ∈ f, Valid p.1 ∧ grade p.1 = 1) (hef : mode e 0 f = h)
    (heS : ∀ w ∈ S2span, modeC 0 (toV e) w ∈ S2span)
    (hfS : ∀ w ∈ S2span, modeC 0 (toV f) w ∈ S2span) :
    ∀ w ∈ S2span, modeC 0 (toV h) w ∈ S2span := by
  intro w hw
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
  exact S2span.sub_mem (heS _ (hfS _ hw)) (hfS _ (heS _ hw))

theorem hL_mem (hF : FLMInput) : ∀ w ∈ S2span, modeC 0 (toV hL) w ∈ S2span :=
  cartan_mem hF (e := eL) (f := fL) (h := hL) (currents_basisStates 1) (currents_basisStates 2)
    left_sl2.2.2.1 eL_mem fL_mem

theorem hR_mem (hF : FLMInput) : ∀ w ∈ S2span, modeC 0 (toV hR) w ∈ S2span :=
  cartan_mem hF (e := eR) (f := fR) (h := hR) (currents_basisStates 4) (currents_basisStates 5)
    right_sl2.2.2.1 eR_mem fR_mem

/-! ## The closure conditions -/

theorem T_mem : ∀ x ∈ Kspan, modeC (-2) x vacV ∈ S2span := by
  intro x hx
  refine modeC_mem_of_span (-2) (t := {vacV}) ?_ x hx vacV (Submodule.subset_span rfl)
  rintro y hy z rfl
  rw [← toV_vac]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [mode_mem_of hL vac hL_valid vac_valid (-2) s2src_mem_0, mode_mem_of eL vac eL_valid vac_valid (-2) s2src_mem_1, mode_mem_of fL vac fL_valid vac_valid (-2) s2src_mem_2, mode_mem_of hR vac hR_valid vac_valid (-2) s2src_mem_3, mode_mem_of eR vac eR_valid vac_valid (-2) s2src_mem_4, mode_mem_of fR vac fR_valid vac_valid (-2) s2src_mem_5]

theorem prod_mem : ∀ x ∈ Kspan, ∀ y ∈ Kspan, modeC (-1) x y ∈ S2span := by
  refine modeC_mem_of_span (-1) ?_
  rintro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [mode_mem_of hL hL hL_valid hL_valid (-1) s2src_mem_6,
    mode_mem_of hL eL hL_valid eL_valid (-1) s2src_mem_7,
    mode_mem_of hL fL hL_valid fL_valid (-1) s2src_mem_8,
    mode_mem_of hL hR hL_valid hR_valid (-1) s2src_mem_9,
    mode_mem_of hL eR hL_valid eR_valid (-1) s2src_mem_10,
    mode_mem_of hL fR hL_valid fR_valid (-1) s2src_mem_11,
    mode_mem_of eL hL eL_valid hL_valid (-1) s2src_mem_12,
    mode_mem_of eL eL eL_valid eL_valid (-1) s2src_mem_13,
    mode_mem_of eL fL eL_valid fL_valid (-1) s2src_mem_14,
    mode_mem_of eL hR eL_valid hR_valid (-1) s2src_mem_15,
    mode_mem_of eL eR eL_valid eR_valid (-1) s2src_mem_16,
    mode_mem_of eL fR eL_valid fR_valid (-1) s2src_mem_17,
    mode_mem_of fL hL fL_valid hL_valid (-1) s2src_mem_18,
    mode_mem_of fL eL fL_valid eL_valid (-1) s2src_mem_19,
    mode_mem_of fL fL fL_valid fL_valid (-1) s2src_mem_20,
    mode_mem_of fL hR fL_valid hR_valid (-1) s2src_mem_21,
    mode_mem_of fL eR fL_valid eR_valid (-1) s2src_mem_22,
    mode_mem_of fL fR fL_valid fR_valid (-1) s2src_mem_23,
    mode_mem_of hR hL hR_valid hL_valid (-1) s2src_mem_24,
    mode_mem_of hR eL hR_valid eL_valid (-1) s2src_mem_25,
    mode_mem_of hR fL hR_valid fL_valid (-1) s2src_mem_26,
    mode_mem_of hR hR hR_valid hR_valid (-1) s2src_mem_27,
    mode_mem_of hR eR hR_valid eR_valid (-1) s2src_mem_28,
    mode_mem_of hR fR hR_valid fR_valid (-1) s2src_mem_29,
    mode_mem_of eR hL eR_valid hL_valid (-1) s2src_mem_30,
    mode_mem_of eR eL eR_valid eL_valid (-1) s2src_mem_31,
    mode_mem_of eR fL eR_valid fL_valid (-1) s2src_mem_32,
    mode_mem_of eR hR eR_valid hR_valid (-1) s2src_mem_33,
    mode_mem_of eR eR eR_valid eR_valid (-1) s2src_mem_34,
    mode_mem_of eR fR eR_valid fR_valid (-1) s2src_mem_35,
    mode_mem_of fR hL fR_valid hL_valid (-1) s2src_mem_36,
    mode_mem_of fR eL fR_valid eL_valid (-1) s2src_mem_37,
    mode_mem_of fR fL fR_valid fL_valid (-1) s2src_mem_38,
    mode_mem_of fR hR fR_valid hR_valid (-1) s2src_mem_39,
    mode_mem_of fR eR fR_valid eR_valid (-1) s2src_mem_40,
    mode_mem_of fR fR fR_valid fR_valid (-1) s2src_mem_41]

theorem zero_mode_mem (hF : FLMInput) : ∀ x ∈ Kspan, ∀ w ∈ S2span, modeC 0 x w ∈ S2span := by
  intro x hx w hw
  refine modeC_mem_of_span 0 (t := (S2span : Set V)) ?_ x hx w (by rwa [Submodule.span_eq])
  rintro y hy z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hL_mem hF z hz, eL_mem z hz, fL_mem z hz, hR_mem hF z hz, eR_mem z hz, fR_mem z hz]

/-- **`S₂` satisfies the closure conditions.** -/
theorem S2Closed_S2span (hF : FLMInput) : S2Closed S2span :=
  ⟨omegaV_mem_S2span, uV_mem_S2span, T_mem, prod_mem, zero_mode_mem hF, u_one_mem⟩

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3) (qp q0 qm : V)
  (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4)

/-- **The minimal-generation record, both halves**: `S₂` is exactly the closure of `ω`, `u`,
`T K`, `K₋₁K` under the current zero modes and `u_(1)`. -/
theorem S2span_eq_closureSpace :
    (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ = (latticeD hF S₃ hS₃ qp q0 qm hq).closureSpace uV := by
  refine le_antisymm (S2span_le_closureSpace hF S₃ hS₃ qp q0 qm hq) ?_
  unfold ClosureData.closureSpace
  exact sInf_le (S2Closed_S2span hF)

end


#print axioms S2Closed_S2span
#print axioms S2span_eq_closureSpace

end LatticeVOA
end HaagerupIzumi.C8
