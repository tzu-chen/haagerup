module

public import HaagerupIzumi.C8.Lattice.VOA
public import HaagerupIzumi.C8.Lattice.S2Data
public import HaagerupIzumi.C8.MinimalGeneration

@[expose] public section

/-!
# The minimal-generation certificate in the Fock model: semantic part

Work item W2 (`C8/ROADMAP.md`): the lemmas that turn the kernel-checked relations of the
minimal-generator record (`S2Rel*.lean`, `S2Pivots.lean`) into statements about the lattice VOA
of `Lattice/VOA.lean` (assembled in `S2MinGen.lean`).

* `toV4_add`, `toV4_smulQA`, `toV4_combo`: the vectors over `ℚ(√13, √-3)` (`Vec4`) are
  additive, and `Vec4.smulQA z` is multiplication by `z.toC` (with `√13² = 13`, `(√3 i)² = -3`).
* `S2Closed W`: the closure conditions of `ClosureData.closureSpace` (`MinimalGeneration.lean`)
  for the lattice closure data and `u`; `mem_closureSpace_of` reduces membership in the closure
  space to these conditions.
* `mem_of_new`: a relation `source = s r + ∑ cᵢ rᵢ` with `s` invertible (kernel-checked inverse)
  puts `r` in every closed `W` that contains the source and the `rᵢ`.
* `src_*`: the sources of the record (`c_(-2)𝟏`, `c_(-1)d`, `ω`, `u`, `E_L(0) r`, `F_L(0) r`,
  `E_R(0) r`, `F_R(0) r`, `u(1) r`) lie in every closed `W` (given `r ∈ W`).
* `linearIndependent_of_triangular`: a family is independent if functionals `φⱼ` vanish on
  `vₖ` for `j < k` and not on `vⱼ` (the echelon form of the record, evaluated at the pivots).

No hypotheses beyond `FLMInput` (only needed to have the algebra).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

/-! ## Vectors over `ℚ(√13, √-3)` -/

theorem toV4_ofVec (v : Vec) : toV4 (Vec4.ofVec v) = toV v := by
  simp [toV4, Vec4.ofVec]

theorem toV4_zero : toV4 Vec4.zero = 0 := by
  simp [toV4, Vec4.zero]

theorem toV4_add (x y : Vec4) : toV4 (Vec4.add x y) = toV4 x + toV4 y := by
  simp only [toV4, Vec4.add, toV_addVec]
  module

theorem toV_comb (p q r w : ℚ) (v0 v1 v2 v3 : Vec) :
    toV (Vec4.comb p q r w v0 v1 v2 v3) =
      (p : ℂ) • toV v0 + (q : ℂ) • toV v1 + (r : ℂ) • toV v2 + (w : ℂ) • toV v3 := by
  simp only [Vec4.comb, toV_addVec, toV_smul]
  abel

theorem toV4_smulQA (z : QA) (x : Vec4) : toV4 (Vec4.smulQA z x) = z.toC • toV4 x := by
  simp only [toV4, Vec4.smulQA, toV_comb, QA.toC]
  push_cast
  linear_combination (norm := module)
    (-((z.b : ℂ) + (z.d : ℂ) * tC)) • sC_mul_self • toV x.c1 +
    (-((z.c : ℂ) + (z.d : ℂ) * sC)) • tC_mul_self • toV x.c2 +
    (-((z.b : ℂ) * tC + (z.d : ℂ) * (tC * tC))) • sC_mul_self • toV x.c3 +
    (-((z.c : ℂ) * sC + 13 * (z.d : ℂ))) • tC_mul_self • toV x.c3

theorem toV4_combo (l : List (QA × Vec4)) :
    toV4 (combo l) = (l.map fun p => p.1.toC • toV4 p.2).sum := by
  induction l with
  | nil => simp [combo, toV4_zero]
  | cons p l ih => simp [combo, toV4_add, toV4_smulQA, ih]

theorem toV4_combo_mem {W : Submodule ℂ V} :
    ∀ l : List (QA × Vec4), (∀ p ∈ l, toV4 p.2 ∈ W) → toV4 (combo l) ∈ W
  | [], _ => by simp [combo, toV4_zero]
  | p :: l, h => by
    rw [combo, toV4_add, toV4_smulQA]
    exact W.add_mem (W.smul_mem _ (h p List.mem_cons_self))
      (toV4_combo_mem l fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- A relation `src = s r + ∑ cᵢ rᵢ` puts `src` in `W` when `r` and the `rᵢ` are. -/
theorem src_mem_of_rel {W : Submodule ℂ V} {src r : Vec4} {s : QA} {cs : List (QA × Vec4)}
    (h : src = Vec4.add (Vec4.smulQA s r) (combo cs)) (hr : toV4 r ∈ W)
    (hcs : ∀ p ∈ cs, toV4 p.2 ∈ W) : toV4 src ∈ W := by
  rw [h, toV4_add, toV4_smulQA]
  exact W.add_mem (W.smul_mem _ hr) (toV4_combo_mem cs hcs)

/-- **A new basis vector of the record lies in `W`**: `src = s r + ∑ cᵢ rᵢ`, `s` invertible. -/
theorem mem_of_new {W : Submodule ℂ V} {src r : Vec4} {s : QA} {cs : List (QA × Vec4)}
    (h : src = Vec4.add (Vec4.smulQA s r) (combo cs)) (hs : QA.mul s (QA.inv s) = QA.one)
    (hsrc : toV4 src ∈ W) (hcs : ∀ p ∈ cs, toV4 p.2 ∈ W) : toV4 r ∈ W := by
  have e : toV4 src = s.toC • toV4 r + toV4 (combo cs) := by
    rw [h, toV4_add, toV4_smulQA]
  have hne := QA.toC_ne_zero_of_mul_eq_one hs
  have hr : toV4 r = (s.toC)⁻¹ • (toV4 src - toV4 (combo cs)) := by
    rw [e, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hr]
  exact W.smul_mem _ (W.sub_mem hsrc (toV4_combo_mem cs hcs))

/-! ## The closure conditions -/

/-- The field `u` in `V`. -/
noncomputable def uV : V := toV4 s2u

/-- The current space `K` of the lattice closure data. -/
noncomputable def Kspan : Submodule ℂ V :=
  Submodule.span ℂ {toV hL, toV eL, toV fL, toV hR, toV eR, toV fR}

/-- The closure conditions of `ClosureData.closureSpace` for the lattice closure data and `u`. -/
def S2Closed (W : Submodule ℂ V) : Prop :=
  omegaV ∈ W ∧ uV ∈ W ∧ (∀ x ∈ Kspan, modeC (-2) x vacV ∈ W) ∧
    (∀ x ∈ Kspan, ∀ y ∈ Kspan, modeC (-1) x y ∈ W) ∧ (∀ x ∈ Kspan, ∀ w ∈ W, modeC 0 x w ∈ W) ∧
    (∀ w ∈ W, modeC 1 uV w ∈ W)

theorem mem_closureSpace_of (hF : FLMInput) (S₂ S₃ : Submodule ℂ V) (hS₂ : S₂ ≤ gradeC 2)
    (hS₃ : S₃ ≤ gradeC 3) (qp q0 qm : V) (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4)
    {x : V} (hx : ∀ W, S2Closed W → x ∈ W) :
    x ∈ (latticeClosureData hF S₂ S₃ hS₂ hS₃ qp q0 qm hq).closureSpace uV :=
  Submodule.mem_sInf.2 fun W hW => hx W hW

theorem current_mem_Kspan {c : Vec} (hc : c = hL ∨ c = eL ∨ c = fL ∨ c = hR ∨ c = eR ∨ c = fR) :
    toV c ∈ Kspan := by
  apply Submodule.subset_span
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem Vec4.AllStates.mono {P Q : State → Prop} {x : Vec4} (h : x.AllStates P)
    (hPQ : ∀ s, P s → Q s) : x.AllStates Q :=
  ⟨fun p hp => hPQ _ (h.1 p hp), fun p hp => hPQ _ (h.2.1 p hp), fun p hp => hPQ _ (h.2.2.1 p hp),
    fun p hp => hPQ _ (h.2.2.2 p hp)⟩

theorem ofVec_allStates {v : Vec} (h : ∀ p ∈ v, Valid p.1) : (Vec4.ofVec v).AllStates Valid :=
  ⟨h, by simp [Vec4.ofVec], by simp [Vec4.ofVec], by simp [Vec4.ofVec]⟩

theorem vac_valid : ∀ p ∈ vac, Valid p.1 := by
  decide +kernel

theorem toV_vac : toV vac = vacV := by
  simp [vac, toV_cons_mk, canon_of_valid (show Valid vacState from List.Pairwise.nil), vacV,
    vacValid]

theorem current_valid {c : Vec} (hc : c = hL ∨ c = eL ∨ c = fL ∨ c = hR ∨ c = eR ∨ c = fR) :
    ∀ p ∈ c, Valid p.1 := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hL_valid, eL_valid, fL_valid, hR_valid, eR_valid, fR_valid]

theorem src_T {W : Submodule ℂ V} (hW : S2Closed W) {c : Vec}
    (hc : c = hL ∨ c = eL ∨ c = fL ∨ c = hR ∨ c = eR ∨ c = fR) :
    toV4 (Vec4.mode (Vec4.ofVec c) (-2) (Vec4.ofVec vac)) ∈ W := by
  rw [toV4_mode _ _ _ (ofVec_allStates (current_valid hc)) (ofVec_allStates vac_valid),
    toV4_ofVec, toV4_ofVec, toV_vac]
  exact hW.2.2.1 _ (current_mem_Kspan hc)

theorem src_mm {W : Submodule ℂ V} (hW : S2Closed W) {c d : Vec}
    (hc : c = hL ∨ c = eL ∨ c = fL ∨ c = hR ∨ c = eR ∨ c = fR)
    (hd : d = hL ∨ d = eL ∨ d = fL ∨ d = hR ∨ d = eR ∨ d = fR) :
    toV4 (Vec4.mode (Vec4.ofVec c) (-1) (Vec4.ofVec d)) ∈ W := by
  rw [toV4_mode _ _ _ (ofVec_allStates (current_valid hc)) (ofVec_allStates (current_valid hd)),
    toV4_ofVec, toV4_ofVec]
  exact hW.2.2.2.1 _ (current_mem_Kspan hc) _ (current_mem_Kspan hd)

theorem src_omega {W : Submodule ℂ V} (hW : S2Closed W) : toV4 (Vec4.ofVec omega) ∈ W := by
  rw [toV4_ofVec]
  exact hW.1

theorem src_u {W : Submodule ℂ V} (hW : S2Closed W) : toV4 s2u ∈ W := hW.2.1

theorem src_current_op {W : Submodule ℂ V} (hW : S2Closed W) {c : Vec}
    (hc : c = hL ∨ c = eL ∨ c = fL ∨ c = hR ∨ c = eR ∨ c = fR) {r : Vec4}
    (hrv : r.AllStates Valid) (hr : toV4 r ∈ W) : toV4 (Vec4.mode (Vec4.ofVec c) 0 r) ∈ W := by
  rw [toV4_mode _ _ _ (ofVec_allStates (current_valid hc)) hrv, toV4_ofVec]
  exact hW.2.2.2.2.1 _ (current_mem_Kspan hc) _ hr

theorem src_u_op {W : Submodule ℂ V} (hW : S2Closed W) (hu : s2u.AllStates Valid) {r : Vec4}
    (hrv : r.AllStates Valid) (hr : toV4 r ∈ W) : toV4 (Vec4.mode s2u 1 r) ∈ W := by
  rw [toV4_mode _ _ _ hu hrv]
  exact hW.2.2.2.2.2 _ hr

/-- The source `op_o(r)` of an operator relation lies in every closed `W` containing `r`. -/
theorem src_op {W : Submodule ℂ V} (hW : S2Closed W) (hu : s2u.AllStates Valid) (o : ℕ)
    (ho : o ≤ 4) {r : Vec4} (hrv : r.AllStates Valid) (hr : toV4 r ∈ W) :
    toV4 (Vec4.mode (s2op o) (s2opIdx o) r) ∈ W := by
  rcases o with _ | _ | _ | _ | _ | o
  · exact src_current_op hW (Or.inr (Or.inl rfl)) hrv hr
  · exact src_current_op hW (Or.inr (Or.inr (Or.inl rfl))) hrv hr
  · exact src_current_op hW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hrv hr
  · exact src_current_op hW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hrv hr
  · exact src_u_op hW hu hrv hr
  · omega

/-! ## Evaluation at a state and triangular independence -/

theorem toV4_apply (x : Vec4) (hx : x.AllStates Valid) (s : ValidState) :
    toV4 x s = (Vec4.coeff x s.1).toC := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  simp only [toV4, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, toV_apply_of_valid _ h0,
    toV_apply_of_valid _ h1, toV_apply_of_valid _ h2, toV_apply_of_valid _ h3, Vec4.coeff,
    QA.toC]
  ring

theorem linearIndependent_of_triangular {n : ℕ} (v : Fin n → V) (φ : Fin n → (V →ₗ[ℂ] ℂ))
    (hdiag : ∀ k, φ k (v k) ≠ 0) (hlow : ∀ j k, j < k → φ j (v k) = 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ m : ℕ, ∀ i : Fin n, i.val = m → g i = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      have h := congrArg (φ i) hg
      rw [map_sum, map_zero] at h
      simp only [map_smul, smul_eq_mul] at h
      rw [Finset.sum_eq_single i] at h
      · exact (mul_eq_zero.1 h).resolve_right (hdiag i)
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with hlt | hgt
        · rw [ih k.val (by rw [← hi]; exact hlt) k rfl, zero_mul]
        · rw [hlow i k hgt, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ i) h'
  intro i
  exact key i.val i rfl

#print axioms toV4_smulQA
#print axioms mem_of_new
#print axioms src_op
#print axioms linearIndependent_of_triangular

end LatticeVOA
end HaagerupIzumi.C8
