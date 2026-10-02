module

public import HaagerupIzumi.C8.Lattice.QA
public import HaagerupIzumi.C8.Lattice.Roots
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The Fock model of `B = V_{E₆ ⊕ A₂}` over `ℂ`: the space, its modes and its grading

Work item W2, option (c) (`C8/ROADMAP.md`).  This file builds, from the computable modes of
`Lattice/Modes.lean`, the concrete vector space and the bilinear modes that the vertex-algebra
interface of `VertexAlgebra/Borcherds.lean` needs.

* `ValidState`: the canonical Fock monomials `(β, osc)` with nondecreasing code list `osc`;
  `canon` sorts a code list (`sortCodes`, insertion of `insertCode`), which does not change the
  monomial (the oscillators commute) nor its grade (`grade_canon`).
* `V = ValidState →₀ ℂ`: the Fock space `S(ĥ⁻) ⊗ ℂ[L]` with its monomial basis.
* `push : Fock →+ V` (coefficients `ℚ → ℂ`, states `canon`), `toV = push ∘ toFock` for rational
  sparse vectors and `toV4` for vectors over `ℚ(√13, √-3)` (`Lattice/QA.lean`), with
  `s ↦ √13`, `t ↦ √3 i`.
* `modeC m : V →ₗ[ℂ] V →ₗ[ℂ] V`: the bilinear extension of `basisMode` to `V`
  (`modeC_single`).  The kernel computations are linked to it by `toV_mode` (rational
  vectors) and `toV4_mode` (vectors over `ℚ(√13, √-3)`): for vectors whose states are canonical,
  the list computation `mode a m b` represents `modeC m (toV a) (toV b)`.
* `gradeC d`: the span of the canonical monomials of grade `d`; it is a direct-sum
  decomposition of `V` (`gradeC_internal`) of CFT type (`gradeC_zero : gradeC 0 = ℂ ∙ 𝟏`).

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## Canonical monomials -/

theorem mem_insertCode {x k : ℕ} : ∀ {l : List ℕ}, x ∈ insertCode k l ↔ x = k ∨ x ∈ l
  | [] => by simp [insertCode]
  | j :: js => by
    unfold insertCode
    split_ifs
    · simp
    · simp only [List.mem_cons, mem_insertCode]
      tauto

theorem oscGrade_insertCode (k : ℕ) : ∀ l, oscGrade (insertCode k l) = (k / 8 + 1) + oscGrade l
  | [] => by simp [insertCode, oscGrade]
  | j :: js => by
    unfold insertCode
    split_ifs
    · simp [oscGrade]
    · simp only [oscGrade, oscGrade_insertCode k js]
      omega

theorem insertCode_pairwise {k : ℕ} :
    ∀ {l : List ℕ}, l.Pairwise (· ≤ ·) → (insertCode k l).Pairwise (· ≤ ·)
  | [], _ => by simp [insertCode]
  | j :: js, h => by
    rw [List.pairwise_cons] at h
    unfold insertCode
    split_ifs with hkj
    · rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.2 h⟩
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hkj
      · exact le_trans hkj (h.1 x hx)
    · rw [List.pairwise_cons]
      refine ⟨?_, insertCode_pairwise h.2⟩
      intro x hx
      rw [mem_insertCode] at hx
      rcases hx with rfl | hx
      · omega
      · exact h.1 x hx

theorem insertCode_of_le {k : ℕ} : ∀ {l : List ℕ}, (∀ x ∈ l, k ≤ x) → insertCode k l = k :: l
  | [], _ => rfl
  | j :: js, h => by
    unfold insertCode
    rw [if_pos (h j List.mem_cons_self)]

/-- Sorting a code list by insertion (the monomial is unchanged: oscillators commute). -/
def sortCodes (l : List ℕ) : List ℕ := l.foldr insertCode []

theorem sortCodes_cons (k : ℕ) (l : List ℕ) : sortCodes (k :: l) = insertCode k (sortCodes l) :=
  rfl

theorem sortCodes_pairwise : ∀ l : List ℕ, (sortCodes l).Pairwise (· ≤ ·)
  | [] => List.Pairwise.nil
  | k :: l => by
    rw [sortCodes_cons]
    exact insertCode_pairwise (sortCodes_pairwise l)

theorem oscGrade_sortCodes : ∀ l, oscGrade (sortCodes l) = oscGrade l
  | [] => rfl
  | k :: l => by
    rw [sortCodes_cons, oscGrade_insertCode, oscGrade_sortCodes l]
    rfl

theorem sortCodes_of_pairwise : ∀ {l : List ℕ}, l.Pairwise (· ≤ ·) → sortCodes l = l
  | [], _ => rfl
  | k :: l, h => by
    rw [List.pairwise_cons] at h
    rw [sortCodes_cons, sortCodes_of_pairwise h.2, insertCode_of_le h.1]

/-- A canonical Fock monomial (nondecreasing code list). -/
abbrev ValidState := {s : State // Valid s}

/-- The canonical form of a monomial. -/
def canon (s : State) : ValidState := ⟨(s.1, sortCodes s.2), sortCodes_pairwise s.2⟩

theorem canon_of_valid {s : State} (h : Valid s) : canon s = ⟨s, h⟩ := by
  apply Subtype.ext
  show (s.1, sortCodes s.2) = s
  rw [sortCodes_of_pairwise h]

theorem grade_canon (s : State) : grade (canon s).1 = grade s := by
  simp only [canon, grade, oscGrade_sortCodes]

/-- The vacuum monomial. -/
def vacValid : ValidState := ⟨vacState, List.Pairwise.nil⟩

/-! ## The Fock space over `ℂ` -/

/-- The Fock space `S(ĥ⁻) ⊗ ℂ[L]` of `V_L`, with the canonical monomials as basis. -/
abbrev V := ValidState →₀ ℂ

/-- The vacuum `𝟏`. -/
noncomputable def vacV : V := Finsupp.single vacValid 1

/-- From the rational model (states with any code order) to `V`. -/
noncomputable def push : Fock →+ V :=
  (Finsupp.mapDomain.addMonoidHom canon).comp
    (Finsupp.mapRange.addMonoidHom (Rat.castHom ℂ).toAddMonoidHom)

theorem push_single (s : State) (q : ℚ) :
    push (Finsupp.single s q) = Finsupp.single (canon s) (q : ℂ) := by
  simp [push, Finsupp.mapRange_single, Finsupp.mapDomain_single]

theorem push_smul (q : ℚ) (f : Fock) : push (q • f) = (q : ℂ) • push f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, smul_add]
  | single s c =>
    rw [Finsupp.smul_single, push_single, push_single, Finsupp.smul_single, smul_eq_mul,
      smul_eq_mul, Rat.cast_mul]

/-- The vector of `V` represented by a rational sparse list. -/
noncomputable def toV (v : Vec) : V := push (toFock v)

@[simp] theorem toV_nil : toV [] = 0 := by
  simp [toV]

theorem toV_cons_mk (s : State) (c : ℚ) (v : Vec) :
    toV ((s, c) :: v) = Finsupp.single (canon s) (c : ℂ) + toV v := by
  unfold toV
  rw [toFock_cons_mk, map_add, push_single]

theorem toV_addVec (a b : Vec) : toV (addVec a b) = toV a + toV b := by
  unfold toV
  rw [toFock_addVec, map_add]

theorem toV_smul (q : ℚ) (v : Vec) : toV (smul q v) = (q : ℂ) • toV v := by
  unfold toV
  rw [toFock_smul, push_smul]

/-- The vector of `V` represented by a sparse vector over `ℚ(√13, √-3)`. -/
noncomputable def toV4 (x : Vec4) : V :=
  toV x.c0 + sC • toV x.c1 + tC • toV x.c2 + (sC * tC) • toV x.c3

/-! ## Modes -/

/-- `u_(m)` on `V`, for a canonical monomial `u`. -/
noncomputable def opC (u : ValidState) (m : ℤ) : V →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun v : ValidState => toV (basisMode u.1 m v.1)

/-- The modes `a_(m) b` of the Fock model, bilinear over `ℂ`. -/
noncomputable def modeC (m : ℤ) : V →ₗ[ℂ] V →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun u : ValidState => opC u m

theorem modeC_single (m : ℤ) (u v : ValidState) (c d : ℂ) :
    modeC m (Finsupp.single u c) (Finsupp.single v d) = (c * d) • toV (basisMode u.1 m v.1) := by
  rw [modeC, Finsupp.linearCombination_single, LinearMap.smul_apply, opC,
    Finsupp.linearCombination_single, smul_smul]

theorem toV_bindVec_cons (t : State) (c : ℚ) (v : Vec) (f : State → Vec) :
    toV (bindVec ((t, c) :: v) f) = (c : ℂ) • toV (f t) + toV (bindVec v f) := by
  unfold toV
  rw [toFock_bindVec_cons, map_add, push_smul]

theorem toV_mode_cons (s : State) (c : ℚ) (a b : Vec) (m : ℤ) :
    toV (mode ((s, c) :: a) m b) =
      (c : ℂ) • toV (bindVec b fun v => basisMode s m v) + toV (mode a m b) := by
  unfold mode
  exact toV_bindVec_cons s c a _

theorem toV_bindVec_basisMode (s : State) (hs : Valid s) (m : ℤ) :
    ∀ b : Vec, (∀ p ∈ b, Valid p.1) →
      toV (bindVec b fun v => basisMode s m v) = opC ⟨s, hs⟩ m (toV b)
  | [], _ => by simp [bindVec, mergeAll]
  | (t, c) :: b, hb => by
    have ht : Valid t := hb (t, c) List.mem_cons_self
    have hb' : ∀ p ∈ b, Valid p.1 := fun p hp => hb p (List.mem_cons_of_mem _ hp)
    rw [toV_bindVec_cons, toV_bindVec_basisMode s hs m b hb', toV_cons_mk,
      canon_of_valid ht, map_add]
    congr 1
    rw [opC, Finsupp.linearCombination_single]

/-- **Link for rational vectors**: for vectors of canonical monomials, the list computation
`mode a m b` represents `modeC m (toV a) (toV b)`. -/
theorem toV_mode (m : ℤ) :
    ∀ a b : Vec, (∀ p ∈ a, Valid p.1) → (∀ p ∈ b, Valid p.1) →
      toV (mode a m b) = modeC m (toV a) (toV b)
  | [], b, _, _ => by simp [mode, bindVec, mergeAll]
  | (s, c) :: a, b, ha, hb => by
    have hs : Valid s := ha (s, c) List.mem_cons_self
    have ha' : ∀ p ∈ a, Valid p.1 := fun p hp => ha p (List.mem_cons_of_mem _ hp)
    rw [toV_mode_cons, toV_bindVec_basisMode s hs m b hb,
      toV_mode m a b ha' hb, toV_cons_mk, canon_of_valid hs, map_add, LinearMap.add_apply]
    congr 1
    rw [modeC, Finsupp.linearCombination_single, LinearMap.smul_apply]

theorem sC_mul_tC_mul_self : sC * tC * (sC * tC) = -39 := by
  linear_combination (tC * tC) * sC_mul_self + 13 * tC_mul_self

theorem sC_mul_sC_mul_tC : sC * (sC * tC) = 13 * tC := by
  linear_combination tC * sC_mul_self

theorem sC_mul_tC_mul_sC : sC * tC * sC = 13 * tC := by
  linear_combination tC * sC_mul_self

theorem tC_mul_sC_mul_tC : tC * (sC * tC) = -3 * sC := by
  linear_combination sC * tC_mul_self

theorem sC_mul_tC_mul_tC : sC * tC * tC = -3 * sC := by
  linear_combination sC * tC_mul_self

theorem tC_mul_sC : tC * sC = sC * tC := mul_comm _ _

/-- **Link for vectors over `ℚ(√13, √-3)`**: `Vec4.mode` represents `modeC`. -/
theorem toV4_mode (m : ℤ) (x y : Vec4) (hx : x.AllStates Valid) (hy : y.AllStates Valid) :
    toV4 (Vec4.mode x m y) = modeC m (toV4 x) (toV4 y) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
  simp only [toV4, Vec4.mode, toV_addVec, toV_smul,
    toV_mode m _ _ hx0 hy0, toV_mode m _ _ hx0 hy1, toV_mode m _ _ hx0 hy2, toV_mode m _ _ hx0 hy3,
    toV_mode m _ _ hx1 hy0, toV_mode m _ _ hx1 hy1, toV_mode m _ _ hx1 hy2, toV_mode m _ _ hx1 hy3,
    toV_mode m _ _ hx2 hy0, toV_mode m _ _ hx2 hy1, toV_mode m _ _ hx2 hy2, toV_mode m _ _ hx2 hy3,
    toV_mode m _ _ hx3 hy0, toV_mode m _ _ hx3 hy1, toV_mode m _ _ hx3 hy2, toV_mode m _ _ hx3 hy3,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  push_cast
  linear_combination (norm := module)
    (-1 : ℂ) • sC_mul_self • modeC m (toV x.c1) (toV y.c1) +
    (-1 : ℂ) • tC_mul_self • modeC m (toV x.c2) (toV y.c2) +
    (-(tC * tC)) • sC_mul_self • modeC m (toV x.c3) (toV y.c3) +
    (-13 : ℂ) • tC_mul_self • modeC m (toV x.c3) (toV y.c3) +
    (-tC) • sC_mul_self • modeC m (toV x.c1) (toV y.c3) +
    (-tC) • sC_mul_self • modeC m (toV x.c3) (toV y.c1) +
    (-sC) • tC_mul_self • modeC m (toV x.c2) (toV y.c3) +
    (-sC) • tC_mul_self • modeC m (toV x.c3) (toV y.c2)

/-! ## The grading -/

/-- The canonical monomials of grade `d`. -/
def gradeSetC (d : ℕ) : Set ValidState := {s | grade s.1 = d}

/-- The grade-`d` subspace `V_d`. -/
noncomputable def gradeC (d : ℕ) : Submodule ℂ V := Finsupp.supported ℂ ℂ (gradeSetC d)

theorem gradeC_internal : DirectSum.IsInternal gradeC := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro d
    refine Disjoint.mono_right (iSup₂_le fun j hj => Finsupp.supported_mono (M := ℂ) (R := ℂ)
      (show gradeSetC j ⊆ {s : ValidState | grade s.1 ≠ d} from fun s hs => by
        simp only [gradeSetC, Set.mem_ofPred_eq] at hs ⊢
        rw [hs]
        exact hj)) ?_
    apply Finsupp.disjoint_supported_supported
    rw [Set.disjoint_left]
    intro s hs hs'
    exact hs' hs
  · show ⨆ d, Finsupp.supported ℂ ℂ (gradeSetC d) = ⊤
    rw [← Finsupp.supported_iUnion]
    have h : (⋃ d, gradeSetC d) = Set.univ :=
      Set.eq_univ_of_forall fun s => Set.mem_iUnion.2 ⟨grade s.1, rfl⟩
    rw [h, Finsupp.supported_univ]

theorem gradeSetC_zero : gradeSetC 0 = {vacValid} := by
  ext s
  simp only [gradeSetC, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hg
    apply Subtype.ext
    obtain ⟨⟨β, osc⟩, h⟩ := s
    obtain ⟨q, hq⟩ := Mom.norm_even β
    have hn := Mom.norm_nonneg β
    simp only [grade] at hg
    rw [hq] at hg
    have hosc : oscGrade osc = 0 := by omega
    have hosc' : osc = [] := by
      cases osc with
      | nil => rfl
      | cons k ks =>
        simp only [oscGrade] at hosc
        omega
    have hβ : β = Mom.zero := Mom.eq_zero_of_norm_eq_zero (by omega)
    subst hosc' hβ
    rfl
  · rintro rfl
    decide

/-- CFT type: `V₀ = ℂ 𝟏`. -/
theorem gradeC_zero : gradeC 0 = ℂ ∙ vacV := by
  rw [gradeC, gradeSetC_zero, Finsupp.supported_eq_span_single, Set.image_singleton]
  rfl

theorem single_mem_gradeC {s : ValidState} {d : ℕ} (h : grade s.1 = d) (c : ℂ) :
    Finsupp.single s c ∈ gradeC d :=
  Finsupp.single_mem_supported ℂ c h

#print axioms toV_mode
#print axioms toV4_mode
#print axioms gradeC_internal
#print axioms gradeC_zero

end LatticeVOA
end HaagerupIzumi.C8
