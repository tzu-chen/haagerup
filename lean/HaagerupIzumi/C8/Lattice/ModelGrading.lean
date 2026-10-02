module

public import HaagerupIzumi.C8.Lattice.Model

@[expose] public section

/-!
# The modes of the Fock model respect the grading

Work item W2, option (c) (`C8/ROADMAP.md`).  The fields `mode_grade` and `mode_trunc` of
`BorcherdsVertexAlgebra` for the Fock model are *proved* here from the definition of the modes
(`Lattice/Modes.lean`), not assumed:

* `toFock_basisModeAux_mem`: every term of `u_(m) v` (any states `u`, `v`) has grade
  `wt u + wt v - m - 1`.  The proof follows the definitions: Heisenberg modes shift the grade
  by `-m` (`toFock_heis_mem`; annihilation `annih_grade`, creation `oscGrade_insertCode`),
  the vertex operator `(e^α)_(m)` lands in grade `(α,α)/2 + wt v - m - 1`
  (`toFock_vertexOp_mem`; contractions `contract_grade`, Schur polynomials `monos_grade`,
  `(α+β, α+β) = (α,α) + 2(α,β) + (β,β)`), and the iterate recursion preserves the target.
* `modeC_mem_gradeC` (`mode_grade`) and `modeC_eq_zero_of_le` (`mode_trunc`): the same for the
  bilinear modes on `V`, via `push` (which preserves grades, `push_mem_gradeC`) and
  bilinearity (`modeC_mem_of_span`).

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## Grades as integers -/

theorem grade_eq (s : State) : (grade s : ℤ) = s.1.norm / 2 + oscGrade s.2 := by
  have := Mom.norm_nonneg s.1
  simp only [grade]
  omega

theorem Mom.norm_add (a b : Mom) : (Mom.add a b).norm = a.norm + 2 * Mom.form a b + b.norm := by
  simp only [Mom.norm, Mom.form, Mom.add]
  ring

theorem oscGrade_mergeOsc (a : List ℕ) : ∀ b : List ℕ, oscGrade (mergeOsc a b) = oscGrade a + oscGrade b
  | [] => rfl
  | k :: b => by
    show oscGrade (insertCode k (mergeOsc a b)) = _
    rw [oscGrade_insertCode, oscGrade_mergeOsc a b]
    simp only [oscGrade]
    omega

/-! ## Graded pieces of the rational model -/

/-- Rational vectors whose states all have grade `e` (any code order). -/
noncomputable def GrQ (e : ℤ) : Submodule ℚ Fock :=
  Finsupp.supported ℚ ℚ {s : State | (grade s : ℤ) = e}

theorem single_mem_GrQ {s : State} {e : ℤ} (h : (grade s : ℤ) = e) (c : ℚ) :
    Finsupp.single s c ∈ GrQ e :=
  Finsupp.single_mem_supported ℚ c h

theorem mem_GrQ_of_eq {f : Fock} {e e' : ℤ} (h : f ∈ GrQ e) (he : e = e') : f ∈ GrQ e' :=
  he ▸ h

theorem GrQ_neg {e : ℤ} (he : e < 0) : GrQ e = ⊥ := by
  have h : {s : State | (grade s : ℤ) = e} = ∅ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    omega
  rw [GrQ, h, Finsupp.supported_empty]

theorem toFock_mem_GrQ_of_forall {e : ℤ} :
    ∀ v : Vec, (∀ p ∈ v, (grade p.1 : ℤ) = e) → toFock v ∈ GrQ e
  | [], _ => by simp
  | (s, c) :: v, h => by
    rw [toFock_cons_mk]
    exact add_mem (single_mem_GrQ (h (s, c) List.mem_cons_self) c)
      (toFock_mem_GrQ_of_forall v fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem toFock_addVec_mem {W : Submodule ℚ Fock} {a b : Vec} (ha : toFock a ∈ W)
    (hb : toFock b ∈ W) : toFock (addVec a b) ∈ W := by
  rw [toFock_addVec]
  exact add_mem ha hb

theorem toFock_smul_mem {W : Submodule ℚ Fock} {q : ℚ} {v : Vec} (hv : toFock v ∈ W) :
    toFock (smul q v) ∈ W := by
  rw [toFock_smul]
  exact W.smul_mem q hv

theorem toFock_bindVec_mem {W : Submodule ℚ Fock} {S : Set State} {w : Vec} {f : State → Vec}
    (hw : toFock w ∈ Finsupp.supported ℚ ℚ S) (hf : ∀ s ∈ S, toFock (f s) ∈ W) :
    toFock (bindVec w f) ∈ W := by
  rw [toFock_bindVec]
  have h := (Finsupp.mem_span_image_iff_linearCombination (R := ℚ)
    (v := fun s => toFock (f s)) (s := S)).2 ⟨_, hw, rfl⟩
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨s, hs, rfl⟩
  exact hf s hs

theorem toFock_foldr_mem {W : Submodule ℚ Fock} {β : Type*} (f : β → Vec → Vec) :
    ∀ l : List β, (∀ j ∈ l, ∀ acc, toFock acc ∈ W → toFock (f j acc) ∈ W) →
      toFock (l.foldr f []) ∈ W
  | [], _ => by simp
  | j :: l, h => by
    rw [List.foldr_cons]
    exact h j List.mem_cons_self _
      (toFock_foldr_mem f l fun i hi => h i (List.mem_cons_of_mem _ hi))

/-! ## Heisenberg modes -/

theorem annih_grade (i n : ℕ) :
    ∀ (osc : List ℕ), ∀ q ∈ annih i n osc, oscGrade q.1 + n = oscGrade osc
  | [] => by simp [annih]
  | k :: ks => by
    intro q hq
    simp only [annih] at hq
    by_cases hk : k / 8 + 1 = n
    · rw [if_pos hk, List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp only [oscGrade]
        omega
      · rw [List.mem_map] at hq
        obtain ⟨q', hq', rfl⟩ := hq
        have := annih_grade i n ks q' hq'
        simp only [oscGrade]
        omega
    · rw [if_neg hk, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := annih_grade i n ks q' hq'
      simp only [oscGrade]
      omega

theorem toFock_heis_mem (i : ℕ) (hi : i < 8) (m : ℤ) (s : State) :
    toFock (heis i m s) ∈ GrQ ((grade s : ℤ) - m) := by
  unfold heis
  split_ifs with h0 hneg
  · subst h0
    rw [toFock_addTerm, toFock_nil, add_zero]
    exact single_mem_GrQ (by simp) _
  · apply toFock_mem_GrQ_of_forall
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    rw [grade_eq, grade_eq s]
    simp only [oscGrade_insertCode]
    omega
  · rw [toFock_normalize]
    apply toFock_mem_GrQ_of_forall
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := annih_grade i m.toNat s.2 q hq
    rw [grade_eq, grade_eq s]
    simp only
    omega

/-! ## Vertex operators -/

theorem contract_grade (α : Mom) :
    ∀ (osc : List ℕ), ∀ t ∈ contract α osc, oscGrade t.1 + t.2.2 = oscGrade osc
  | [] => by simp [contract, oscGrade]
  | k :: ks => by
    intro t ht
    simp only [contract] at ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · rw [List.mem_map] at ht
      obtain ⟨t', ht', rfl⟩ := ht
      have := contract_grade α ks t' ht'
      simp only [oscGrade]
      omega
    · split_ifs at ht with ha
      · simp at ht
      · rw [List.mem_map] at ht
        obtain ⟨t', ht', rfl⟩ := ht
        have := contract_grade α ks t' ht'
        simp only [oscGrade]
        omega

theorem monos_grade : ∀ (fuel rem : ℕ) (cs : List ℕ), ∀ l ∈ monos fuel rem cs, oscGrade l = rem
  | _, 0, _ => by
    intro l hl
    simp only [monos, List.mem_singleton] at hl
    subst hl
    rfl
  | 0, _ + 1, _ => by
    intro l hl
    simp [monos] at hl
  | fuel + 1, rem + 1, cs => by
    intro l hl
    simp only [monos, List.mem_flatMap] at hl
    obtain ⟨suf, -, hl⟩ := hl
    cases suf with
    | nil => simp at hl
    | cons k ks =>
      simp only at hl
      split_ifs at hl with hk
      · rw [List.mem_map] at hl
        obtain ⟨l', hl', rfl⟩ := hl
        have := monos_grade fuel _ _ l' hl'
        simp only [oscGrade]
        omega
      · simp at hl

theorem schur_mem {α : Mom} {g : ℕ} {p : State × ℚ} (hp : p ∈ schur α g) :
    p.1.1 = Mom.zero ∧ oscGrade p.1.2 = g := by
  unfold schur at hp
  rw [List.mem_map] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  exact ⟨rfl, monos_grade g g _ l hl⟩

theorem toFock_vertexOp_mem (α : Mom) (m : ℤ) (s : State) :
    toFock (vertexOp α m s) ∈ GrQ (α.norm / 2 + (grade s : ℤ) - m - 1) := by
  unfold vertexOp
  dsimp only
  apply toFock_foldr_mem
  intro t ht acc hacc
  try dsimp only
  split_ifs with hdeg
  · exact hacc
  · apply toFock_addVec_mem _ hacc
    apply toFock_smul_mem
    apply toFock_mem_GrQ_of_forall
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hq2 := (schur_mem hq).2
    have hc := contract_grade α s.2 t ht
    obtain ⟨qa, hqa⟩ := Mom.norm_even α
    obtain ⟨qb, hqb⟩ := Mom.norm_even s.1
    rw [grade_eq, grade_eq s]
    simp only [oscGrade_mergeOsc, Mom.norm_add]
    rw [hqa, hqb]
    omega

/-! ## The iterate recursion -/

theorem toFock_basisModeAux_mem (α : Mom) : ∀ (osc : List ℕ) (m : ℤ) (v : State),
    toFock (basisModeAux α osc m v) ∈
      GrQ (α.norm / 2 + (oscGrade osc : ℤ) + (grade v : ℤ) - m - 1)
  | [], m, v => by
    simp only [basisModeAux]
    refine mem_GrQ_of_eq (toFock_vertexOp_mem α m v) ?_
    simp [oscGrade]
  | k :: ks, m, v => by
    simp only [basisModeAux]
    have hk8 : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    apply toFock_addVec_mem
    · apply toFock_foldr_mem
      intro j _ acc hacc
      try dsimp only
      apply toFock_addVec_mem _ hacc
      apply toFock_smul_mem
      refine toFock_bindVec_mem (toFock_basisModeAux_mem α ks _ v) ?_
      intro s hs
      have hs' : (grade s : ℤ) = _ := hs
      refine mem_GrQ_of_eq (toFock_heis_mem (k % 8) hk8 _ s) ?_
      rw [hs']
      simp only [oscGrade]
      omega
    · apply toFock_foldr_mem
      intro j _ acc hacc
      try dsimp only
      apply toFock_addVec_mem _ hacc
      apply toFock_smul_mem
      refine toFock_bindVec_mem (toFock_heis_mem (k % 8) hk8 _ v) ?_
      intro s hs
      have hs' : (grade s : ℤ) = _ := hs
      refine mem_GrQ_of_eq (toFock_basisModeAux_mem α ks _ s) ?_
      rw [hs']
      simp only [oscGrade]
      omega

theorem toFock_basisMode_mem (u : State) (m : ℤ) (v : State) :
    toFock (basisMode u m v) ∈ GrQ ((grade u : ℤ) + grade v - m - 1) := by
  refine mem_GrQ_of_eq (toFock_basisModeAux_mem u.1 u.2 m v) ?_
  rw [grade_eq u]

/-! ## The modes on `V` -/

theorem push_mem_gradeC {e : ℤ} {f : Fock} (hf : f ∈ GrQ e) : push f ∈ gradeC e.toNat := by
  rw [GrQ, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨s, hs, rfl⟩ := h
    rw [push_single]
    apply single_mem_gradeC
    rw [grade_canon]
    have hs' : (grade s : ℤ) = e := hs
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [push_smul]
    exact Submodule.smul_mem _ _ hx

theorem modeC_single_mem (m : ℤ) (u v : ValidState) (c d : ℂ) :
    modeC m (Finsupp.single u c) (Finsupp.single v d) ∈
      gradeC ((grade u.1 : ℤ) + grade v.1 - m - 1).toNat := by
  rw [modeC_single]
  exact Submodule.smul_mem _ _ (push_mem_gradeC (toFock_basisMode_mem u.1 m v.1))

theorem modeC_single_eq_zero (m : ℤ) (u v : ValidState) (c d : ℂ)
    (h : (grade u.1 : ℤ) + grade v.1 ≤ m) :
    modeC m (Finsupp.single u c) (Finsupp.single v d) = 0 := by
  rw [modeC_single]
  have h0 := toFock_basisMode_mem u.1 m v.1
  rw [GrQ_neg (by omega), Submodule.mem_bot] at h0
  rw [toV, h0, map_zero, smul_zero]

/-- Bilinear extension from spanning sets. -/
theorem modeC_mem_of_span (m : ℤ) {s t : Set V} {Z : Submodule ℂ V}
    (h : ∀ x ∈ s, ∀ y ∈ t, modeC m x y ∈ Z) :
    ∀ x ∈ Submodule.span ℂ s, ∀ y ∈ Submodule.span ℂ t, modeC m x y ∈ Z := by
  intro x hx y hy
  have h1 : ∀ x ∈ s, Submodule.span ℂ t ≤ Z.comap (modeC m x) := fun x hx' =>
    Submodule.span_le.mpr fun y hy' => h x hx' y hy'
  have h2 : Submodule.span ℂ s ≤ Z.comap ((modeC m).flip y) :=
    Submodule.span_le.mpr fun x hx' => h1 x hx' hy
  exact h2 hx

theorem gradeC_eq_span (d : ℕ) :
    gradeC d = Submodule.span ℂ ((fun s => Finsupp.single s (1 : ℂ)) '' gradeSetC d) :=
  Finsupp.supported_eq_span_single ℂ _

/-- **`mode_grade`** for the Fock model. -/
theorem modeC_mem_gradeC {i j : ℕ} {a b : V} (n : ℤ) (ha : a ∈ gradeC i) (hb : b ∈ gradeC j)
    (_hn : n + 1 ≤ (i : ℤ) + j) : modeC n a b ∈ gradeC ((i : ℤ) + j - n - 1).toNat := by
  rw [gradeC_eq_span] at ha hb
  refine modeC_mem_of_span n ?_ a ha b hb
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  have hu' : grade u.1 = i := hu
  have hv' : grade v.1 = j := hv
  have := modeC_single_mem n u v 1 1
  rwa [hu', hv'] at this

/-- **`mode_trunc`** for the Fock model. -/
theorem modeC_eq_zero_of_le {i j : ℕ} {a b : V} (n : ℤ) (ha : a ∈ gradeC i) (hb : b ∈ gradeC j)
    (hn : (i : ℤ) + j ≤ n) : modeC n a b = 0 := by
  rw [gradeC_eq_span] at ha hb
  have key : ∀ x ∈ (fun s => Finsupp.single s (1 : ℂ)) '' gradeSetC i,
      ∀ y ∈ (fun s => Finsupp.single s (1 : ℂ)) '' gradeSetC j,
        modeC n x y ∈ (⊥ : Submodule ℂ V) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hu' : grade u.1 = i := hu
    have hv' : grade v.1 = j := hv
    rw [Submodule.mem_bot]
    exact modeC_single_eq_zero n u v 1 1 (by rw [hu', hv']; exact hn)
  exact (Submodule.mem_bot ℂ).1 (modeC_mem_of_span n key a ha b hb)

#print axioms toFock_basisModeAux_mem
#print axioms modeC_mem_gradeC
#print axioms modeC_eq_zero_of_le

end LatticeVOA
end HaagerupIzumi.C8
