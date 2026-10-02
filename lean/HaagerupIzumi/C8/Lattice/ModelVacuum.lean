module

public import HaagerupIzumi.C8.Lattice.ModelGrading

@[expose] public section

/-!
# The vacuum axioms of the Fock model

Work item W2, option (c) (`C8/ROADMAP.md`).  The vacuum fields of `BorcherdsVertexAlgebra` for
the Fock model are *proved* from the definition of the modes (`Lattice/Modes.lean`):

* `modeC_vac` (`vac_mode`): `𝟏_(n) = δ_{n,-1}`.  The vertex operator of `e⁰` has no
  contractions (`contract_zero`) and the Schur polynomials of `0` vanish in positive degree
  (`schur_zero_pos`), so `(e⁰)_(n) v = δ_{n,-1} v` (`toFock_vertexOp_zero`).
* `modeC_vac_nonneg` (`mode_vac_nonneg`): `a_(n) 𝟏 = 0` for `n ≥ 0`, by induction on the
  oscillators of `a` (`toFock_basisModeAux_vac_nonneg`): the vertex operator has negative degree,
  the Heisenberg modes `hᵢ(k)`, `k ≥ 0`, kill `𝟏`, and the remaining terms carry the binomial
  coefficient `C(j, n-1) = 0`, `0 ≤ j < n - 1` (`gbinom_eq_zero`).
* `modeC_vac_neg_one` (`mode_vac_neg_one`): `a_(-1) 𝟏 = a`, by the same induction for sorted
  code lists (`toFock_basisModeAux_vac_neg_one`): only the term `j = n - 1` survives, with
  `C(n-1, n-1) = 1` (`gbinom_self`), and it re-inserts the first oscillator.

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## Facts about `0` -/

theorem Mom.pairSimple_zero (i : ℕ) : Mom.pairSimple i Mom.zero = 0 := by
  unfold Mom.pairSimple
  split <;> simp [Mom.zero]

theorem Mom.coord_zero (i : ℕ) : Mom.zero.coord i = 0 := by
  unfold Mom.coord
  split <;> rfl

theorem Mom.form_zero_left (b : Mom) : Mom.form Mom.zero b = 0 := by
  simp [Mom.form, Mom.zero]

theorem Mom.form_zero_right (a : Mom) : Mom.form a Mom.zero = 0 := by
  simp [Mom.form, Mom.zero]

theorem Mom.eps_zero_left (b : Mom) : Mom.eps Mom.zero b = 1 := by
  simp [Mom.eps, Mom.cocycleExp, Mom.zero]

theorem Mom.eps_zero_right (a : Mom) : Mom.eps a Mom.zero = 1 := by
  simp [Mom.eps, Mom.cocycleExp, Mom.zero]

theorem Mom.zero_add' (a : Mom) : Mom.add Mom.zero a = a := by
  cases a
  simp [Mom.add, Mom.zero]

theorem Mom.add_zero' (a : Mom) : Mom.add a Mom.zero = a := by
  cases a
  simp [Mom.add, Mom.zero]

theorem contract_zero : ∀ osc : List ℕ, contract Mom.zero osc = [(osc, 1, 0)]
  | [] => rfl
  | k :: ks => by
    simp [contract, Mom.pairSimple_zero, contract_zero ks]

theorem schur_zero (α : Mom) : schur α 0 = [((Mom.zero, []), 1)] := by
  simp [schur, monos, coeffAux]

theorem schur_zero_pos {g : ℕ} (hg : 0 < g) : schur Mom.zero g = [] := by
  have hf : (List.range (8 * g)).filter (fun k => Mom.zero.coord (k % 8) ≠ 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro k _
    simp [Mom.coord_zero]
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [schur, hf, monos, suffixes, List.flatMap_nil, List.map_nil]

/-! ## Binomial coefficients -/

theorem descProd_eq_zero {a : ℤ} (h0 : 0 ≤ a) : ∀ r : ℕ, a < r → descProd a r = 0
  | 0, h => by omega
  | r + 1, h => by
    rw [descProd]
    by_cases har : a = r
    · rw [har, sub_self, mul_zero]
    · rw [descProd_eq_zero h0 r (by omega), zero_mul]

theorem gbinom_eq_zero {a : ℤ} {r : ℕ} (h0 : 0 ≤ a) (h : a < r) : gbinom a r = 0 := by
  rw [gbinom, descProd_eq_zero h0 r h, Int.cast_zero, zero_div]

theorem descProd_cast_add (m : ℕ) :
    ∀ r : ℕ, descProd ((m + r : ℕ) : ℤ) r * (m.factorial : ℤ) = ((m + r).factorial : ℤ)
  | 0 => by simp [descProd]
  | r + 1 => by
    have ih := descProd_cast_add (m + 1) r
    have e : m + 1 + r = m + (r + 1) := by omega
    rw [e, Nat.factorial_succ] at ih
    rw [descProd, ← ih]
    push_cast
    ring

theorem descProd_self (r : ℕ) : descProd (r : ℤ) r = (r.factorial : ℤ) := by
  have h := descProd_cast_add 0 r
  simpa using h

theorem gbinom_self (r : ℕ) : gbinom (r : ℤ) r = 1 := by
  rw [gbinom, descProd_self]
  push_cast
  exact div_self (by exact_mod_cast r.factorial_ne_zero)

/-! ## Sums over the iterate recursion -/

theorem toFock_foldr_addVec {β : Type*} (T : β → Vec) :
    ∀ l : List β, toFock (l.foldr (fun j acc => addVec (T j) acc) []) =
      (l.map fun j => toFock (T j)).sum
  | [] => by simp
  | j :: l => by
    rw [List.foldr_cons, toFock_addVec, toFock_foldr_addVec T l, List.map_cons, List.sum_cons]

theorem gbinom_neg_neg (j : ℕ) (r : ℕ) : gbinom (-(-((j : ℤ) + 1)) - 1) r = gbinom (j : ℤ) r := by
  congr 1
  ring

theorem neg_one_sub_eq (m : ℕ) : (-1 : ℤ) - ((m + 1 : ℕ) : ℤ) - -((m : ℤ) + 1) = -1 := by
  push_cast
  ring

theorem list_sum_map_eq_single {β : Type*} [DecidableEq β] (g : β → Fock) (j₀ : β) :
    ∀ l : List β, l.Nodup → j₀ ∈ l → (∀ j ∈ l, j ≠ j₀ → g j = 0) → (l.map g).sum = g j₀
  | [], _, h, _ => absurd h List.not_mem_nil
  | j :: l, hnd, hj, hz => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    by_cases hjj : j = j₀
    · subst hjj
      have : (l.map g).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        rw [List.mem_map] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact hz i (List.mem_cons_of_mem _ hi) (fun e => hnd.1 (e ▸ hi))
      rw [this, add_zero]
    · rw [hz j List.mem_cons_self hjj, zero_add]
      refine list_sum_map_eq_single g j₀ l hnd.2 ?_ fun i hi => hz i (List.mem_cons_of_mem _ hi)
      rcases List.mem_cons.1 hj with h | h
      · exact absurd h.symm hjj
      · exact h

/-! ## The vertex operator of `e⁰` -/

theorem toFock_vertexOp_zero (n : ℤ) (s : State) :
    toFock (vertexOp Mom.zero n s) = if n = -1 then Finsupp.single s 1 else 0 := by
  obtain ⟨β, osc⟩ := s
  simp only [vertexOp, contract_zero, List.foldr_cons, List.foldr_nil, Mom.form_zero_left,
    Mom.eps_zero_left]
  by_cases hn : n = -1
  · subst hn
    rw [if_pos rfl]
    split_ifs with hc
    · simp at hc
    · simp [schur_zero, mergeOsc, Mom.zero_add', smul, addVec, mergeInto]
  · rw [if_neg hn]
    split_ifs with hc
    · simp
    · rw [schur_zero_pos ?_]
      · simp [smul, addVec]
      · omega

/-! ## Heisenberg modes on the vacuum -/

theorem toFock_heis_vac (i j : ℕ) : toFock (heis i (j : ℤ) vacState) = 0 := by
  unfold heis
  split_ifs with h0 hneg
  · rw [toFock_addTerm, toFock_nil, add_zero]
    simp [vacState, Mom.pairSimple_zero]
  · omega
  · simp [vacState, annih, normalize]

theorem toFock_smul_bot {c : ℚ} {v : Vec} (h : c = 0 ∨ toFock v = 0) :
    toFock (smul c v) ∈ (⊥ : Submodule ℚ Fock) := by
  rw [toFock_smul, Submodule.mem_bot]
  rcases h with h | h <;> simp [h]

theorem toFock_bindVec_of_zero {w : Vec} {f : State → Vec} (h : toFock w = 0) :
    toFock (bindVec w f) = 0 := by
  rw [toFock_bindVec, h, map_zero]

theorem grade_vacState : grade vacState = 0 := by
  decide +kernel

theorem toFock_foldr_heis_vac (c : ℕ → ℚ) (i : ℕ) (F : ℕ → State → Vec) (l : List ℕ) :
    toFock (l.foldr (fun j acc =>
      addVec (smul (c j) (bindVec (heis i (j : ℤ) vacState) (F j))) acc) []) = 0 := by
  rw [toFock_foldr_addVec]
  refine List.sum_eq_zero fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  rw [toFock_smul, toFock_bindVec_of_zero (toFock_heis_vac i j), smul_zero]

/-! ## `a_(n) 𝟏 = 0` for `n ≥ 0` -/

theorem toFock_basisModeAux_vac_nonneg (α : Mom) :
    ∀ (osc : List ℕ) (n : ℤ), 0 ≤ n → toFock (basisModeAux α osc n vacState) = 0
  | [], n, hn => by
    simp only [basisModeAux, vertexOp]
    rw [show contract α vacState.2 = [([], 1, 0)] from rfl, List.foldr_cons, List.foldr_nil,
      if_pos ?_]
    · simp
    · simp only [vacState, Mom.form_zero_right]
      omega
  | k :: ks, n, hn => by
    simp only [basisModeAux]
    suffices h : toFock _ ∈ (⊥ : Submodule ℚ Fock) from (Submodule.mem_bot ℚ).1 h
    apply toFock_addVec_mem
    · apply toFock_foldr_mem
      intro j _ acc hacc
      try dsimp only
      apply toFock_addVec_mem _ hacc
      apply toFock_smul_bot
      by_cases hj : 0 ≤ n - ((k / 8 + 1 : ℕ) : ℤ) - -((j : ℤ) + 1)
      · right
        exact toFock_bindVec_of_zero (toFock_basisModeAux_vac_nonneg α ks _ hj)
      · left
        rw [gbinom_neg_neg]
        exact gbinom_eq_zero (by omega) (by omega)
    · apply toFock_foldr_mem
      intro j _ acc hacc
      try dsimp only
      apply toFock_addVec_mem _ hacc
      apply toFock_smul_bot
      right
      exact toFock_bindVec_of_zero (toFock_heis_vac _ j)

/-! ## `a_(-1) 𝟏 = a` -/

theorem toFock_heis_create (k : ℕ) (β : Mom) (ks : List ℕ) (hks : ∀ x ∈ ks, k ≤ x) :
    toFock (heis (k % 8) (-((((k / 8 : ℕ) : ℤ)) + 1)) (β, ks)) = Finsupp.single (β, k :: ks) 1 := by
  unfold heis
  rw [if_neg (by omega), if_pos (by omega)]
  have hcode : k % 8 + 8 * ((-(-((((k / 8 : ℕ) : ℤ)) + 1))).toNat - 1) = k := by omega
  rw [hcode, insertCode_of_le hks]
  simp

theorem toFock_basisModeAux_vac_neg_one (α : Mom) :
    ∀ (osc : List ℕ), osc.Pairwise (· ≤ ·) →
      toFock (basisModeAux α osc (-1) vacState) = Finsupp.single (α, osc) 1
  | [], _ => by
    simp only [basisModeAux, vertexOp]
    rw [show contract α vacState.2 = [([], 1, 0)] from rfl, List.foldr_cons, List.foldr_nil,
      if_neg ?_]
    · simp [vacState, Mom.form_zero_right, Mom.eps_zero_right, schur_zero, mergeOsc,
        Mom.add_zero', smul, addVec, mergeInto]
    · simp [vacState, Mom.form_zero_right]
  | k :: ks, hsorted => by
    rw [List.pairwise_cons] at hsorted
    have ih := toFock_basisModeAux_vac_neg_one α ks hsorted.2
    simp only [basisModeAux]
    rw [toFock_addVec, toFock_foldr_heis_vac, add_zero, toFock_foldr_addVec]
    rw [list_sum_map_eq_single _ (k / 8) _ List.nodup_range ?_ ?_]
    · beta_reduce
      rw [toFock_smul, gbinom_neg_neg, Nat.add_sub_cancel, gbinom_self, one_smul,
        neg_one_sub_eq, toFock_bindVec, ih, Finsupp.linearCombination_single, one_smul]
      beta_reduce
      rw [toFock_heis_create k α ks hsorted.1]
    · rw [List.mem_range]
      have := Mom.norm_nonneg α
      simp only [oscGrade, grade_vacState]
      omega
    · intro j _ hj
      beta_reduce
      apply (Submodule.mem_bot ℚ).1
      apply toFock_smul_bot
      rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
      · left
        rw [gbinom_neg_neg]
        exact gbinom_eq_zero (by omega) (by omega)
      · right
        exact toFock_bindVec_of_zero
          (toFock_basisModeAux_vac_nonneg α ks _ (by push_cast; omega))

/-! ## The vacuum axioms on `V` -/

theorem modeC_vac_eq_opC (n : ℤ) : modeC n vacV = opC vacValid n := by
  rw [vacV, modeC, Finsupp.linearCombination_single, one_smul]

/-- **`vac_mode`**: `𝟏_(n) b = δ_{n,-1} b`. -/
theorem modeC_vac (n : ℤ) (b : V) : modeC n vacV b = if n = -1 then b else 0 := by
  rw [modeC_vac_eq_opC]
  have key : opC vacValid n = if n = -1 then LinearMap.id else 0 := by
    apply Finsupp.lhom_ext
    intro v d
    rw [opC, Finsupp.linearCombination_single]
    show d • toV (vertexOp Mom.zero n v.1) = _
    rw [toV, toFock_vertexOp_zero]
    split_ifs with hn
    · simp [push_single, canon_of_valid v.2]
    · simp
  rw [key]
  split_ifs <;> rfl

/-- **`mode_vac_nonneg`**: `a_(n) 𝟏 = 0` for `n ≥ 0`. -/
theorem modeC_vac_nonneg (n : ℤ) (a : V) (hn : 0 ≤ n) : modeC n a vacV = 0 := by
  have key : (modeC n).flip vacV = 0 := by
    apply Finsupp.lhom_ext
    intro u c
    rw [LinearMap.flip_apply, vacV, modeC_single, LinearMap.zero_apply]
    show (c * 1) • push (toFock (basisModeAux u.1.1 u.1.2 n vacState)) = 0
    rw [toFock_basisModeAux_vac_nonneg u.1.1 u.1.2 n hn, map_zero, smul_zero]
  have := LinearMap.congr_fun key a
  rwa [LinearMap.flip_apply] at this

/-- **`mode_vac_neg_one`**: `a_(-1) 𝟏 = a`. -/
theorem modeC_vac_neg_one (a : V) : modeC (-1) a vacV = a := by
  have key : (modeC (-1)).flip vacV = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro u c
    rw [LinearMap.flip_apply, vacV, modeC_single, LinearMap.id_apply]
    show (c * 1) • push (toFock (basisModeAux u.1.1 u.1.2 (-1) vacState)) = _
    rw [toFock_basisModeAux_vac_neg_one u.1.1 u.1.2 u.2, push_single]
    simp [canon_of_valid u.2]
  have := LinearMap.congr_fun key a
  rwa [LinearMap.flip_apply] at this

#print axioms modeC_vac
#print axioms modeC_vac_nonneg
#print axioms modeC_vac_neg_one

end LatticeVOA
end HaagerupIzumi.C8
