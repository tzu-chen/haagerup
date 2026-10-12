module

public import HaagerupIzumi.C8.Lattice.ModelGrading
public import HaagerupIzumi.C8.Lattice.PCTLink

@[expose] public section

/-!
# `θ_g` is compatible with all modes of the Fock model (`PCTModeCompatible`)

Main theorem `pctModeCompatible : PCTModeCompatible` (`Lattice/PCTLink.lean`): the transported
PCT involution `θ_g` (manuscript `eq:pct`, `c8_expanded_20260929/haagerup_c8_expanded.tex`
lines 1975–1989) satisfies `θ_g (a_(m) b) = (θ_g a)_(m) (θ_g b)` for all `m : ℤ`, `a b : V`,
i.e. it is an antilinear automorphism of the lattice vertex algebra.  Unconditional (no
`FLMBorcherds`/`FLMInput` needed): it is proved directly on the computable modes.

* `thetaF : Fock →ₗ[ℚ] Fock`: the rational part of `θ_g`,
  `(β, osc) ↦ (-1)^{|osc|} ∏ c̃ᵢ^{βᵢ} (−β, osc)`; `pctV ∘ push = push ∘ thetaF`
  (`pctV_push`; `pctV` is `thetaF` followed by complex conjugation of the coefficients).
* `PCTBasisCompat`: the coefficient identity on basis monomials,
  `thetaF (u_(m) v) = c(u) c(v) (θu)_(m) (θv)`, and
  `pctModeCompatible_of_basis : PCTBasisCompat → PCTModeCompatible` (sesquilinearity: `modeC`
  is `ℂ`-bilinear with rational structure constants, `pctV` is conjugate-linear).
* `pctBasisCompat`: proved by induction along the definition of `basisModeAux`:
  - Heisenberg modes (`thetaF_heis`): `θ hᵢ(m) = −hᵢ(m) θ` (`hᵢ(0)` changes sign with the
    momentum, creation/annihilation change the oscillator number by one);
  - vertex operators (`thetaF_vertexOp`): `θ (e^α)_(m) = c̃^α (e^{−α})_(m) θ`, from
    `ε(−α,−β) = ε(α,β)` (`Mom.eps_neg_neg`, the cocycle is bilinear), `(−α,−β) = (α,β)`,
    the contraction factors `−(α_k, α)` changing sign (`contract_neg`), the Schur coefficients
    `S_g(−α) = (−1)^{|osc|} S_g(α)` (`schur_neg`, `coeffAux_neg`) and the multiplicativity of
    the gauge `∏ c̃ᵢ^{βᵢ}` (`pctGauge_add`);
  - the iterate recursion (`thetaF_basisModeAux`), whose binomial coefficients and summation
    ranges are unchanged (`Mom.norm_neg`, `grade_pctState`).

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## Lengths of code lists -/

theorem length_insertCode (k : ℕ) : ∀ l : List ℕ, (insertCode k l).length = l.length + 1
  | [] => rfl
  | j :: js => by
    unfold insertCode
    split_ifs
    · simp
    · simp [length_insertCode k js]

theorem length_sortCodes : ∀ l : List ℕ, (sortCodes l).length = l.length
  | [] => rfl
  | k :: l => by
    rw [sortCodes_cons, length_insertCode, length_sortCodes l]
    rfl

theorem length_mergeOsc (a : List ℕ) : ∀ b : List ℕ, (mergeOsc a b).length = a.length + b.length
  | [] => rfl
  | k :: b => by
    show (insertCode k (mergeOsc a b)).length = _
    rw [length_insertCode, length_mergeOsc a b, List.length_cons]
    omega

/-! ## Signs and the gauge -/

theorem pctSign_eq (l : List ℕ) : pctSign l = if l.length % 2 = 0 then 1 else -1 := rfl

theorem pctSign_insertCode (k : ℕ) (l : List ℕ) : pctSign (insertCode k l) = -pctSign l := by
  rw [pctSign_eq, pctSign_eq, length_insertCode]
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | norm_num

theorem pctSign_mergeOsc (a b : List ℕ) : pctSign (mergeOsc a b) = pctSign a * pctSign b := by
  rw [pctSign_eq, pctSign_eq, pctSign_eq, length_mergeOsc]
  split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> first | (exfalso; omega) | norm_num

theorem pctSign_sortCodes (l : List ℕ) : pctSign (sortCodes l) = pctSign l := by
  rw [pctSign_eq, pctSign_eq, length_sortCodes]

theorem zp_eq_zpow (c : ℚ) : ∀ n : ℤ, zp c n = c ^ n
  | .ofNat n => by simp [zp]
  | .negSucc n => by simp [zp, zpow_negSucc]

theorem zp_add (c : ℚ) (hc : c ≠ 0) (a b : ℤ) : zp c (a + b) = zp c a * zp c b := by
  rw [zp_eq_zpow, zp_eq_zpow, zp_eq_zpow, zpow_add₀ hc]

theorem pctGauge_add (a b : Mom) : pctGauge (Mom.add a b) = pctGauge a * pctGauge b := by
  simp only [pctGauge, Mom.add]
  rw [zp_add 5 (by norm_num), zp_add 8 (by norm_num), zp_add 9 (by norm_num),
    zp_add 8 (by norm_num), zp_add 5 (by norm_num), zp_add 1 (by norm_num),
    zp_add 2 (by norm_num), zp_add 2 (by norm_num)]
  ring

/-! ## Negation of momenta -/

theorem Mom.pairSimple_neg (a : Mom) : ∀ i, Mom.pairSimple i (Mom.neg a) = -Mom.pairSimple i a
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => by simp only [Mom.pairSimple, Mom.neg]; ring
  | _ + 8 => by simp [Mom.pairSimple]

theorem Mom.coord_neg (a : Mom) : ∀ i, (Mom.neg a).coord i = -a.coord i
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => by simp only [Mom.coord, Mom.neg]
  | _ + 8 => by simp [Mom.coord]

theorem Mom.form_neg_neg (a b : Mom) : Mom.form (Mom.neg a) (Mom.neg b) = Mom.form a b := by
  simp only [Mom.form, Mom.neg]
  ring

theorem Mom.norm_neg (a : Mom) : (Mom.neg a).norm = a.norm := Mom.form_neg_neg a a

theorem Mom.cocycleExp_neg_neg (a b : Mom) :
    Mom.cocycleExp (Mom.neg a) (Mom.neg b) = Mom.cocycleExp a b := by
  simp only [Mom.cocycleExp, Mom.neg]
  ring

theorem Mom.eps_neg_neg (a b : Mom) : Mom.eps (Mom.neg a) (Mom.neg b) = Mom.eps a b := by
  simp only [Mom.eps, Mom.cocycleExp_neg_neg]

theorem Mom.add_neg_neg (a b : Mom) : Mom.add (Mom.neg a) (Mom.neg b) = Mom.neg (Mom.add a b) := by
  simp only [Mom.add, Mom.neg, Mom.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem grade_pctState (s : State) : grade (pctState s) = grade s := by
  simp only [grade, pctState, Mom.norm_neg]

/-! ## The rational part of `θ_g` on the Fock model -/

/-- `θ_g` without the complex conjugation: `(β, osc) ↦ pctCoef (β, osc) · (−β, osc)`. -/
noncomputable def thetaF : Fock →ₗ[ℚ] Fock :=
  Finsupp.linearCombination ℚ fun s : State => Finsupp.single (pctState s) (pctCoef s)

theorem thetaF_single (s : State) (c : ℚ) :
    thetaF (Finsupp.single s c) = Finsupp.single (pctState s) (pctCoef s * c) := by
  rw [thetaF, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem pctCoef_canon (s : State) : pctCoef (canon s).1 = pctCoef s := by
  simp only [canon, pctCoef, pctSign_sortCodes]

theorem pctValid_canon (s : State) : pctValid (canon s) = canon (pctState s) := rfl

/-- `pctV ∘ push = push ∘ thetaF`. -/
theorem pctV_push (f : Fock) : pctV (push f) = push (thetaF f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single s c =>
    rw [push_single, pctV_single, thetaF_single, push_single, pctValid_canon, pctCoef_canon,
      map_ratCast, Rat.cast_mul, mul_comm]

theorem pctV_toV_any (w : Vec) : pctV (toV w) = push (thetaF (toFock w)) :=
  pctV_push _

/-- `thetaF` on a list all of whose states have the same factor `c`. -/
theorem thetaF_toFock_of (c : ℚ) :
    ∀ w : Vec, (∀ p ∈ w, pctCoef p.1 = c) →
      thetaF (toFock w) = c • toFock (w.map fun p => (pctState p.1, p.2))
  | [], _ => by simp
  | (s, d) :: w, hw => by
    have hs : pctCoef s = c := hw (s, d) List.mem_cons_self
    have ih := thetaF_toFock_of c w fun p hp => hw p (List.mem_cons_of_mem _ hp)
    rw [toFock_cons_mk, map_add, ih, thetaF_single, hs, List.map_cons, toFock_cons_mk, smul_add,
      Finsupp.smul_single, smul_eq_mul]

/-! ## Heisenberg modes -/

theorem annih_length (i n : ℕ) :
    ∀ (osc : List ℕ), ∀ q ∈ annih i n osc, q.1.length + 1 = osc.length
  | [] => by simp [annih]
  | k :: ks => by
    intro q hq
    simp only [annih] at hq
    by_cases hk : k / 8 + 1 = n
    · rw [if_pos hk, List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp
      · rw [List.mem_map] at hq
        obtain ⟨q', hq', rfl⟩ := hq
        have := annih_length i n ks q' hq'
        simp only [List.length_cons]
        omega
    · rw [if_neg hk, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := annih_length i n ks q' hq'
      simp only [List.length_cons]
      omega

theorem pctSign_of_length_succ {l l' : List ℕ} (h : l.length + 1 = l'.length) :
    pctSign l = -pctSign l' := by
  rw [pctSign_eq, pctSign_eq, ← h]
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | norm_num

/-- **`θ` and the Heisenberg modes**: `θ hᵢ(m) = −hᵢ(m) θ`. -/
theorem thetaF_heis (i : ℕ) (m : ℤ) (s : State) :
    thetaF (toFock (heis i m s)) = (-pctCoef s) • toFock (heis i m (pctState s)) := by
  unfold heis
  split_ifs with h0 hneg
  · rw [toFock_addTerm, toFock_addTerm, toFock_nil, add_zero, add_zero, thetaF_single,
      Finsupp.smul_single, smul_eq_mul]
    congr 1
    simp only [pctState, Mom.pairSimple_neg]
    push_cast
    ring
  · rw [thetaF_toFock_of (-pctCoef s)]
    · rfl
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      simp only [pctCoef]
      rw [pctSign_insertCode]
      ring
  · rw [toFock_normalize, toFock_normalize, thetaF_toFock_of (-pctCoef s), List.map_map]
    · rfl
    · intro p hp
      rw [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simp only [pctCoef]
      rw [pctSign_of_length_succ (annih_length i m.toNat s.2 q hq)]
      ring

/-! ## The coefficient identity on basis monomials, and the reduction -/

/-- `θ_g` on the modes of two basis monomials (rational coefficient identity). -/
def PCTBasisCompat : Prop :=
  ∀ (u : State) (m : ℤ) (v : State),
    thetaF (toFock (basisMode u m v)) =
      (pctCoef u * pctCoef v) • toFock (basisMode (pctState u) m (pctState v))

/-- **Reduction**: the coefficient identity on basis monomials implies `PCTModeCompatible`. -/
theorem pctModeCompatible_of_basis (h : PCTBasisCompat) : PCTModeCompatible := by
  intro m a b
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single u c =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, hb, hb']
    | single v d =>
      rw [modeC_single, pctV_smul, pctV_single, pctV_single, modeC_single, pctV_toV_any,
        h u.1 m v.1, push_smul]
      have e : toV (basisMode (pctValid u).1 m (pctValid v).1) =
          push (toFock (basisMode (pctState u.1) m (pctState v.1))) := rfl
      rw [e, smul_smul, map_mul]
      congr 1
      push_cast
      ring

/-! ## Integer signs, `thetaF` on lists -/

/-- `(-1)^{|l|}` as an integer. -/
def intSign (l : List ℕ) : ℤ := if l.length % 2 = 0 then 1 else -1

theorem intSign_cons (k : ℕ) (l : List ℕ) : intSign (k :: l) = -intSign l := by
  unfold intSign
  rw [List.length_cons]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem intSign_cast (l : List ℕ) : ((intSign l : ℤ) : ℚ) = pctSign l := by
  unfold intSign
  rw [pctSign_eq]
  split_ifs <;> norm_num

theorem pctSign_cons (k : ℕ) (l : List ℕ) : pctSign (k :: l) = -pctSign l := by
  rw [pctSign_eq, pctSign_eq, List.length_cons]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem pctSign_pm (l : List ℕ) : pctSign l = 1 ∨ pctSign l = -1 := by
  rw [pctSign_eq]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem pctCoef_cons (α : Mom) (k : ℕ) (ks : List ℕ) :
    pctCoef (α, k :: ks) = -pctCoef (α, ks) := by
  simp only [pctCoef]
  rw [pctSign_cons]
  ring

theorem pctCoef_nil (α : Mom) : pctCoef (α, []) = pctGauge α := by
  simp [pctCoef, pctSign]

theorem thetaF_toFock (w : Vec) : thetaF (toFock w) = toFock (pctVec w) := by
  induction w with
  | nil => simp [pctVec]
  | cons p w ih =>
    rw [toFock_cons, map_add, ih, thetaF_single]
    simp only [pctVec, List.map_cons]
    rw [toFock_cons]

theorem toFock_map_smul (c : ℚ) :
    ∀ w : Vec, toFock (w.map fun p => (p.1, c * p.2)) = c • toFock w
  | [] => by simp
  | p :: w => by
    rw [List.map_cons, toFock_cons, toFock_cons, toFock_map_smul c w, smul_add,
      Finsupp.smul_single, smul_eq_mul]

theorem thetaF_foldr_rel {β : Type*} (c : ℚ) (f g : β → Vec → Vec) :
    ∀ l : List β, (∀ t ∈ l, ∀ acc acc' : Vec, thetaF (toFock acc) = c • toFock acc' →
      thetaF (toFock (f t acc)) = c • toFock (g t acc')) →
      thetaF (toFock (l.foldr f [])) = c • toFock (l.foldr g [])
  | [], _ => by simp
  | t :: l, h => by
    rw [List.foldr_cons, List.foldr_cons]
    exact h t List.mem_cons_self _ _
      (thetaF_foldr_rel c f g l fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem thetaF_linearCombination (a : ℚ) (F G : State → Fock)
    (h : ∀ s, thetaF (F s) = (a * pctCoef s) • G (pctState s)) (x : Fock) :
    thetaF (Finsupp.linearCombination ℚ F x) = a • Finsupp.linearCombination ℚ G (thetaF x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | single s c =>
    rw [Finsupp.linearCombination_single, map_smul, h, thetaF_single,
      Finsupp.linearCombination_single, smul_smul, smul_smul]
    congr 1
    ring

theorem thetaF_bindVec_rel (a : ℚ) (f g : State → Vec)
    (hf : ∀ s, thetaF (toFock (f s)) = (a * pctCoef s) • toFock (g (pctState s)))
    (x y : Vec) (b : ℚ) (hxy : thetaF (toFock x) = b • toFock y) :
    thetaF (toFock (bindVec x f)) = (a * b) • toFock (bindVec y g) := by
  rw [toFock_bindVec, toFock_bindVec,
    thetaF_linearCombination a (fun s => toFock (f s)) (fun s => toFock (g s)) hf, hxy, map_smul,
    smul_smul]

/-! ## Contractions and Schur polynomials under `α ↦ -α` -/

theorem contract_neg (α : Mom) : ∀ l : List ℕ,
    contract (Mom.neg α) l =
      (contract α l).map fun p => (p.1, intSign l * intSign p.1 * p.2.1, p.2.2)
  | [] => by simp [contract, intSign]
  | k :: ks => by
    have ih := contract_neg α ks
    simp only [contract]
    rw [ih, Mom.pairSimple_neg, neg_neg]
    by_cases ha : Mom.pairSimple (k % 8) α = 0
    · have ha' : -Mom.pairSimple (k % 8) α = 0 := by rw [ha]; rfl
      rw [if_pos ha, if_pos ha']
      simp only [List.append_nil, List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_apply, intSign_cons]
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      ring
    · have ha' : ¬ -Mom.pairSimple (k % 8) α = 0 := by omega
      rw [if_neg ha, if_neg ha']
      simp only [List.map_append, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro p _
        simp only [Function.comp_apply, intSign_cons]
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        ring
      · apply List.map_congr_left
        intro p _
        simp only [Function.comp_apply, intSign_cons]
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        ring

theorem coeffAux_neg (α : Mom) : ∀ (prev mult : ℕ) (l : List ℕ),
    coeffAux (Mom.neg α) prev mult l =
      (intSign l * (coeffAux α prev mult l).1, (coeffAux α prev mult l).2)
  | _, _, [] => by simp [coeffAux, intSign]
  | prev, mult, k :: ks => by
    simp only [coeffAux]
    rw [coeffAux_neg α k _ ks, Mom.coord_neg, intSign_cons]
    refine Prod.ext ?_ rfl
    try dsimp only
    ring

theorem schur_neg (α : Mom) (g : ℕ) :
    schur (Mom.neg α) g = (schur α g).map fun q => (q.1, pctSign q.1.2 * q.2) := by
  have hf : ((List.range (8 * g)).filter fun k => (Mom.neg α).coord (k % 8) ≠ 0) =
      (List.range (8 * g)).filter fun k => α.coord (k % 8) ≠ 0 := by
    apply List.filter_congr
    intro k _
    simp [Mom.coord_neg]
  unfold schur
  rw [hf, List.map_map]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, coeffAux_neg]
  refine Prod.ext rfl ?_
  push_cast
  rw [intSign_cast]
  ring

/-! ## Vertex operators of `e^α` -/

/-- **`θ` and `Y(e^α, z)`**: `θ (e^α)_(m) = c̃^α (e^{-α})_(m) θ`. -/
theorem thetaF_vertexOp (α : Mom) (m : ℤ) (s : State) :
    thetaF (toFock (vertexOp α m s)) =
      (pctGauge α * pctCoef s) • toFock (vertexOp (Mom.neg α) m (pctState s)) := by
  unfold vertexOp
  simp only [pctState, contract_neg, List.foldr_map, Mom.add_neg_neg, Mom.eps_neg_neg,
    Mom.form_neg_neg]
  apply thetaF_foldr_rel
  intro t _ acc acc' hacc
  try dsimp only
  split_ifs with hd
  · exact hacc
  · rw [toFock_addVec, toFock_addVec, map_add, hacc, smul_add]
    congr 1
    rw [toFock_smul, toFock_smul, map_smul, thetaF_toFock, smul_smul, ← toFock_map_smul,
      ← toFock_map_smul, schur_neg]
    congr 1
    simp only [pctVec, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, pctState, pctCoef, pctSign_mergeOsc, pctGauge_add]
    refine Prod.ext rfl ?_
    push_cast
    rw [intSign_cast, intSign_cast]
    rcases pctSign_pm s.2 with h | h <;> rw [h] <;> ring

/-! ## The iterate recursion -/

theorem thetaF_bind_mode_heis (α : Mom) (ks : List ℕ)
    (IH : ∀ (M : ℤ) (s : State), thetaF (toFock (basisModeAux α ks M s)) =
      (pctCoef (α, ks) * pctCoef s) • toFock (basisModeAux (Mom.neg α) ks M (pctState s)))
    (M : ℤ) (v : State) (i : ℕ) (kk : ℤ) :
    thetaF (toFock (bindVec (basisModeAux α ks M v) (heis i kk))) =
      (-1 * (pctCoef (α, ks) * pctCoef v)) •
        toFock (bindVec (basisModeAux (Mom.neg α) ks M (pctState v)) (heis i kk)) :=
  thetaF_bindVec_rel (-1) (heis i kk) (heis i kk)
    (fun s => by rw [thetaF_heis, neg_one_mul]) _ _ _ (IH M v)

theorem thetaF_bind_heis_mode (α : Mom) (ks : List ℕ)
    (IH : ∀ (M : ℤ) (s : State), thetaF (toFock (basisModeAux α ks M s)) =
      (pctCoef (α, ks) * pctCoef s) • toFock (basisModeAux (Mom.neg α) ks M (pctState s)))
    (M : ℤ) (v : State) (i : ℕ) (j : ℤ) :
    thetaF (toFock (bindVec (heis i j v) (basisModeAux α ks M))) =
      (pctCoef (α, ks) * -pctCoef v) •
        toFock (bindVec (heis i j (pctState v)) (basisModeAux (Mom.neg α) ks M)) :=
  thetaF_bindVec_rel (pctCoef (α, ks)) (basisModeAux α ks M) (basisModeAux (Mom.neg α) ks M)
    (IH M) _ _ _ (thetaF_heis i j v)

/-- **`θ` on the modes of oscillator states** (induction on the code list). -/
theorem thetaF_basisModeAux (α : Mom) : ∀ (osc : List ℕ) (m : ℤ) (v : State),
    thetaF (toFock (basisModeAux α osc m v)) =
      (pctCoef (α, osc) * pctCoef v) • toFock (basisModeAux (Mom.neg α) osc m (pctState v))
  | [], m, v => by
    simp only [basisModeAux]
    rw [thetaF_vertexOp, pctCoef_nil]
  | k :: ks, m, v => by
    have IH : ∀ (M : ℤ) (s : State), thetaF (toFock (basisModeAux α ks M s)) =
        (pctCoef (α, ks) * pctCoef s) • toFock (basisModeAux (Mom.neg α) ks M (pctState s)) :=
      fun M s => thetaF_basisModeAux α ks M s
    have hc : pctCoef (α, k :: ks) = -pctCoef (α, ks) := pctCoef_cons α k ks
    simp only [basisModeAux, Mom.norm_neg, grade_pctState]
    rw [toFock_addVec, toFock_addVec, map_add, smul_add]
    congr 1
    · apply thetaF_foldr_rel
      intro j _ acc acc' hacc
      try dsimp only
      rw [toFock_addVec, toFock_addVec, map_add, hacc, toFock_smul, toFock_smul, map_smul,
        thetaF_bind_mode_heis α ks IH, hc]
      module
    · apply thetaF_foldr_rel
      intro j _ acc acc' hacc
      try dsimp only
      rw [toFock_addVec, toFock_addVec, map_add, hacc, toFock_smul, toFock_smul, map_smul,
        thetaF_bind_heis_mode α ks IH, hc]
      module

/-- **The coefficient identity on basis monomials.** -/
theorem pctBasisCompat : PCTBasisCompat := fun u m v => thetaF_basisModeAux u.1 u.2 m v

/-- **`θ_g` is compatible with all modes of the Fock model** (an antilinear automorphism of
the lattice vertex algebra, manuscript `eq:pct`). -/
theorem pctModeCompatible : PCTModeCompatible := pctModeCompatible_of_basis pctBasisCompat

#print axioms pctModeCompatible
#print axioms pctModeCompatible_of_basis
#print axioms thetaF_heis
#print axioms pctGauge_add

end LatticeVOA
end HaagerupIzumi.C8
