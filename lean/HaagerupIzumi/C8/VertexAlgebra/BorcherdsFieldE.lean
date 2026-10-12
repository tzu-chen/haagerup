module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsFieldDong
public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsAssocFace

@[expose] public section

/-!
# The `E`-level Borcherds defect for three fields: Pascal recursion and reduction

W3, item (1), route A (`Lattice/W3_PLAN.md`, section 2.2, steps 1 and 4).  For fields `A, B, C`
(`OpField`), pairwise local of order `N`, the `E`-level Borcherds defect at the mode `s` on `v` is

`eD(p, q, r) = ∑_t (p choose t) ((A_(r+t)B)_(p+q-t) C)_s v
   - ∑_t (-1)^t (r choose t) ((A_(p+r-t)(B_(q+t)C))_s v - (-1)^r (B_(q+r-t)(A_(p+t)C))_s v)`

with ranges adapted to the localities (`prod_eq_zero_of_local`).  Its plane `p = 0` is the field
iterate identity (`fieldIter`).  Proved here:

* `prod_eq_zero_left`, `prod_eq_zero_right`: products with a zero field vanish;
* `eD_pascal`: the Pascal recursion (step 1);
* `eD_eq_zero_of_face_plane` (step 4): `eD ≡ 0` from a locality face `r ≥ R₀` and one plane
  `p = P₀` (via `eq_zero_of_pascal_shift_face`), and `fieldIter_of_eD`: then the field iterate
  identity holds.

Steps 2 (the face) and 3 (the plane) are open; see `Lattice/W3_PLAN.md`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

namespace OpField

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem prod_eq_zero_left (A B : OpField k V) (hA : ∀ u, A.mode u = 0) (n s : ℤ) :
    (prod n A B).mode s = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [prod_mode, prodMode_apply, LinearMap.zero_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
  unfold prodTerm
  rw [hA, hA]
  simp

theorem prod_eq_zero_right (A B : OpField k V) (hB : ∀ u, B.mode u = 0) (n s : ℤ) :
    (prod n A B).mode s = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [prod_mode, prodMode_apply, LinearMap.zero_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
  unfold prodTerm
  rw [hB, hB]
  simp

/-- A local pair has vanishing products from the locality order on (integer index). -/
theorem prod_eq_zero_of_local' (A B : OpField k V) {N : ℕ} (hloc : IsLocal A B N) {n : ℤ}
    (hn : (N : ℤ) ≤ n) (s : ℤ) : (prod n A B).mode s = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  exact prod_eq_zero_of_local A B N hloc m (by omega) s

/-- `Xe(u, w) = ((A_(u)B)_(w) C)_s v`. -/
noncomputable def eX (A B C : OpField k V) (s : ℤ) (v : V) : ℤ → ℤ → V :=
  fun u w => (prod w (prod u A B) C).mode s v
/-- `Ye(u, w) = (A_(u)(B_(w)C))_s v`. -/
noncomputable def eY (A B C : OpField k V) (s : ℤ) (v : V) : ℤ → ℤ → V :=
  fun u w => (prod u A (prod w B C)).mode s v
/-- `Ze(u, w) = (B_(u)(A_(w)C))_s v`. -/
noncomputable def eZ (A B C : OpField k V) (s : ℤ) (v : V) : ℤ → ℤ → V :=
  fun u w => (prod u B (prod w A C)).mode s v

/-- The `E`-level Borcherds defect (ranges from the locality order `N`). -/
noncomputable def eD (A B C : OpField k V) (N : ℕ) (s : ℤ) (v : V) (p q r : ℤ) : V :=
  lsum k (eX A B C s v) p q r ((N : ℤ) - r).toNat -
    (ysum k (eY A B C s v) p q r ((N : ℤ) - q).toNat -
      (-1 : k) ^ r • ysum k (eZ A B C s v) q p r ((N : ℤ) - p).toNat)

section E

variable (A B C : OpField k V) (N : ℕ) (hAB : IsLocal A B N) (hAC : IsLocal A C N)
  (hBC : IsLocal B C N) (s : ℤ) (v : V)

include hAB in
theorem eX_eq_zero {u : ℤ} (hu : (N : ℤ) ≤ u) (w : ℤ) : eX A B C s v u w = 0 := by
  show (prod w (prod u A B) C).mode s v = 0
  rw [prod_eq_zero_left _ C (fun t => prod_eq_zero_of_local' A B hAB hu t) w s,
    LinearMap.zero_apply]

include hBC in
theorem eY_eq_zero (u : ℤ) {w : ℤ} (hw : (N : ℤ) ≤ w) : eY A B C s v u w = 0 := by
  show (prod u A (prod w B C)).mode s v = 0
  rw [prod_eq_zero_right A _ (fun t => prod_eq_zero_of_local' B C hBC hw t) u s,
    LinearMap.zero_apply]

include hAC in
theorem eZ_eq_zero (u : ℤ) {w : ℤ} (hw : (N : ℤ) ≤ w) : eZ A B C s v u w = 0 := by
  show (prod u B (prod w A C)).mode s v = 0
  rw [prod_eq_zero_right B _ (fun t => prod_eq_zero_of_local' A C hAC hw t) u s,
    LinearMap.zero_apply]

include hAB in
theorem eL_stable (p q r : ℤ) {M M' : ℕ} (hM : ((N : ℤ) - r).toNat ≤ M)
    (hM' : ((N : ℤ) - r).toNat ≤ M') :
    lsum k (eX A B C s v) p q r M = lsum k (eX A B C s v) p q r M' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    rw [eX_eq_zero A B C N hAB s v (by omega), smul_zero]) hM hM'

include hBC in
theorem eY_stable (p q r : ℤ) {M M' : ℕ} (hM : ((N : ℤ) - q).toNat ≤ M)
    (hM' : ((N : ℤ) - q).toNat ≤ M') :
    ysum k (eY A B C s v) p q r M = ysum k (eY A B C s v) p q r M' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    rw [eY_eq_zero A B C N hBC s v _ (by omega), smul_zero]) hM hM'

include hAC in
theorem eZ_stable (p q r : ℤ) {M M' : ℕ} (hM : ((N : ℤ) - p).toNat ≤ M)
    (hM' : ((N : ℤ) - p).toNat ≤ M') :
    ysum k (eZ A B C s v) q p r M = ysum k (eZ A B C s v) q p r M' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    rw [eZ_eq_zero A B C N hAC s v _ (by omega), smul_zero]) hM hM'

include hAB hAC hBC in
/-- **The Pascal recursion** of the `E`-level defect (step 1). -/
theorem eD_pascal (p q r : ℤ) :
    eD A B C N s v (p + 1) q r = eD A B C N s v p (q + 1) r + eD A B C N s v p q (r + 1) := by
  have hL : lsum k (eX A B C s v) (p + 1) q r ((N : ℤ) - r).toNat =
      lsum k (eX A B C s v) p (q + 1) r ((N : ℤ) - r).toNat +
        lsum k (eX A B C s v) p q (r + 1) ((N : ℤ) - (r + 1)).toNat := by
    set L := ((N : ℤ) - r).toNat
    rw [eL_stable A B C N hAB s v (p + 1) q r (M := L) (M' := L + 1) le_rfl (by omega),
      eL_stable A B C N hAB s v p (q + 1) r (M := L) (M' := L + 1) le_rfl (by omega),
      eL_stable A B C N hAB s v p q (r + 1) (M := ((N : ℤ) - (r + 1)).toNat) (M' := L)
        le_rfl (by omega)]
    exact lsum_pascal k (eX A B C s v) p q r L
  have hY : ysum k (eY A B C s v) (p + 1) q r ((N : ℤ) - q).toNat =
      ysum k (eY A B C s v) p (q + 1) r ((N : ℤ) - (q + 1)).toNat +
        ysum k (eY A B C s v) p q (r + 1) ((N : ℤ) - q).toNat := by
    set L := ((N : ℤ) - q).toNat
    rw [eY_stable A B C N hBC s v (p + 1) q r (M := L) (M' := L + 1) le_rfl (by omega),
      eY_stable A B C N hBC s v p (q + 1) r (M := ((N : ℤ) - (q + 1)).toNat) (M' := L)
        le_rfl (by omega),
      eY_stable A B C N hBC s v p q (r + 1) (M := L) (M' := L + 1) le_rfl (by omega),
      ysum_pascal k (eY A B C s v) p q r L]
    abel
  have hZ : ysum k (eZ A B C s v) q (p + 1) r ((N : ℤ) - (p + 1)).toNat =
      ysum k (eZ A B C s v) (q + 1) p r ((N : ℤ) - p).toNat -
        ysum k (eZ A B C s v) q p (r + 1) ((N : ℤ) - p).toNat := by
    set L := ((N : ℤ) - p).toNat
    rw [eZ_stable A B C N hAC s v (p + 1) q r (M := ((N : ℤ) - (p + 1)).toNat) (M' := L)
        le_rfl (by omega),
      eZ_stable A B C N hAC s v p (q + 1) r (M := L) (M' := L + 1) le_rfl (by omega),
      eZ_stable A B C N hAC s v p q (r + 1) (M := L) (M' := L + 1) le_rfl (by omega),
      ysum_pascal k (eZ A B C s v) q p r L]
    abel
  have hs : (-1 : k) ^ (r + 1) = -(-1 : k) ^ r := by
    rw [zpow_add_one₀ (by norm_num : (-1 : k) ≠ 0)]
    ring
  unfold eD
  rw [hL, hY, hZ, hs]
  module

include hAB hAC hBC in
/-- **Reduction** (step 4): a locality face `r ≥ R₀` and one plane `p = P₀` force `eD ≡ 0`. -/
theorem eD_eq_zero_of_face_plane (R₀ P₀ : ℤ)
    (hface : ∀ p q r, R₀ ≤ r → eD A B C N s v p q r = 0)
    (hplane : ∀ q r, eD A B C N s v P₀ q r = 0) : ∀ p q r, eD A B C N s v p q r = 0 :=
  eq_zero_of_pascal_shift_face (fun p q r => eD A B C N s v p q r)
    (eD_pascal A B C N hAB hAC hBC s v) R₀ P₀ hface hplane

include hAB in
/-- The plane `p = 0` of the `E`-level defect is the **field iterate identity**:
`((A_(n)B)_(m) C)_s v = ∑_t (-1)^t (n choose t) ((A_(n-t)(B_(m+t)C))_s v
  - (-1)^n (B_(n+m-t)(A_t C))_s v)` (with the ranges of `eD`). -/
theorem fieldIter_of_eD (h : ∀ m n, eD A B C N s v 0 m n = 0) (n m : ℤ) :
    (prod m (prod n A B) C).mode s v =
      ysum k (eY A B C s v) 0 m n ((N : ℤ) - m).toNat -
        (-1 : k) ^ n • ysum k (eZ A B C s v) m 0 n ((N : ℤ) - 0).toNat := by
  have h0 := h m n
  unfold eD at h0
  have hL : lsum k (eX A B C s v) 0 m n ((N : ℤ) - n).toNat =
      (prod m (prod n A B) C).mode s v := by
    rw [eL_stable A B C N hAB s v 0 m n (M' := ((N : ℤ) - n).toNat + 1) le_rfl (by omega)]
    unfold lsum
    rw [sum_range_eq_zero_term (by omega) (fun t ht => by
      rw [zbinom_zero_left_of_pos k (by omega), zero_smul])]
    simp only [zbinom_zero_right, one_smul, Nat.cast_zero, add_zero, zero_add, sub_zero]
    rfl
  rw [hL] at h0
  exact sub_eq_zero.1 h0

end E

end OpField

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.OpField.eD_pascal
#print axioms HaagerupIzumi.C8.OpField.eD_eq_zero_of_face_plane
#print axioms HaagerupIzumi.C8.OpField.fieldIter_of_eD
