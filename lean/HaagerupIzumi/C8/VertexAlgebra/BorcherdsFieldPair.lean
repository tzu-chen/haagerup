module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsFields

@[expose] public section

/-!
# The Borcherds identity for a local pair of fields and its field products

W3, item (1), route A groundwork (`Lattice/W3_PLAN.md`, section 2).  For two fields `A, B`
(`OpField`, `VertexAlgebra/BorcherdsFields.lean`) that are local of order `N`, and the field
products `A_(n) B` (`OpField.prod`), the Borcherds identity holds on every vector:

`∑_t (p choose t) (A_(r+t) B)_{p+q-t} v
   = ∑_t (-1)^t (r choose t) (A_{p+r-t} B_{q+t} v - (-1)^r B_{q+r-t} A_{p+t} v)`

(**`borcherds_of_local`**; the mode form of the Jacobi identity for a local pair of fields,
Lepowsky–Li, Ch. 5, and Kac, *Vertex algebras for beginners*, §4.8, numbers from memory).
Proof: the defect satisfies the Pascal recursion (`fD_pascal`, from `lsum_pascal`,
`ysum_pascal`), the iterate family `p = 0` is the definition of the field product
(`fD_iter`), and the locality face `r ≥ N` is locality (`fD_face`, via `ysum_sub_eq_dz`);
conclude with `eq_zero_of_pascal_iter_face`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-- For `r = R ≥ 0`: `∑_t (-1)^t (R choose t) (Y(p+R-t, q+t) - (-1)^R Z(q+R-t, p+t))
= dz R (Y - Zᵀ) (p, q)`. -/
theorem ysum_sub_eq_dz (k : Type*) [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    (Y Z : ℤ → ℤ → W) (p q : ℤ) (R : ℕ) {M : ℕ} (hM : R + 1 ≤ M) :
    ysum k Y p q R M - (-1 : k) ^ (R : ℤ) • ysum k Z q p R M =
      dz k R (fun u w => Y u w - Z w u) p q := by
  have hcutY : ysum k Y p q R M = ysum k Y p q R (R + 1) :=
    sum_range_eq_of_vanish _ (fun t ht => by
      rw [zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul]) hM le_rfl
  have hcutZ : ysum k Z q p R M = ysum k Z q p R (R + 1) :=
    sum_range_eq_of_vanish _ (fun t ht => by
      rw [zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul]) hM le_rfl
  have hYd : ∀ (G : ℤ → ℤ → W) (p q : ℤ), ysum k G p q R (R + 1) = dz k R G p q :=
    fun G p q => by
      unfold ysum dz
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [zbinom_natCast]
  have hZ : ysum k Z q p R (R + 1) = (-1 : k) ^ R • dz k R (fun u w => Z w u) p q := by
    rw [hYd]
    exact dz_swap k R (fun u w => Z w u) p q
  rw [hcutY, hcutZ, hZ, zpow_natCast, smul_smul, neg_one_pow_mul_self, one_smul, dz_sub_fun,
    hYd]

namespace OpField

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- `X(u, w) = (A_(u) B)_w v`. -/
noncomputable def bX (A B : OpField k V) (v : V) : ℤ → ℤ → V := fun u w => (prod u A B).mode w v
/-- `Y(u, w) = A_u B_w v`. -/
def bY (A B : OpField k V) (v : V) : ℤ → ℤ → V := fun u w => A.mode u (B.mode w v)
/-- `Z(u, w) = B_u A_w v`. -/
def bZ (A B : OpField k V) (v : V) : ℤ → ℤ → V := fun u w => B.mode u (A.mode w v)

/-- The Borcherds defect of a pair of fields on `v`, with ranges adapted to the truncation
bounds `N` (locality), `NA`, `NB`. -/
noncomputable def fD (A B : OpField k V) (v : V) (N : ℕ) (NA NB : ℤ) (p q r : ℤ) : V :=
  lsum k (bX A B v) p q r ((N : ℤ) - r).toNat -
    (ysum k (bY A B v) p q r (NB - q).toNat -
      (-1 : k) ^ r • ysum k (bZ A B v) q p r (NA - p).toNat)

section Local

variable (A B : OpField k V) (N : ℕ)
  (hloc : ∀ p q, dz k N (opComm A.mode B.mode) p q = 0) (v : V) (NA NB : ℤ)
  (hA : ∀ u, NA ≤ u → A.mode u v = 0) (hB : ∀ u, NB ≤ u → B.mode u v = 0)

include hloc in
theorem bX_eq_zero {u : ℤ} (hu : (N : ℤ) ≤ u) (w : ℤ) : bX A B v u w = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = n := ⟨u.toNat, by omega⟩
  show (prod n A B).mode w v = 0
  rw [prod_eq_zero_of_local A B N hloc n (by omega) w, LinearMap.zero_apply]

include hloc in
theorem lsum_stable (p q r : ℤ) {M M' : ℕ} (hM : ((N : ℤ) - r).toNat ≤ M)
    (hM' : ((N : ℤ) - r).toNat ≤ M') :
    lsum k (bX A B v) p q r M = lsum k (bX A B v) p q r M' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    rw [bX_eq_zero A B N hloc v (by omega), smul_zero]) hM hM'

include hB in
theorem ysumY_stable (p q r : ℤ) {M M' : ℕ} (hM : (NB - q).toNat ≤ M)
    (hM' : (NB - q).toNat ≤ M') :
    ysum k (bY A B v) p q r M = ysum k (bY A B v) p q r M' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    show _ • A.mode _ (B.mode (q + t) v) = 0
    rw [hB (q + t) (by omega), map_zero, smul_zero]) hM hM'

include hA in
theorem ysumZ_stable (p q r : ℤ) {M M' : ℕ} (hM : (NA - p).toNat ≤ M)
    (hM' : (NA - p).toNat ≤ M') :
    ysum k (bZ A B v) q p r M = ysum k (bZ A B v) q p r M' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    show _ • B.mode _ (A.mode (p + t) v) = 0
    rw [hA (p + t) (by omega), map_zero, smul_zero]) hM hM'

include hloc hA hB in
/-- **The Pascal recursion** of the defect. -/
theorem fD_pascal (p q r : ℤ) :
    fD A B v N NA NB (p + 1) q r = fD A B v N NA NB p (q + 1) r + fD A B v N NA NB p q (r + 1) := by
  have hL : lsum k (bX A B v) (p + 1) q r ((N : ℤ) - r).toNat =
      lsum k (bX A B v) p (q + 1) r ((N : ℤ) - r).toNat +
        lsum k (bX A B v) p q (r + 1) ((N : ℤ) - (r + 1)).toNat := by
    set L := ((N : ℤ) - r).toNat
    rw [lsum_stable A B N hloc v (p + 1) q r (M := L) (M' := L + 1) le_rfl (by omega),
      lsum_stable A B N hloc v p (q + 1) r (M := L) (M' := L + 1) le_rfl (by omega),
      lsum_stable A B N hloc v p q (r + 1) (M := ((N : ℤ) - (r + 1)).toNat) (M' := L)
        le_rfl (by omega)]
    exact lsum_pascal k (bX A B v) p q r L
  have hY : ysum k (bY A B v) (p + 1) q r (NB - q).toNat =
      ysum k (bY A B v) p (q + 1) r (NB - (q + 1)).toNat +
        ysum k (bY A B v) p q (r + 1) (NB - q).toNat := by
    set L := (NB - q).toNat
    rw [ysumY_stable A B v NB hB (p + 1) q r (M := L) (M' := L + 1) le_rfl (by omega),
      ysumY_stable A B v NB hB p (q + 1) r (M := (NB - (q + 1)).toNat) (M' := L)
        le_rfl (by omega),
      ysumY_stable A B v NB hB p q (r + 1) (M := L) (M' := L + 1) le_rfl (by omega),
      ysum_pascal k (bY A B v) p q r L]
    abel
  have hZ : ysum k (bZ A B v) q (p + 1) r (NA - (p + 1)).toNat =
      ysum k (bZ A B v) (q + 1) p r (NA - p).toNat -
        ysum k (bZ A B v) q p (r + 1) (NA - p).toNat := by
    set L := (NA - p).toNat
    rw [ysumZ_stable A B v NA hA (p + 1) q r (M := (NA - (p + 1)).toNat) (M' := L)
        le_rfl (by omega),
      ysumZ_stable A B v NA hA p (q + 1) r (M := L) (M' := L + 1) le_rfl (by omega),
      ysumZ_stable A B v NA hA p q (r + 1) (M := L) (M' := L + 1) le_rfl (by omega),
      ysum_pascal k (bZ A B v) q p r L]
    abel
  have hs : (-1 : k) ^ (r + 1) = -(-1 : k) ^ r := by
    rw [zpow_add_one₀ (by norm_num : (-1 : k) ≠ 0)]
    ring
  unfold fD
  rw [hL, hY, hZ, hs]
  module

include hloc hA hB in
/-- The iterate family `p = 0` is the definition of the field product. -/
theorem fD_iter (q r : ℤ) : fD A B v N NA NB 0 q r = 0 := by
  obtain ⟨M₀, hM₀⟩ := prodMode_eq_sum A B r q v
  obtain ⟨M, h1, h2, h3, h4⟩ : ∃ M : ℕ, M₀ ≤ M ∧ ((N : ℤ) - r).toNat + 1 ≤ M ∧
      (NB - q).toNat ≤ M ∧ (NA - 0).toNat ≤ M :=
    ⟨M₀ + (((N : ℤ) - r).toNat + 1) + (NB - q).toNat + (NA - 0).toNat, by omega, by omega,
      by omega, by omega⟩
  unfold fD
  rw [lsum_stable A B N hloc v 0 q r (M' := M) le_rfl (by omega),
    ysumY_stable A B v NB hB 0 q r (M' := M) le_rfl h3,
    ysumZ_stable A B v NA hA 0 q r (M' := M) le_rfl h4]
  have hL : lsum k (bX A B v) 0 q r M = (prod r A B).mode q v := by
    unfold lsum
    rw [sum_range_eq_zero_term (by omega) (fun t ht => by
      rw [zbinom_zero_left_of_pos k (by omega), zero_smul])]
    simp only [zbinom_zero_right, one_smul, Nat.cast_zero, add_zero, zero_add, sub_zero]
    rfl
  rw [hL, prod_mode, hM₀ M h1]
  unfold ysum prodTerm bY bZ
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun t _ => ?_
  simp only [zero_add]
  rw [show q + r - (t : ℤ) = r + q - t by ring]
  module

include hloc hA hB in
/-- The locality face: the defect vanishes for `r ≥ N`. -/
theorem fD_face (p q r : ℤ) (hr : (N : ℤ) ≤ r) : fD A B v N NA NB p q r = 0 := by
  obtain ⟨R, rfl⟩ : ∃ R : ℕ, r = R := ⟨r.toNat, by omega⟩
  obtain ⟨M, h2, h3, h4⟩ : ∃ M : ℕ, R + 1 ≤ M ∧ (NB - q).toNat ≤ M ∧ (NA - p).toNat ≤ M :=
    ⟨R + 1 + (NB - q).toNat + (NA - p).toNat, by omega, by omega, by omega⟩
  unfold fD
  have hL : lsum k (bX A B v) p q R ((N : ℤ) - R).toNat = 0 :=
    Finset.sum_eq_zero fun t _ => by rw [bX_eq_zero A B N hloc v (by omega), smul_zero]
  have e : dz k R (fun u w => bY A B v u w - bZ A B v w u) p q =
      dz k R (opComm A.mode B.mode) p q v := by
    rw [dz_linearMap_apply]
    rfl
  rw [hL, ysumY_stable A B v NB hB p q R (M' := M) le_rfl h3,
    ysumZ_stable A B v NA hA p q R (M' := M) le_rfl h4,
    ysum_sub_eq_dz k (bY A B v) (bZ A B v) p q R h2, e,
    dz_mono k _ hloc (by omega) p q, LinearMap.zero_apply, sub_zero]

include hloc hA hB in
/-- The defect vanishes identically. -/
theorem fD_eq_zero : ∀ p q r, fD A B v N NA NB p q r = 0 :=
  eq_zero_of_pascal_iter_face (fun p q r => fD A B v N NA NB p q r)
    (fD_pascal A B N hloc v NA NB hA hB) N
    (fun p q r hr => fD_face A B N hloc v NA NB hA hB p q r hr)
    (fD_iter A B N hloc v NA NB hA hB)

end Local

/-- **The Borcherds identity for a local pair of fields**: if `A, B` are local of order `N`, then
on every `v` and for all `p, q, r`, with every large enough range `M`,
`∑_{t<M} (p choose t) (A_(r+t) B)_{p+q-t} v
  = ∑_{t<M} (-1)^t (r choose t) (A_{p+r-t} B_{q+t} v - (-1)^r B_{q+r-t} A_{p+t} v)`. -/
theorem borcherds_of_local (A B : OpField k V) (N : ℕ)
    (hloc : ∀ p q, dz k N (opComm A.mode B.mode) p q = 0) (v : V) (p q r : ℤ) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → lsum k (bX A B v) p q r M =
      ysum k (bY A B v) p q r M - (-1 : k) ^ r • ysum k (bZ A B v) q p r M := by
  obtain ⟨NA, hA⟩ := A.trunc v
  obtain ⟨NB, hB⟩ := B.trunc v
  have h0 := fD_eq_zero A B N hloc v NA NB hA hB p q r
  refine ⟨((N : ℤ) - r).toNat + (NB - q).toNat + (NA - p).toNat, fun M hM => ?_⟩
  unfold fD at h0
  rw [lsum_stable A B N hloc v p q r (M := M) (M' := ((N : ℤ) - r).toNat) (by omega) le_rfl,
    ysumY_stable A B v NB hB p q r (M := M) (M' := (NB - q).toNat) (by omega) le_rfl,
    ysumZ_stable A B v NA hA p q r (M := M) (M' := (NA - p).toNat) (by omega) le_rfl]
  exact sub_eq_zero.1 h0

end OpField

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ysum_sub_eq_dz
#print axioms HaagerupIzumi.C8.OpField.fD_pascal
#print axioms HaagerupIzumi.C8.OpField.fD_eq_zero
#print axioms HaagerupIzumi.C8.OpField.borcherds_of_local
