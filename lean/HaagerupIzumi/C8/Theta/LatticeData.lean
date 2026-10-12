module

public import HaagerupIzumi.C8.Theta.Harmonic
public import HaagerupIzumi.C8.Theta.LatticeThetaModular

@[expose] public section

/-!
# Concrete lattice data for the four theta tables

W6 phase 2, plan item 1 (`Theta/W6_PLAN.md`).  For the four lattices of the proof of
Proposition `prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): `L₇ ⊕ A₂` (`Theta/M3First`), `G₇⁻`
(`M3Reverse`), `A₁ ⊕ A₁ ⊕ A₂` (`M6First`) and `G₆⁻` (`M6Reverse`), we prove

* positive definiteness of `gramR G` (explicit sums of squares) and evenness;
* `(gramR G)⁻¹ = G⁻¹_ℚ` (the inverse Gram matrices of the table files), hence harmonicity over
  ℝ of the weights `H` from the `pairTrace` facts of `Theta/Harmonic`;
* residue systems `hR` of `ℤ⁴/Gℤ⁴ ≅ L'/L`, labelled as in the manuscript, from explicit
  Smith-type factorizations `U G V = diag(d)` (`existsUnique_residue_of_smith`, a general
  lemma, with all identities checked by `decide`);
* the identification of the manuscript's coset labels with `G⁻¹ (label vector)`;
* the `S`- and `T`-laws of the coset theta vectors with and without the harmonic weight, with
  the `S`- and `T`-matrices written explicitly as finite data, in Borcherds' convention
  (`T ↦ e(q(γ))`, `S ↦ e(-sig/8)/√|D| · e(-(γ, δ))`, here `e(-4/8) = -1`):
  `Θ_{H,p}(-1/τ) = -τ⁴/√|D| ∑_q e(-(γ_p, γ_q)) Θ_{H,q}(τ)` and
  `Θ_{H,p}(τ+1) = e(q(γ_p)) Θ_{H,p}(τ)` (`τ²` instead of `τ⁴` without weight);
* the symmetries used by the projections of the tables: lattice isometries
  (`latticeThetaQ_isometry`) for `L₇ ⊕ A₂` (`r ↦ -r`), `A₁ ⊕ A₁ ⊕ A₂` (swap, `s ↦ -s`) and `G₆⁻`
  (`b ↔ c`); for `G₇⁻` the needed `(r, s) ↦ (-r, s)` is `j ↦ 13 j` on `ℤ/21`, an isometry of the
  discriminant form (`O(D)`), and the `S`/`T`-data are invariant under it (finite check).

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex Matrix

namespace HaagerupIzumi.C8
namespace Theta

/-! ## General tools -/

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A rational vector as a real vector. -/
def ratVec (v : n → ℚ) : n → ℝ := fun i => (v i : ℝ)

omit [Fintype n] [DecidableEq n] in
theorem intVec_eq_ratVec (k : n → ℤ) : intVec k = ratVec (fun i => (k i : ℚ)) := by
  funext i
  simp [intVec, ratVec]

omit [DecidableEq n] in
theorem ratVec_dotProduct (v w : n → ℚ) : ratVec v ⬝ᵥ ratVec w = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  simp [ratVec, dotProduct]

omit [DecidableEq n] in
theorem map_ratCast_mulVec (K : Matrix n n ℚ) (v : n → ℚ) :
    K.map (Rat.cast : ℚ → ℝ) *ᵥ ratVec v = ratVec (K *ᵥ v) := by
  funext i
  simp [ratVec, mulVec, dotProduct]

omit [DecidableEq n] in
theorem gramR_mulVec_ratVec (Gz : Matrix n n ℤ) (v : n → ℚ) :
    gramR Gz *ᵥ ratVec v = ratVec (Gz.map (Int.cast : ℤ → ℚ) *ᵥ v) := by
  funext i
  simp [gramR, ratVec, mulVec, dotProduct]

omit [DecidableEq n] in
theorem qf_gramR_ratVec (Gz : Matrix n n ℤ) (v : n → ℚ) :
    qf (gramR Gz) (ratVec v) = ((v ⬝ᵥ (Gz.map (Int.cast : ℤ → ℚ) *ᵥ v) : ℚ) : ℝ) := by
  rw [qf, gramR_mulVec_ratVec, ratVec_dotProduct]

omit [DecidableEq n] in
/-- `Q_M` at a rational point, for a rational weight `M`. -/
theorem qf_map_ratVec (M : Matrix n n ℚ) (v : n → ℚ) :
    qf (M.map (Rat.cast : ℚ → ℝ)) (ratVec v) = ((v ⬝ᵥ (M *ᵥ v) : ℚ) : ℝ) := by
  rw [qf, map_ratCast_mulVec, ratVec_dotProduct]

/-- The inverse of `gramR Gz` is the rational inverse, given `Gz · K = 1` over ℚ. -/
theorem inv_gramR_eq {Gz : Matrix n n ℤ} {K : Matrix n n ℚ}
    (hK : ∀ i j, ∑ k, (Gz i k : ℚ) * K k j = if i = j then 1 else 0) :
    (gramR Gz)⁻¹ = K.map (Rat.cast : ℚ → ℝ) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  have h := congrArg (Rat.cast : ℚ → ℝ) (hK i j)
  rw [Rat.cast_sum] at h
  simp only [Rat.cast_mul, Rat.cast_intCast] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [gramR, Matrix.map_apply]
  rw [h]
  split_ifs <;> simp

/-- Harmonicity over ℝ from the rational `pairTrace` facts of `Theta/Harmonic`. -/
theorem harmonic_of_pairTrace {Gz : Matrix (Fin 4) (Fin 4) ℤ} {K M : Matrix (Fin 4) (Fin 4) ℚ}
    (hinv : (gramR Gz)⁻¹ = K.map (Rat.cast : ℚ → ℝ)) (h : pairTrace K M = 0) :
    ∑ i, ∑ j, (gramR Gz)⁻¹ i j * (M.map (Rat.cast : ℚ → ℝ)) i j = 0 := by
  rw [hinv]
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  simp only [pairTrace, Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] at h'
  simpa only [Matrix.map_apply] using h'

theorem det_gramR (Gz : Matrix n n ℤ) : (gramR Gz).det = (Gz.det : ℝ) := by
  have h := (Int.castRingHom ℝ).map_det Gz
  rw [eq_intCast] at h
  rw [h]
  rfl

omit [DecidableEq n] in
/-- A positive-definiteness criterion: a symmetric integral Gram matrix whose real form
dominates `c |x|²`, `c > 0`. -/
theorem posDef_gramR_of_coercive {Gz : Matrix n n ℤ} (hsymm : Gzᵀ = Gz) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ x : n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (gramR Gz *ᵥ x)) : (gramR Gz).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · show (gramR Gz)ᴴ = gramR Gz
    rw [conjTranspose_eq_transpose_of_trivial, gramR, ← Matrix.transpose_map, hsymm]
  · rw [star_trivial]
    have h0 : 0 ≤ x ⬝ᵥ x := dotProduct_self_nonneg' x
    have h1 : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.1 h)
    nlinarith [hQ x, lt_of_le_of_ne h0 (Ne.symm h1)]

omit [DecidableEq n] in
/-- Integral congruence `Uᵀ Gz U = Gz` transported to `gramR`. -/
theorem gramR_transpose_mul_mul {U Gz : Matrix n n ℤ} (h : Uᵀ * Gz * U = Gz) :
    (gramR U)ᵀ * gramR Gz * gramR U = gramR Gz := by
  ext i j
  have h' := congrArg (fun A : Matrix n n ℤ => ((A i j : ℤ) : ℝ)) h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Int.cast_sum, Int.cast_mul] at h'
  simpa [gramR, Matrix.mul_apply, Matrix.transpose_apply] using h'

omit [DecidableEq n] in
/-- Rational congruence `Uᵀ M U = M` transported to the real weight. -/
theorem ratCast_transpose_mul_mul {U : Matrix n n ℤ} {M : Matrix n n ℚ}
    (h : (U.map (Int.cast : ℤ → ℚ))ᵀ * M * U.map (Int.cast : ℤ → ℚ) = M) :
    (gramR U)ᵀ * M.map (Rat.cast : ℚ → ℝ) * gramR U = M.map (Rat.cast : ℚ → ℝ) := by
  ext i j
  have h' := congrArg (fun A : Matrix n n ℚ => ((A i j : ℚ) : ℝ)) h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_intCast] at h'
  simpa [gramR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using h'

omit [DecidableEq n] in
/-- `Q_G(Ax) = Q_{AᵀGA}(x)`. -/
theorem qf_mulVec (G A : Matrix n n ℝ) (x : n → ℝ) : qf G (A *ᵥ x) = qf (Aᵀ * G * A) x := by
  rw [qf, qf, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Aᵀ, vecMul_transpose]

/-- **Lattice isometries.**  If `U ∈ GL(ℤ^d)` preserves the form (`UᵀGU = G`) and the weight
(`UᵀMU = M`), then `Θ_{M,Uγ} = Θ_{M,γ}`. -/
theorem latticeThetaQ_isometry {G M : Matrix n n ℝ} {Uz Uiz : Matrix n n ℤ}
    (hU : Uz * Uiz = 1) (hU' : Uiz * Uz = 1)
    (hG : (gramR Uz)ᵀ * G * gramR Uz = G) (hM : (gramR Uz)ᵀ * M * gramR Uz = M)
    (γ : n → ℝ) (τ : ℂ) : latticeThetaQ G M (gramR Uz *ᵥ γ) τ = latticeThetaQ G M γ τ := by
  let e : (n → ℤ) ≃ (n → ℤ) :=
    ⟨(Uz *ᵥ ·), (Uiz *ᵥ ·), fun m => by simp [mulVec_mulVec, hU'],
      fun m => by simp [mulVec_mulVec, hU]⟩
  unfold latticeThetaQ
  rw [← e.tsum_eq]
  refine tsum_congr fun m => ?_
  have hx : gramR Uz *ᵥ γ + intVec (e m) = gramR Uz *ᵥ (γ + intVec m) := by
    show _ + intVec (Uz *ᵥ m) = _
    rw [intVec_mulVec, mulVec_add]
  rw [hx, qf_mulVec, qf_mulVec, hG, hM]

/-- **Lattice isometries**, unweighted. -/
theorem latticeTheta_isometry {G : Matrix n n ℝ} {Uz Uiz : Matrix n n ℤ}
    (hU : Uz * Uiz = 1) (hU' : Uiz * Uz = 1) (hG : (gramR Uz)ᵀ * G * gramR Uz = G)
    (γ : n → ℝ) (τ : ℂ) : latticeTheta G (gramR Uz *ᵥ γ) τ = latticeTheta G γ τ := by
  let e : (n → ℤ) ≃ (n → ℤ) :=
    ⟨(Uz *ᵥ ·), (Uiz *ᵥ ·), fun m => by simp [mulVec_mulVec, hU'],
      fun m => by simp [mulVec_mulVec, hU]⟩
  unfold latticeTheta
  rw [← e.tsum_eq]
  refine tsum_congr fun m => ?_
  have hx : gramR Uz *ᵥ γ + intVec (e m) = gramR Uz *ᵥ (γ + intVec m) := by
    show _ + intVec (Uz *ᵥ m) = _
    rw [intVec_mulVec, mulVec_add]
  rw [hx, qf_mulVec, hG]

/-! ### Residue systems from Smith-type factorizations -/

/-- Componentwise uniqueness of division with remainder by a positive diagonal. -/
theorem eq_of_box {dv : n → ℤ} (hd : ∀ j, 0 < dv j) {c c' a a' : n → ℤ}
    (hc : ∀ j, 0 ≤ c j ∧ c j < dv j) (hc' : ∀ j, 0 ≤ c' j ∧ c' j < dv j)
    (h : c + diagonal dv *ᵥ a = c' + diagonal dv *ᵥ a') : c = c' ∧ a = a' := by
  have key : ∀ j, c j = c' j ∧ a j = a' j := by
    intro j
    have hj := congrFun h j
    simp only [Pi.add_apply, mulVec_diagonal] at hj
    have e1 : c j = (c j + dv j * a j) % dv j := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (hc j).1 (hc j).2]
    have e2 : c' j = (c' j + dv j * a' j) % dv j := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (hc' j).1 (hc' j).2]
    have hcc : c j = c' j := by rw [e1, e2, hj]
    refine ⟨hcc, ?_⟩
    have : dv j * a j = dv j * a' j := by linarith
    exact mul_left_cancel₀ (hd j).ne' this
  exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩

/-- **Residue systems from a Smith-type factorization.**  If `U Gz V = diag(d)` with `U`, `V`
invertible over ℤ (`Ui U = 1`, `V Vi = 1`), and the labels `lab : ι → ℤ^d` are injective, are
sent by `U` into the box `∏ [0, dⱼ)`, and are as many as the box, then they form a complete
system of representatives of `ℤ^d / Gz ℤ^d`, in the form required by `latticeTheta_S`. -/
theorem existsUnique_residue_of_smith {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Gz U Ui V Vi : Matrix n n ℤ} {dv : n → ℤ} {lab : ι → n → ℤ}
    (hUi : Ui * U = 1) (hV : V * Vi = 1) (hS : U * Gz * V = diagonal dv)
    (hd : ∀ j, 0 < dv j) (hbox : ∀ i j, 0 ≤ (U *ᵥ lab i) j ∧ (U *ᵥ lab i) j < dv j)
    (hinj : Function.Injective lab) (hcard : Fintype.card ι = ∏ j, (dv j).toNat) :
    ∀ k : n → ℤ, ∃! p : (Finset.univ.image lab) × (n → ℤ), (p.1 : n → ℤ) + Gz *ᵥ p.2 = k := by
  classical
  have hUinj : ∀ x y : n → ℤ, U *ᵥ x = U *ᵥ y → x = y := by
    intro x y h
    have hx : Ui *ᵥ (U *ᵥ x) = x := by rw [mulVec_mulVec, hUi, one_mulVec]
    have hy : Ui *ᵥ (U *ᵥ y) = y := by rw [mulVec_mulVec, hUi, one_mulVec]
    rw [← hx, ← hy, h]
  have hUG : U * Gz = diagonal dv * Vi := by
    calc U * Gz = U * Gz * (V * Vi) := by rw [hV, Matrix.mul_one]
      _ = U * Gz * V * Vi := by rw [Matrix.mul_assoc (U * Gz)]
      _ = diagonal dv * Vi := by rw [hS]
  have hsurj : ∀ c : n → ℤ, (∀ j, 0 ≤ c j ∧ c j < dv j) → ∃ i, U *ᵥ lab i = c := by
    intro c hc
    let B : Finset (n → ℤ) := Fintype.piFinset fun j => Finset.Ico 0 (dv j)
    have hmaps : Set.MapsTo (fun i => U *ᵥ lab i) (Finset.univ : Finset ι) B := by
      intro i _
      simp only [B, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      exact hbox i
    have hinjOn : Set.InjOn (fun i => U *ᵥ lab i) (Finset.univ : Finset ι) :=
      fun i _ i' _ h => hinj (hUinj _ _ h)
    have hcardB : B.card ≤ (Finset.univ : Finset ι).card := by
      rw [Fintype.card_piFinset, Finset.card_univ, hcard]
      simp [Int.card_Ico]
    have hcB : c ∈ (B : Set (n → ℤ)) := by
      simp only [B, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      exact hc
    obtain ⟨i, -, hi⟩ := Finset.surjOn_of_injOn_of_card_le _ hmaps hinjOn hcardB hcB
    exact ⟨i, hi⟩
  have hU_apply : ∀ r m : n → ℤ,
      U *ᵥ (r + Gz *ᵥ m) = U *ᵥ r + diagonal dv *ᵥ (Vi *ᵥ m) := by
    intro r m
    rw [mulVec_add, mulVec_mulVec, hUG, ← mulVec_mulVec]
  intro k
  set y := U *ᵥ k with hy
  set c : n → ℤ := fun j => y j % dv j with hc_def
  set q : n → ℤ := fun j => y j / dv j with hq_def
  have hyc : y = c + diagonal dv *ᵥ q := by
    funext j
    simp only [Pi.add_apply, mulVec_diagonal, c, q]
    exact (Int.emod_add_mul_ediv (y j) (dv j)).symm
  have hcbox : ∀ j, 0 ≤ c j ∧ c j < dv j :=
    fun j => ⟨Int.emod_nonneg _ (hd j).ne', Int.emod_lt_of_pos _ (hd j)⟩
  obtain ⟨i, hi⟩ := hsurj c hcbox
  have hmem : lab i ∈ Finset.univ.image lab := Finset.mem_image_of_mem lab (Finset.mem_univ i)
  refine ⟨(⟨lab i, hmem⟩, V *ᵥ q), ?_, ?_⟩
  · apply hUinj
    show U *ᵥ (lab i + Gz *ᵥ (V *ᵥ q)) = U *ᵥ k
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hS, hi, ← hyc]
  · rintro ⟨⟨r', hr'⟩, m'⟩ h'
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hr'
    have h1 : U *ᵥ lab i' + diagonal dv *ᵥ (Vi *ᵥ m') = c + diagonal dv *ᵥ q := by
      rw [← hU_apply, ← hyc]
      exact congrArg (U *ᵥ ·) h'
    obtain ⟨hc', hq'⟩ := eq_of_box hd (fun j => hbox i' j) hcbox h1
    have hii : lab i' = lab i := hUinj _ _ (hc'.trans hi.symm)
    have hm : m' = V *ᵥ q := by
      rw [← hq', mulVec_mulVec, hV, one_mulVec]
    exact Prod.ext (Subtype.ext hii) hm

/-- Divisibility after `U` decides membership in `Gz ℤ^d`. -/
theorem exists_mulVec_eq_of_dvd {Gz U Ui V : Matrix n n ℤ} {dv : n → ℤ}
    (hUi : Ui * U = 1) (hS : U * Gz * V = diagonal dv) (x : n → ℤ)
    (hdvd : ∀ j, dv j ∣ (U *ᵥ x) j) : ∃ m, x = Gz *ᵥ m := by
  refine ⟨V *ᵥ fun j => (U *ᵥ x) j / dv j, ?_⟩
  have h1 : U *ᵥ (Gz *ᵥ (V *ᵥ fun j => (U *ᵥ x) j / dv j)) = U *ᵥ x := by
    rw [mulVec_mulVec, mulVec_mulVec, hS]
    funext j
    rw [mulVec_diagonal]
    exact Int.mul_ediv_cancel' (hdvd j)
  have hUinj : ∀ x y : n → ℤ, U *ᵥ x = U *ᵥ y → x = y := by
    intro x y h
    have hx : Ui *ᵥ (U *ᵥ x) = x := by rw [mulVec_mulVec, hUi, one_mulVec]
    have hy : Ui *ᵥ (U *ᵥ y) = y := by rw [mulVec_mulVec, hUi, one_mulVec]
    rw [← hx, ← hy, h]
  exact (hUinj _ _ h1).symm

/-- The determinant from a Smith-type factorization `U Gz V = diag(d)` with `U`, `V` invertible
over ℤ, given `det Gz > 0` and `∏ dⱼ ≥ 0`. -/
theorem det_eq_of_smith {Gz U Ui V Vi : Matrix n n ℤ} {dv : n → ℤ}
    (hUi : Ui * U = 1) (hV : V * Vi = 1) (hS : U * Gz * V = diagonal dv) (hpos : 0 < Gz.det)
    (hd : 0 ≤ ∏ j, dv j) : Gz.det = ∏ j, dv j := by
  have h1 : U.det * Ui.det = 1 := by rw [mul_comm, ← det_mul, hUi, det_one]
  have h2 : V.det * Vi.det = 1 := by rw [← det_mul, hV, det_one]
  have h3 : U.det * Gz.det * V.det = ∏ j, dv j := by rw [← det_mul, ← det_mul, hS, det_diagonal]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with hU | hU <;>
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with hV' | hV' <;>
    rw [hU, hV'] at h3 <;> linarith

/-- `det (gramR Gz)` from a Smith-type factorization, for positive definite `gramR Gz`. -/
theorem det_gramR_of_smith {Gz U Ui V Vi : Matrix n n ℤ} {dv : n → ℤ}
    (hUi : Ui * U = 1) (hV : V * Vi = 1) (hS : U * Gz * V = diagonal dv)
    (hG : (gramR Gz).PosDef) (hd : 0 ≤ ∏ j, dv j) : (gramR Gz).det = ((∏ j, dv j : ℤ) : ℝ) := by
  have hpos : (0 : ℝ) < (Gz.det : ℝ) := by rw [← det_gramR]; exact hG.det_pos
  rw [det_gramR, det_eq_of_smith hUi hV hS (by exact_mod_cast hpos) hd]

/-! ### Label forms of the `S`-laws -/

/-- `latticeThetaQ_S` with the residue system given by injective labels. -/
theorem latticeThetaQ_S_labels {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Gz : Matrix n n ℤ} (hG : (gramR Gz).PosDef) {M : Matrix n n ℝ}
    (hM : ∑ i, ∑ j, (gramR Gz)⁻¹ i j * M i j = 0) {lab : ι → n → ℤ}
    (hinj : Function.Injective lab)
    (hR : ∀ k : n → ℤ, ∃! p : (Finset.univ.image lab) × (n → ℤ),
      (p.1 : n → ℤ) + Gz *ᵥ p.2 = k)
    (i : ι) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeThetaQ (gramR Gz) M ((gramR Gz)⁻¹ *ᵥ intVec (lab i)) (-1 / τ) =
      (((Real.sqrt (gramR Gz).det)⁻¹ : ℝ) : ℂ) * (-I * τ) ^ (Fintype.card n / 2 : ℂ) *
        τ ^ 2 * ∑ j, eChar (intVec (lab j) ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec (lab i))) *
          latticeThetaQ (gramR Gz) M ((gramR Gz)⁻¹ *ᵥ intVec (lab j)) τ := by
  rw [latticeThetaQ_S hG hM _ hR (lab i) hτ, Finset.sum_image fun x _ y _ h => hinj h]

/-- `latticeTheta_S` with the residue system given by injective labels. -/
theorem latticeTheta_S_labels {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Gz : Matrix n n ℤ} (hG : (gramR Gz).PosDef) {lab : ι → n → ℤ}
    (hinj : Function.Injective lab)
    (hR : ∀ k : n → ℤ, ∃! p : (Finset.univ.image lab) × (n → ℤ),
      (p.1 : n → ℤ) + Gz *ᵥ p.2 = k)
    (i : ι) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeTheta (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec (lab i)) (-1 / τ) =
      (((Real.sqrt (gramR Gz).det)⁻¹ : ℝ) : ℂ) * (-I * τ) ^ (Fintype.card n / 2 : ℂ) *
        ∑ j, eChar (intVec (lab j) ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec (lab i))) *
          latticeTheta (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec (lab j)) τ := by
  rw [latticeTheta_S hG _ hR (lab i) hτ, Finset.sum_image fun x _ y _ h => hinj h]

/-- **Flipping the sign of the `S`-exponent** (Borcherds' convention).  If `neg` is an
involution of the labels with `lab (neg q) ≡ -lab q` modulo `Gz ℤ^d`, and `Θ` is invariant
under `ℤ^d`-translations and under `x ↦ -x`, then for `γ = G⁻¹ s ∈ L'` the sums with
`e(+(γ, δ))` and with `e(-(γ, δ))` agree. -/
theorem sum_eChar_neg_of_involutive {ι : Type*} [Fintype ι] {Gz : Matrix n n ℤ}
    (hunit : IsUnit (gramR Gz).det) (hGt : (gramR Gz)ᵀ = gramR Gz) (lab : ι → n → ℤ)
    (neg : ι → ι) (hinv : Function.Involutive neg)
    (hmem : ∀ q, ∃ m, lab (neg q) + lab q = Gz *ᵥ m) (s : n → ℤ) (Θ : (n → ℝ) → ℂ)
    (hper : ∀ x k, Θ (x + intVec k) = Θ x) (hev : ∀ x, Θ (-x) = Θ x) :
    ∑ q, eChar (intVec (lab q) ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec s)) *
        Θ ((gramR Gz)⁻¹ *ᵥ intVec (lab q)) =
      ∑ q, eChar (-(intVec (lab q) ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec s))) *
        Θ ((gramR Gz)⁻¹ *ᵥ intVec (lab q)) := by
  rw [← Equiv.sum_comp (hinv.toPerm neg)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Function.Involutive.coe_toPerm]
  obtain ⟨m, hm⟩ := hmem q
  have hl : intVec (lab (neg q)) = -intVec (lab q) + gramR Gz *ᵥ intVec m := by
    rw [← intVec_mulVec, ← hm, intVec_add]
    abel
  have he : intVec (lab (neg q)) ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec s) =
      -(intVec (lab q) ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec s)) + ((m ⬝ᵥ s : ℤ) : ℝ) := by
    rw [hl, add_dotProduct, neg_dotProduct, mulVec_dotProduct_inv_mulVec hGt hunit,
      intVec_dotProduct]
  have hx : (gramR Gz)⁻¹ *ᵥ intVec (lab (neg q)) =
      -((gramR Gz)⁻¹ *ᵥ intVec (lab q)) + intVec m := by
    rw [hl, mulVec_add, mulVec_neg, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  rw [he, eChar_add, eChar_intCast, mul_one, hx, hper, hev]

/-! ### Small algebraic facts -/

/-- For rank four, `(-iτ)^{4/2} = -τ²`. -/
theorem neg_I_mul_cpow_card_fin_four (τ : ℂ) :
    (-I * τ) ^ ((Fintype.card (Fin 4) : ℂ) / 2) = -τ ^ 2 := by
  have h : ((Fintype.card (Fin 4) : ℕ) : ℂ) / 2 = ((2 : ℕ) : ℂ) := by norm_num
  rw [h, Complex.cpow_natCast]
  linear_combination τ ^ 2 * I_sq

/-- `exp(πi · 2e) = e(e)`. -/
theorem cexp_pi_I_two_mul (e : ℝ) : cexp (π * I * ((2 * e : ℝ) : ℂ)) = eChar e := by
  rw [eChar]
  congr 1
  push_cast
  ring

/-- `e(x) = e(y)` when `x - y` is an integer. -/
theorem eChar_eq_of_sub_eq_int {x y : ℝ} (k : ℤ) (h : x = y + k) : eChar x = eChar y := by
  rw [h, eChar_add, eChar_intCast, mul_one]

end General

/-! ## `L₇ ⊕ A₂` (Table 1, `M3First`) -/

/-- The label `(r, s) ∈ ℤ/7 × ℤ/3` of `L'/L` as the vector
`k = G (r · 2w/7 + s · ω) = (0, r, s, 0)` (`m3First_discriminant`). -/
def labL7A2 (p : Fin 7 × Fin 3) : Fin 4 → ℤ := ![0, ((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ), 0]

/-- Smith data `U G V = diag(1, 7, 3, 1)`. -/
def smithUL7A2 : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 3, 1, 0, 0; 0, 0, 1, 2; 0, 0, 0, 1]
def smithUiL7A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; -3, 1, 0, 0; 0, 0, 1, -2; 0, 0, 0, 1]
def smithVL7A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, 0, 0; -1, 2, 0, 0; 0, 0, 2, -1; 0, 0, 1, 0]
def smithViL7A2 : Matrix (Fin 4) (Fin 4) ℤ := !![2, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 2]

theorem smith_L7A2 :
    smithUiL7A2 * smithUL7A2 = 1 ∧ smithVL7A2 * smithViL7A2 = 1 ∧
      smithUL7A2 * gramL7A2 * smithVL7A2 = diagonal ![1, 7, 3, 1] := by
  decide +kernel

theorem posDef_L7A2 : (gramR gramL7A2).PosDef := by
  refine posDef_gramR_of_coercive (by decide) (by norm_num : (0 : ℝ) < 1 / 2) fun x => ?_
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramR, gramL7A2]
  nlinarith [sq_nonneg (x 0 + 2 / 3 * x 1), sq_nonneg (x 1), sq_nonneg (x 2 - 2 / 3 * x 3),
    sq_nonneg (x 3)]

theorem even_L7A2 : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (gramL7A2 *ᵥ m)) := by
  intro m
  refine ⟨m 0 ^ 2 + m 0 * m 1 + 2 * m 1 ^ 2 + m 2 ^ 2 - m 2 * m 3 + m 3 ^ 2, ?_⟩
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramL7A2]
  ring

theorem inv_L7A2 : (gramR gramL7A2)⁻¹ = invL7A2.map (Rat.cast : ℚ → ℝ) :=
  inv_gramR_eq m3First_dual_generated.1

theorem det_L7A2 : (gramR gramL7A2).det = 21 := by
  rw [det_gramR_of_smith smith_L7A2.1 smith_L7A2.2.1 smith_L7A2.2.2 posDef_L7A2
    (by decide +kernel), show (∏ j, (![1, 7, 3, 1] : Fin 4 → ℤ) j) = 21 by decide +kernel]
  norm_num

theorem hR_L7A2 : ∀ k : Fin 4 → ℤ, ∃! p : (Finset.univ.image labL7A2) × (Fin 4 → ℤ),
    (p.1 : Fin 4 → ℤ) + gramL7A2 *ᵥ p.2 = k :=
  existsUnique_residue_of_smith smith_L7A2.1 smith_L7A2.2.1 smith_L7A2.2.2 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Coset label `(r, s)` = manuscript coset `r · 2w/7 + s · ω` (`cosetL7A2`). -/
theorem invL7A2_lab (p : Fin 7 × Fin 3) :
    invL7A2 *ᵥ (fun i => (labL7A2 p i : ℚ)) = cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ) := by
  revert p
  decide +kernel

theorem rep_L7A2 (p : Fin 7 × Fin 3) :
    (gramR gramL7A2)⁻¹ *ᵥ intVec (labL7A2 p) =
      ratVec (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ)) := by
  rw [inv_L7A2, intVec_eq_ratVec, map_ratCast_mulVec, invL7A2_lab]

/-- The `S`-matrix exponent `(γ_p, γ_q) = 2rr'/7 + 2ss'/3`. -/
def sL7A2 (p q : Fin 7 × Fin 3) : ℝ :=
  2 * ((p.1 : ℕ) : ℝ) * ((q.1 : ℕ) : ℝ) / 7 + 2 * ((p.2 : ℕ) : ℝ) * ((q.2 : ℕ) : ℝ) / 3

/-- The `T`-matrix exponent `q(γ_p) = r²/7 + s²/3`. -/
def eL7A2 (p : Fin 7 × Fin 3) : ℝ := ((p.1 : ℕ) : ℝ) ^ 2 / 7 + ((p.2 : ℕ) : ℝ) ^ 2 / 3

theorem pair_L7A2 (p q : Fin 7 × Fin 3) :
    intVec (labL7A2 q) ⬝ᵥ ratVec (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ)) = sL7A2 p q := by
  rw [intVec_eq_ratVec, ratVec_dotProduct]
  simp [labL7A2, cosetL7A2, sL7A2, dotProduct, Fin.sum_univ_four]
  ring

theorem qf_rep_L7A2 (p : Fin 7 × Fin 3) :
    qf (gramR gramL7A2) (ratVec (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ))) =
      2 * eL7A2 p := by
  rw [qf_gramR_ratVec]
  simp [cosetL7A2, gramL7A2, eL7A2, dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- `-(r, s) = (-r, -s)`. -/
def negL7A2 (p : Fin 7 × Fin 3) : Fin 7 × Fin 3 := (-p.1, -p.2)

theorem neg_L7A2 : (∀ p, negL7A2 (negL7A2 p) = p) ∧
    ∀ q j, (![1, 7, 3, 1] : Fin 4 → ℤ) j ∣
      (smithUL7A2 *ᵥ (labL7A2 (negL7A2 q) + labL7A2 q)) j := by
  decide +kernel

/-- The coset theta vector with harmonic weight `M` (e.g. `H₁`, `H₂`). -/
def thetaQL7A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 7 × Fin 3) (τ : ℂ) : ℂ :=
  latticeThetaQ (gramR gramL7A2) (M.map (Rat.cast : ℚ → ℝ))
    (ratVec (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ))) τ

/-- The coset theta vector without weight. -/
def thetaL7A2 (p : Fin 7 × Fin 3) (τ : ℂ) : ℂ :=
  latticeTheta (gramR gramL7A2) (ratVec (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ))) τ

/-- **`S`-law, `L₇ ⊕ A₂`, harmonic weight** (weight 4):
`Θ_{H,p}(-1/τ) = -τ⁴/√21 ∑_q e(-(2rr'/7 + 2ss'/3)) Θ_{H,q}(τ)`. -/
theorem thetaQL7A2_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invL7A2 M = 0)
    (p : Fin 7 × Fin 3) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQL7A2 M p (-1 / τ) =
      -((((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * τ ^ 4) *
        ∑ q, eChar (-sL7A2 p q) * thetaQL7A2 M q τ := by
  have hinj : Function.Injective labL7A2 := by decide
  have h := latticeThetaQ_S_labels posDef_L7A2 (harmonic_of_pairTrace inv_L7A2 hM) hinj
    hR_L7A2 p hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_L7A2)
    (transpose_eq_of_posDef posDef_L7A2) labL7A2 negL7A2 neg_L7A2.1
    (fun q => exists_mulVec_eq_of_dvd smith_L7A2.1 smith_L7A2.2.2 _ (neg_L7A2.2 q))
    (labL7A2 p) (fun x => latticeThetaQ (gramR gramL7A2) (M.map (Rat.cast : ℚ → ℝ)) x τ)
    (fun x k => latticeThetaQ_add_intVec _ _ x k τ) (fun x => latticeThetaQ_neg _ _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_L7A2, pair_L7A2, det_L7A2, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaQL7A2
  rw [h]
  ring

/-- **`S`-law, `L₇ ⊕ A₂`, no weight** (weight 2). -/
theorem thetaL7A2_S (p : Fin 7 × Fin 3) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaL7A2 p (-1 / τ) =
      -((((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * τ ^ 2) * ∑ q, eChar (-sL7A2 p q) * thetaL7A2 q τ := by
  have hinj : Function.Injective labL7A2 := by decide
  have h := latticeTheta_S_labels posDef_L7A2 hinj hR_L7A2 p hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_L7A2)
    (transpose_eq_of_posDef posDef_L7A2) labL7A2 negL7A2 neg_L7A2.1
    (fun q => exists_mulVec_eq_of_dvd smith_L7A2.1 smith_L7A2.2.2 _ (neg_L7A2.2 q))
    (labL7A2 p) (fun x => latticeTheta (gramR gramL7A2) x τ)
    (fun x k => latticeTheta_add_intVec _ x k τ) (fun x => latticeTheta_neg _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_L7A2, pair_L7A2, det_L7A2, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaL7A2
  rw [h]
  ring

/-- **`T`-law, `L₇ ⊕ A₂`**: `Θ_{H,p}(τ+1) = e(r²/7 + s²/3) Θ_{H,p}(τ)` (any weight `M`). -/
theorem thetaQL7A2_T (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 7 × Fin 3) (τ : ℂ) :
    thetaQL7A2 M p (τ + 1) = eChar (eL7A2 p) * thetaQL7A2 M p τ := by
  have h := latticeThetaQ_T posDef_L7A2 even_L7A2 (M.map (Rat.cast : ℚ → ℝ)) (labL7A2 p) τ
  rw [rep_L7A2, qf_rep_L7A2, cexp_pi_I_two_mul] at h
  exact h

theorem thetaL7A2_T (p : Fin 7 × Fin 3) (τ : ℂ) :
    thetaL7A2 p (τ + 1) = eChar (eL7A2 p) * thetaL7A2 p τ := by
  have h := latticeTheta_T posDef_L7A2 even_L7A2 (labL7A2 p) τ
  rw [rep_L7A2, qf_rep_L7A2, cexp_pi_I_two_mul] at h
  exact h

/-- Integer labels reduce modulo `(7, 3)`. -/
theorem ratVec_cosetL7A2_emod (r s : ℤ) :
    ratVec (cosetL7A2 r s) = ratVec (cosetL7A2 (r % 7) (s % 3)) +
      intVec ![-(r / 7), 2 * (r / 7), 2 * (s / 3), s / 3] := by
  have hr : (r : ℝ) = ((r % 7 : ℤ) : ℝ) + 7 * ((r / 7 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv r 7).symm
  have hs : (s : ℝ) = ((s % 3 : ℤ) : ℝ) + 3 * ((s / 3 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv s 3).symm
  funext i
  fin_cases i <;> simp [ratVec, intVec, cosetL7A2] <;> linarith

/-- The isometry `-1 ⊕ 1` of `L₇ ⊕ A₂` sends the coset `(r, s)` to `(-r, s)`. -/
def isoL7A2 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem iso_L7A2 : isoL7A2 * isoL7A2 = 1 ∧ isoL7A2ᵀ * gramL7A2 * isoL7A2 = gramL7A2 ∧
    (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * MH1 * isoL7A2.map (Int.cast : ℤ → ℚ) = MH1 ∧
    (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * MH2 * isoL7A2.map (Int.cast : ℤ → ℚ) = MH2 := by
  decide +kernel

theorem iso_cosetL7A2 (r s : ℤ) :
    gramR isoL7A2 *ᵥ ratVec (cosetL7A2 r s) = ratVec (cosetL7A2 (-r) s) := by
  rw [gramR_mulVec_ratVec]
  congr 1
  funext i
  fin_cases i <;> simp [isoL7A2, cosetL7A2, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- `r ↦ -r` symmetry of the `H₁`-, `H₂`-weighted coset theta series (`M3First`). -/
theorem thetaQ_cosetL7A2_neg_r {M : Matrix (Fin 4) (Fin 4) ℚ}
    (hM : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (r s : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramL7A2) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetL7A2 (-r) s)) τ =
      latticeThetaQ (gramR gramL7A2) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetL7A2 r s)) τ := by
  rw [← iso_cosetL7A2]
  exact latticeThetaQ_isometry iso_L7A2.1 iso_L7A2.1
    (gramR_transpose_mul_mul iso_L7A2.2.1) (ratCast_transpose_mul_mul hM) _ τ

/-! ## `G₇⁻` (Table 2, `M3Reverse`) -/

/-- The label `j ∈ ℤ/21` of the cyclic `L'/L = ⟨ℓ⟩`, `ℓ = e₀* = G⁻¹ e₀`, as the vector
`(j, 0, 0, 0)`.  The manuscript label `(r, s)` is `j ≡ 9r + 7s` (`cosetG7m_eq`,
`ratVec_repG7m_emod`). -/
def labG7m (j : Fin 21) : Fin 4 → ℤ := ![((j : ℕ) : ℤ), 0, 0, 0]

/-- The coset representative `t ℓ`. -/
def repG7m (t : ℤ) : Fin 4 → ℚ := fun i => (t : ℚ) * ellG7m i

theorem cosetG7m_eq (r s : ℤ) : cosetG7m r s = repG7m (9 * r + 7 * s) := rfl

/-- Smith data `U G V = diag(21, 1, 1, 1)`. -/
def smithUG7m : Matrix (Fin 4) (Fin 4) ℤ := !![1, 2, 3, 4; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def smithUiG7m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -2, -3, -4; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def smithVG7m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![16, -1, -2, -3; 11, 0, -1, -2; 6, 0, 0, -1; 1, 0, 0, 0]
def smithViG7m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 6]

theorem smith_G7m :
    smithUiG7m * smithUG7m = 1 ∧ smithVG7m * smithViG7m = 1 ∧
      smithUG7m * gramG7m * smithVG7m = diagonal ![21, 1, 1, 1] := by
  decide +kernel

theorem posDef_G7m : (gramR gramG7m).PosDef := by
  refine posDef_gramR_of_coercive (by decide) (by norm_num : (0 : ℝ) < 1 / 2) fun x => ?_
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramR, gramG7m]
  nlinarith [sq_nonneg (x 0 - 2 / 3 * x 1), sq_nonneg (x 1 - 6 / 5 * x 2),
    sq_nonneg (x 2 - 10 / 3 * x 3), sq_nonneg (x 3)]

theorem even_G7m : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (gramG7m *ᵥ m)) := by
  intro m
  refine ⟨m 0 ^ 2 - m 0 * m 1 + m 1 ^ 2 - m 1 * m 2 + m 2 ^ 2 - m 2 * m 3 + 3 * m 3 ^ 2, ?_⟩
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramG7m]
  ring

theorem inv_G7m : (gramR gramG7m)⁻¹ = invG7m.map (Rat.cast : ℚ → ℝ) :=
  inv_gramR_eq m3Reverse_dual_cyclic.1

theorem det_G7m : (gramR gramG7m).det = 21 := by
  rw [det_gramR_of_smith smith_G7m.1 smith_G7m.2.1 smith_G7m.2.2 posDef_G7m
    (by decide +kernel), show (∏ j, (![21, 1, 1, 1] : Fin 4 → ℤ) j) = 21 by decide +kernel]
  norm_num

theorem hR_G7m : ∀ k : Fin 4 → ℤ, ∃! p : (Finset.univ.image labG7m) × (Fin 4 → ℤ),
    (p.1 : Fin 4 → ℤ) + gramG7m *ᵥ p.2 = k :=
  existsUnique_residue_of_smith smith_G7m.1 smith_G7m.2.1 smith_G7m.2.2 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem invG7m_lab (j : Fin 21) :
    invG7m *ᵥ (fun i => (labG7m j i : ℚ)) = repG7m ((j : ℕ) : ℤ) := by
  revert j
  decide +kernel

theorem rep_G7m (j : Fin 21) :
    (gramR gramG7m)⁻¹ *ᵥ intVec (labG7m j) = ratVec (repG7m ((j : ℕ) : ℤ)) := by
  rw [inv_G7m, intVec_eq_ratVec, map_ratCast_mulVec, invG7m_lab]

/-- The `S`-matrix exponent `(jℓ, kℓ) = 16jk/21`. -/
def sG7m (j k : Fin 21) : ℝ := 16 * ((j : ℕ) : ℝ) * ((k : ℕ) : ℝ) / 21

/-- The `T`-matrix exponent `q(jℓ) = 8j²/21`. -/
def eG7m (j : Fin 21) : ℝ := 8 * ((j : ℕ) : ℝ) ^ 2 / 21

theorem pair_G7m (j k : Fin 21) :
    intVec (labG7m k) ⬝ᵥ ratVec (repG7m ((j : ℕ) : ℤ)) = sG7m j k := by
  rw [intVec_eq_ratVec, ratVec_dotProduct]
  simp [labG7m, repG7m, ellG7m, sG7m, dotProduct, Fin.sum_univ_four]
  ring

theorem qf_rep_G7m (j : Fin 21) :
    qf (gramR gramG7m) (ratVec (repG7m ((j : ℕ) : ℤ))) = 2 * eG7m j := by
  rw [qf_gramR_ratVec]
  simp [repG7m, ellG7m, gramG7m, eG7m, dotProduct, mulVec, Fin.sum_univ_four]
  ring

def negG7m (j : Fin 21) : Fin 21 := -j

theorem neg_G7m : (∀ j, negG7m (negG7m j) = j) ∧
    ∀ q j, (![21, 1, 1, 1] : Fin 4 → ℤ) j ∣
      (smithUG7m *ᵥ (labG7m (negG7m q) + labG7m q)) j := by
  decide +kernel

def thetaQG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (j : Fin 21) (τ : ℂ) : ℂ :=
  latticeThetaQ (gramR gramG7m) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (repG7m ((j : ℕ) : ℤ))) τ

def thetaG7m (j : Fin 21) (τ : ℂ) : ℂ :=
  latticeTheta (gramR gramG7m) (ratVec (repG7m ((j : ℕ) : ℤ))) τ

/-- **`S`-law, `G₇⁻`, harmonic weight**:
`Θ_{H,j}(-1/τ) = -τ⁴/√21 ∑_k e(-16jk/21) Θ_{H,k}(τ)`. -/
theorem thetaQG7m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0)
    (j : Fin 21) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG7m M j (-1 / τ) =
      -((((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * τ ^ 4) * ∑ k, eChar (-sG7m j k) * thetaQG7m M k τ := by
  have hinj : Function.Injective labG7m := by decide
  have h := latticeThetaQ_S_labels posDef_G7m (harmonic_of_pairTrace inv_G7m hM) hinj
    hR_G7m j hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_G7m)
    (transpose_eq_of_posDef posDef_G7m) labG7m negG7m neg_G7m.1
    (fun q => exists_mulVec_eq_of_dvd smith_G7m.1 smith_G7m.2.2 _ (neg_G7m.2 q))
    (labG7m j) (fun x => latticeThetaQ (gramR gramG7m) (M.map (Rat.cast : ℚ → ℝ)) x τ)
    (fun x k => latticeThetaQ_add_intVec _ _ x k τ) (fun x => latticeThetaQ_neg _ _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_G7m, pair_G7m, det_G7m, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaQG7m
  rw [h]
  ring

/-- **`S`-law, `G₇⁻`, no weight**. -/
theorem thetaG7m_S (j : Fin 21) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaG7m j (-1 / τ) =
      -((((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * τ ^ 2) * ∑ k, eChar (-sG7m j k) * thetaG7m k τ := by
  have hinj : Function.Injective labG7m := by decide
  have h := latticeTheta_S_labels posDef_G7m hinj hR_G7m j hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_G7m)
    (transpose_eq_of_posDef posDef_G7m) labG7m negG7m neg_G7m.1
    (fun q => exists_mulVec_eq_of_dvd smith_G7m.1 smith_G7m.2.2 _ (neg_G7m.2 q))
    (labG7m j) (fun x => latticeTheta (gramR gramG7m) x τ)
    (fun x k => latticeTheta_add_intVec _ x k τ) (fun x => latticeTheta_neg _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_G7m, pair_G7m, det_G7m, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaG7m
  rw [h]
  ring

/-- **`T`-law, `G₇⁻`**: `Θ_{H,j}(τ+1) = e(8j²/21) Θ_{H,j}(τ)`. -/
theorem thetaQG7m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (j : Fin 21) (τ : ℂ) :
    thetaQG7m M j (τ + 1) = eChar (eG7m j) * thetaQG7m M j τ := by
  have h := latticeThetaQ_T posDef_G7m even_G7m (M.map (Rat.cast : ℚ → ℝ)) (labG7m j) τ
  rw [rep_G7m, qf_rep_G7m, cexp_pi_I_two_mul] at h
  exact h

theorem thetaG7m_T (j : Fin 21) (τ : ℂ) :
    thetaG7m j (τ + 1) = eChar (eG7m j) * thetaG7m j τ := by
  have h := latticeTheta_T posDef_G7m even_G7m (labG7m j) τ
  rw [rep_G7m, qf_rep_G7m, cexp_pi_I_two_mul] at h
  exact h

/-- Integer labels reduce modulo `21` (`21 ℓ = (16, 11, 6, 1) ∈ ℤ⁴`). -/
theorem ratVec_repG7m_emod (t : ℤ) :
    ratVec (repG7m t) = ratVec (repG7m (t % 21)) +
      intVec ![16 * (t / 21), 11 * (t / 21), 6 * (t / 21), t / 21] := by
  have ht : (t : ℝ) = ((t % 21 : ℤ) : ℝ) + 21 * ((t / 21 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv t 21).symm
  funext i
  fin_cases i <;> simp [ratVec, intVec, repG7m, ellG7m] <;> linarith

/-- The isometry `(r, s) ↦ (-r, s)` of the discriminant form, `j ↦ 13 j` on `ℤ/21`
(`13 ≡ -1 (mod 7)`, `13 ≡ 1 (mod 3)`), preserves the `S`- and `T`-exponents modulo `1`. -/
def oG7m (j : Fin 21) : Fin 21 := 13 * j

theorem oG7m_data : (∀ j, oG7m (oG7m j) = j) ∧
    (∀ j k, (21 : ℤ) ∣ 16 * ((oG7m j : ℕ) : ℤ) * ((oG7m k : ℕ) : ℤ) -
      16 * ((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) ∧
    (∀ j, (21 : ℤ) ∣ 8 * ((oG7m j : ℕ) : ℤ) ^ 2 - 8 * ((j : ℕ) : ℤ) ^ 2) := by
  decide +kernel

theorem eChar_sG7m_o (j k : Fin 21) : eChar (-sG7m (oG7m j) (oG7m k)) = eChar (-sG7m j k) := by
  obtain ⟨c, hc⟩ := oG7m_data.2.1 j k
  refine eChar_eq_of_sub_eq_int (-c) ?_
  have hc' : (16 * ((oG7m j : ℕ) : ℝ) * ((oG7m k : ℕ) : ℝ) - 16 * ((j : ℕ) : ℝ) * ((k : ℕ) : ℝ)) =
      21 * (c : ℝ) := by exact_mod_cast hc
  simp only [sG7m]
  push_cast
  linarith

theorem eChar_eG7m_o (j : Fin 21) : eChar (eG7m (oG7m j)) = eChar (eG7m j) := by
  obtain ⟨c, hc⟩ := oG7m_data.2.2 j
  refine eChar_eq_of_sub_eq_int c ?_
  have hc' : (8 * ((oG7m j : ℕ) : ℝ) ^ 2 - 8 * ((j : ℕ) : ℝ) ^ 2) = 21 * (c : ℝ) := by
    exact_mod_cast hc
  simp only [eG7m]
  linarith

/-- **`O(D)`-equivariance, `G₇⁻`**: the vector `(Θ_{H, 13j})_j` (the coset labels with
`r ↦ -r`) satisfies the same `S`-law as `(Θ_{H,j})_j`; together with `thetaQG7m_T` and
`eChar_eG7m_o` the same holds for `T`.  Hence the projection to functions even in `r`
(average of the two vectors) transforms by the same matrices. -/
theorem thetaQG7m_S_o {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0)
    (j : Fin 21) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG7m M (oG7m j) (-1 / τ) =
      -((((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * τ ^ 4) *
        ∑ k, eChar (-sG7m j k) * thetaQG7m M (oG7m k) τ := by
  rw [thetaQG7m_S hM (oG7m j) hτ]
  congr 1
  refine (Fintype.sum_equiv (⟨oG7m, oG7m, oG7m_data.1, oG7m_data.1⟩ : Fin 21 ≃ Fin 21) _ _
    fun k => ?_).symm
  show _ = eChar (-sG7m (oG7m j) (oG7m k)) * thetaQG7m M (oG7m k) τ
  rw [eChar_sG7m_o]

theorem thetaQG7m_T_o (M : Matrix (Fin 4) (Fin 4) ℚ) (j : Fin 21) (τ : ℂ) :
    thetaQG7m M (oG7m j) (τ + 1) = eChar (eG7m j) * thetaQG7m M (oG7m j) τ := by
  rw [thetaQG7m_T, eChar_eG7m_o]

theorem thetaG7m_S_o (j : Fin 21) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaG7m (oG7m j) (-1 / τ) =
      -((((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * τ ^ 2) * ∑ k, eChar (-sG7m j k) * thetaG7m (oG7m k) τ := by
  rw [thetaG7m_S (oG7m j) hτ]
  congr 1
  refine (Fintype.sum_equiv (⟨oG7m, oG7m, oG7m_data.1, oG7m_data.1⟩ : Fin 21 ≃ Fin 21) _ _
    fun k => ?_).symm
  show _ = eChar (-sG7m (oG7m j) (oG7m k)) * thetaG7m (oG7m k) τ
  rw [eChar_sG7m_o]

/-! ## `A₁ ⊕ A₁ ⊕ A₂` (Table 3, `M6First`) -/

/-- The label `(a, b, s) ∈ ℤ/2 × ℤ/2 × ℤ/3` as the vector `G (a α/2, b α'/2, s ω) = (a, b, s, 0)`. -/
def labA1A1A2 (p : Fin 2 × Fin 2 × Fin 3) : Fin 4 → ℤ :=
  ![((p.1 : ℕ) : ℤ), ((p.2.1 : ℕ) : ℤ), ((p.2.2 : ℕ) : ℤ), 0]

def smithUA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 2; 0, 0, 0, 1]
def smithUiA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, -2; 0, 0, 0, 1]
def smithVA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, -1; 0, 0, 1, 0]
def smithViA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 2]

theorem smith_A1A1A2 :
    smithUiA1A1A2 * smithUA1A1A2 = 1 ∧ smithVA1A1A2 * smithViA1A1A2 = 1 ∧
      smithUA1A1A2 * gramA1A1A2 * smithVA1A1A2 = diagonal ![2, 2, 3, 1] := by
  decide +kernel

theorem posDef_A1A1A2 : (gramR gramA1A1A2).PosDef := by
  refine posDef_gramR_of_coercive (by decide) (by norm_num : (0 : ℝ) < 1 / 2) fun x => ?_
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramR, gramA1A1A2]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2 - 2 / 3 * x 3), sq_nonneg (x 3)]

theorem even_A1A1A2 : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (gramA1A1A2 *ᵥ m)) := by
  intro m
  refine ⟨m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 - m 2 * m 3 + m 3 ^ 2, ?_⟩
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramA1A1A2]
  ring

theorem inv_A1A1A2 : (gramR gramA1A1A2)⁻¹ = invA1A1A2.map (Rat.cast : ℚ → ℝ) :=
  inv_gramR_eq harmonic_quadratics.1

theorem det_A1A1A2 : (gramR gramA1A1A2).det = 12 := by
  rw [det_gramR_of_smith smith_A1A1A2.1 smith_A1A1A2.2.1 smith_A1A1A2.2.2 posDef_A1A1A2
    (by decide +kernel), show (∏ j, (![2, 2, 3, 1] : Fin 4 → ℤ) j) = 12 by decide +kernel]
  norm_num

theorem hR_A1A1A2 : ∀ k : Fin 4 → ℤ, ∃! p : (Finset.univ.image labA1A1A2) × (Fin 4 → ℤ),
    (p.1 : Fin 4 → ℤ) + gramA1A1A2 *ᵥ p.2 = k :=
  existsUnique_residue_of_smith smith_A1A1A2.1 smith_A1A1A2.2.1 smith_A1A1A2.2.2 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem invA1A1A2_lab (p : Fin 2 × Fin 2 × Fin 3) :
    invA1A1A2 *ᵥ (fun i => (labA1A1A2 p i : ℚ)) =
      cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ) := by
  revert p
  decide +kernel

theorem rep_A1A1A2 (p : Fin 2 × Fin 2 × Fin 3) :
    (gramR gramA1A1A2)⁻¹ *ᵥ intVec (labA1A1A2 p) =
      ratVec (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) := by
  rw [inv_A1A1A2, intVec_eq_ratVec, map_ratCast_mulVec, invA1A1A2_lab]

/-- The `S`-matrix exponent `aa'/2 + bb'/2 + 2ss'/3`. -/
def sA1A1A2 (p q : Fin 2 × Fin 2 × Fin 3) : ℝ :=
  ((p.1 : ℕ) : ℝ) * ((q.1 : ℕ) : ℝ) / 2 + ((p.2.1 : ℕ) : ℝ) * ((q.2.1 : ℕ) : ℝ) / 2 +
    2 * ((p.2.2 : ℕ) : ℝ) * ((q.2.2 : ℕ) : ℝ) / 3

/-- The `T`-matrix exponent `a²/4 + b²/4 + s²/3`. -/
def eA1A1A2 (p : Fin 2 × Fin 2 × Fin 3) : ℝ :=
  ((p.1 : ℕ) : ℝ) ^ 2 / 4 + ((p.2.1 : ℕ) : ℝ) ^ 2 / 4 + ((p.2.2 : ℕ) : ℝ) ^ 2 / 3

theorem pair_A1A1A2 (p q : Fin 2 × Fin 2 × Fin 3) :
    intVec (labA1A1A2 q) ⬝ᵥ
        ratVec (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) =
      sA1A1A2 p q := by
  rw [intVec_eq_ratVec, ratVec_dotProduct]
  simp [labA1A1A2, cosetA1A1A2, sA1A1A2, dotProduct, Fin.sum_univ_four]
  ring

theorem qf_rep_A1A1A2 (p : Fin 2 × Fin 2 × Fin 3) :
    qf (gramR gramA1A1A2)
        (ratVec (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) =
      2 * eA1A1A2 p := by
  rw [qf_gramR_ratVec]
  simp [cosetA1A1A2, gramA1A1A2, eA1A1A2, dotProduct, mulVec, Fin.sum_univ_four]
  ring

def negA1A1A2 (p : Fin 2 × Fin 2 × Fin 3) : Fin 2 × Fin 2 × Fin 3 := (-p.1, -p.2.1, -p.2.2)

theorem neg_A1A1A2 : (∀ p, negA1A1A2 (negA1A1A2 p) = p) ∧
    ∀ q j, (![2, 2, 3, 1] : Fin 4 → ℤ) j ∣
      (smithUA1A1A2 *ᵥ (labA1A1A2 (negA1A1A2 q) + labA1A1A2 q)) j := by
  decide +kernel

def thetaQA1A1A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) : ℂ :=
  latticeThetaQ (gramR gramA1A1A2) (M.map (Rat.cast : ℚ → ℝ))
    (ratVec (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) τ

def thetaA1A1A2 (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) : ℂ :=
  latticeTheta (gramR gramA1A1A2)
    (ratVec (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) τ

/-- **`S`-law, `A₁ ⊕ A₁ ⊕ A₂`, harmonic weight**:
`Θ_{H,p}(-1/τ) = -τ⁴/√12 ∑_q e(-(aa'/2 + bb'/2 + 2ss'/3)) Θ_{H,q}(τ)`. -/
theorem thetaQA1A1A2_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invA1A1A2 M = 0)
    (p : Fin 2 × Fin 2 × Fin 3) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQA1A1A2 M p (-1 / τ) =
      -((((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * τ ^ 4) *
        ∑ q, eChar (-sA1A1A2 p q) * thetaQA1A1A2 M q τ := by
  have hinj : Function.Injective labA1A1A2 := by decide
  have h := latticeThetaQ_S_labels posDef_A1A1A2 (harmonic_of_pairTrace inv_A1A1A2 hM) hinj
    hR_A1A1A2 p hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_A1A1A2)
    (transpose_eq_of_posDef posDef_A1A1A2) labA1A1A2 negA1A1A2 neg_A1A1A2.1
    (fun q => exists_mulVec_eq_of_dvd smith_A1A1A2.1 smith_A1A1A2.2.2 _ (neg_A1A1A2.2 q))
    (labA1A1A2 p) (fun x => latticeThetaQ (gramR gramA1A1A2) (M.map (Rat.cast : ℚ → ℝ)) x τ)
    (fun x k => latticeThetaQ_add_intVec _ _ x k τ) (fun x => latticeThetaQ_neg _ _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_A1A1A2, pair_A1A1A2, det_A1A1A2, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaQA1A1A2
  rw [h]
  ring

theorem thetaA1A1A2_S (p : Fin 2 × Fin 2 × Fin 3) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaA1A1A2 p (-1 / τ) =
      -((((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * τ ^ 2) *
        ∑ q, eChar (-sA1A1A2 p q) * thetaA1A1A2 q τ := by
  have hinj : Function.Injective labA1A1A2 := by decide
  have h := latticeTheta_S_labels posDef_A1A1A2 hinj hR_A1A1A2 p hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_A1A1A2)
    (transpose_eq_of_posDef posDef_A1A1A2) labA1A1A2 negA1A1A2 neg_A1A1A2.1
    (fun q => exists_mulVec_eq_of_dvd smith_A1A1A2.1 smith_A1A1A2.2.2 _ (neg_A1A1A2.2 q))
    (labA1A1A2 p) (fun x => latticeTheta (gramR gramA1A1A2) x τ)
    (fun x k => latticeTheta_add_intVec _ x k τ) (fun x => latticeTheta_neg _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_A1A1A2, pair_A1A1A2, det_A1A1A2, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaA1A1A2
  rw [h]
  ring

theorem thetaQA1A1A2_T (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQA1A1A2 M p (τ + 1) = eChar (eA1A1A2 p) * thetaQA1A1A2 M p τ := by
  have h := latticeThetaQ_T posDef_A1A1A2 even_A1A1A2 (M.map (Rat.cast : ℚ → ℝ))
    (labA1A1A2 p) τ
  rw [rep_A1A1A2, qf_rep_A1A1A2, cexp_pi_I_two_mul] at h
  exact h

theorem thetaA1A1A2_T (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaA1A1A2 p (τ + 1) = eChar (eA1A1A2 p) * thetaA1A1A2 p τ := by
  have h := latticeTheta_T posDef_A1A1A2 even_A1A1A2 (labA1A1A2 p) τ
  rw [rep_A1A1A2, qf_rep_A1A1A2, cexp_pi_I_two_mul] at h
  exact h

theorem ratVec_cosetA1A1A2_emod (a b s : ℤ) :
    ratVec (cosetA1A1A2 a b s) = ratVec (cosetA1A1A2 (a % 2) (b % 2) (s % 3)) +
      intVec ![a / 2, b / 2, 2 * (s / 3), s / 3] := by
  have ha : (a : ℝ) = ((a % 2 : ℤ) : ℝ) + 2 * ((a / 2 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a 2).symm
  have hb : (b : ℝ) = ((b % 2 : ℤ) : ℝ) + 2 * ((b / 2 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b 2).symm
  have hs : (s : ℝ) = ((s % 3 : ℤ) : ℝ) + 3 * ((s / 3 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv s 3).symm
  funext i
  fin_cases i <;> simp [ratVec, intVec, cosetA1A1A2] <;> linarith

/-- The interchange of the two `A₁` factors and the conjugation of the `A₂` charge. -/
def swapA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def conjA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

theorem iso_A1A1A2 :
    swapA1A1A2 * swapA1A1A2 = 1 ∧ swapA1A1A2ᵀ * gramA1A1A2 * swapA1A1A2 = gramA1A1A2 ∧
    (swapA1A1A2.map (Int.cast : ℤ → ℚ))ᵀ * MHA1A1A2 * swapA1A1A2.map (Int.cast : ℤ → ℚ) =
      MHA1A1A2 ∧
    conjA1A1A2 * conjA1A1A2 = 1 ∧ conjA1A1A2ᵀ * gramA1A1A2 * conjA1A1A2 = gramA1A1A2 ∧
    (conjA1A1A2.map (Int.cast : ℤ → ℚ))ᵀ * MHA1A1A2 * conjA1A1A2.map (Int.cast : ℤ → ℚ) =
      MHA1A1A2 := by
  decide +kernel

theorem swap_cosetA1A1A2 (a b s : ℤ) :
    gramR swapA1A1A2 *ᵥ ratVec (cosetA1A1A2 a b s) = ratVec (cosetA1A1A2 b a s) := by
  rw [gramR_mulVec_ratVec]
  congr 1
  funext i
  fin_cases i <;> simp [swapA1A1A2, cosetA1A1A2, mulVec, dotProduct, Fin.sum_univ_four]

theorem conj_cosetA1A1A2 (a b s : ℤ) :
    gramR conjA1A1A2 *ᵥ ratVec (cosetA1A1A2 a b s) = ratVec (cosetA1A1A2 a b (-s)) := by
  rw [gramR_mulVec_ratVec]
  congr 1
  funext i
  fin_cases i <;> simp [conjA1A1A2, cosetA1A1A2, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The symmetries of `symA1A1A2` (`M6First`): `(a, b, s) ↦ (b, a, s)` and `(a, b, -s)`. -/
theorem thetaQ_cosetA1A1A2_swap (a b s : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramA1A1A2) (MHA1A1A2.map (Rat.cast : ℚ → ℝ))
        (ratVec (cosetA1A1A2 b a s)) τ =
      latticeThetaQ (gramR gramA1A1A2) (MHA1A1A2.map (Rat.cast : ℚ → ℝ))
        (ratVec (cosetA1A1A2 a b s)) τ := by
  rw [← swap_cosetA1A1A2]
  exact latticeThetaQ_isometry iso_A1A1A2.1 iso_A1A1A2.1
    (gramR_transpose_mul_mul iso_A1A1A2.2.1) (ratCast_transpose_mul_mul iso_A1A1A2.2.2.1) _ τ

theorem thetaQ_cosetA1A1A2_conj (a b s : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramA1A1A2) (MHA1A1A2.map (Rat.cast : ℚ → ℝ))
        (ratVec (cosetA1A1A2 a b (-s))) τ =
      latticeThetaQ (gramR gramA1A1A2) (MHA1A1A2.map (Rat.cast : ℚ → ℝ))
        (ratVec (cosetA1A1A2 a b s)) τ := by
  rw [← conj_cosetA1A1A2]
  exact latticeThetaQ_isometry iso_A1A1A2.2.2.2.1 iso_A1A1A2.2.2.2.1
    (gramR_transpose_mul_mul iso_A1A1A2.2.2.2.2.1)
    (ratCast_transpose_mul_mul iso_A1A1A2.2.2.2.2.2) _ τ

/-! ## `G₆⁻` (Table 4, `M6Reverse`) -/

/-- The coset `a d₁ + b d₂ + t d₃' + L` (`d₃' = d₃ - e₃ ≡ d₃`), in coordinates. -/
def cosetG6m (a b t : ℤ) : Fin 4 → ℚ :=
  ![2 * (t : ℚ) / 3, (a : ℚ) / 2 + (t : ℚ) / 3, (b : ℚ) / 2 + (t : ℚ) / 3,
    (a : ℚ) / 2 + (b : ℚ) / 2 - (t : ℚ) / 3]

/-- The label `(a, b, t) ∈ ℤ/2 × ℤ/2 × ℤ/3` of `L'/L = ⟨d₁, d₂, d₃⟩` as the vector
`G (a d₁ + b d₂ + t d₃') = a (-1,1,0,2) + b (-1,0,1,2) + t (1,0,0,-2)`. -/
def labG6m (p : Fin 2 × Fin 2 × Fin 3) : Fin 4 → ℤ :=
  ![-((p.1 : ℕ) : ℤ) - ((p.2.1 : ℕ) : ℤ) + ((p.2.2 : ℕ) : ℤ), ((p.1 : ℕ) : ℤ),
    ((p.2.1 : ℕ) : ℤ), 2 * ((p.1 : ℕ) : ℤ) + 2 * ((p.2.1 : ℕ) : ℤ) - 2 * ((p.2.2 : ℕ) : ℤ)]

def smithUG6m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-2, 1, 0, -1; 2, 0, 1, 1; -1, 1, 1, -1; -2, 0, 0, -1]
def smithUiG6m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1, -1, 1, -1; 1, 0, 0, -1; 0, 1, 0, 1; 2, 2, -2, 1]
def smithVG6m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 2, -1; 1, 0, 1, -1; 0, 1, 1, 0; 1, 1, -1, 0]
def smithViG6m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-2, 2, 1, -1; 1, -1, 0, 1; -1, 1, 1, -1; -3, 2, 2, -2]

theorem smith_G6m :
    smithUiG6m * smithUG6m = 1 ∧ smithVG6m * smithViG6m = 1 ∧
      smithUG6m * gramG6m * smithVG6m = diagonal ![2, 2, 3, 1] := by
  decide +kernel

theorem posDef_G6m : (gramR gramG6m).PosDef := by
  refine posDef_gramR_of_coercive (by decide) (by norm_num : (0 : ℝ) < 1 / 4) fun x => ?_
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramR, gramG6m]
  nlinarith [sq_nonneg (x 0 - 4 / 7 * (x 1 + x 2 + x 3)), sq_nonneg (x 1 - 16 / 33 * (x 2 + x 3)),
    sq_nonneg (x 2 - 16 / 17 * x 3), sq_nonneg (x 3)]

theorem even_G6m : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (gramG6m *ᵥ m)) := by
  intro m
  refine ⟨m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 + 2 * m 3 ^ 2 - m 0 * m 1 - m 0 * m 2 - m 0 * m 3, ?_⟩
  simp only [dotProduct, mulVec, Fin.sum_univ_four]
  simp [gramG6m]
  ring

theorem inv_G6m : (gramR gramG6m)⁻¹ = invG6m.map (Rat.cast : ℚ → ℝ) :=
  inv_gramR_eq m6Reverse_dual_generated.1

theorem det_G6m : (gramR gramG6m).det = 12 := by
  rw [det_gramR_of_smith smith_G6m.1 smith_G6m.2.1 smith_G6m.2.2 posDef_G6m
    (by decide +kernel), show (∏ j, (![2, 2, 3, 1] : Fin 4 → ℤ) j) = 12 by decide +kernel]
  norm_num

theorem hR_G6m : ∀ k : Fin 4 → ℤ, ∃! p : (Finset.univ.image labG6m) × (Fin 4 → ℤ),
    (p.1 : Fin 4 → ℤ) + gramG6m *ᵥ p.2 = k :=
  existsUnique_residue_of_smith smith_G6m.1 smith_G6m.2.1 smith_G6m.2.2 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem invG6m_lab (p : Fin 2 × Fin 2 × Fin 3) :
    invG6m *ᵥ (fun i => (labG6m p i : ℚ)) =
      cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ) := by
  revert p
  decide +kernel

theorem rep_G6m (p : Fin 2 × Fin 2 × Fin 3) :
    (gramR gramG6m)⁻¹ *ᵥ intVec (labG6m p) =
      ratVec (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) := by
  rw [inv_G6m, intVec_eq_ratVec, map_ratCast_mulVec, invG6m_lab]

/-- The `S`-matrix exponent, from `(dᵢ, dᵢ) = 3/2`, `(d₃', d₃') = 4/3`, `(d₁, d₂) = 1`,
`(dᵢ, d₃') = -1`. -/
def sG6m (p q : Fin 2 × Fin 2 × Fin 3) : ℝ :=
  3 / 2 * ((p.1 : ℕ) : ℝ) * ((q.1 : ℕ) : ℝ) + 3 / 2 * ((p.2.1 : ℕ) : ℝ) * ((q.2.1 : ℕ) : ℝ) +
    4 / 3 * ((p.2.2 : ℕ) : ℝ) * ((q.2.2 : ℕ) : ℝ) +
    (((p.1 : ℕ) : ℝ) * ((q.2.1 : ℕ) : ℝ) + ((p.2.1 : ℕ) : ℝ) * ((q.1 : ℕ) : ℝ)) -
    (((p.1 : ℕ) : ℝ) * ((q.2.2 : ℕ) : ℝ) + ((p.2.2 : ℕ) : ℝ) * ((q.1 : ℕ) : ℝ)) -
    (((p.2.1 : ℕ) : ℝ) * ((q.2.2 : ℕ) : ℝ) + ((p.2.2 : ℕ) : ℝ) * ((q.2.1 : ℕ) : ℝ))

/-- The `T`-matrix exponent `q = 3a²/4 + 3b²/4 + 2t²/3 + ab - at - bt`. -/
def eG6m (p : Fin 2 × Fin 2 × Fin 3) : ℝ :=
  3 / 4 * ((p.1 : ℕ) : ℝ) ^ 2 + 3 / 4 * ((p.2.1 : ℕ) : ℝ) ^ 2 + 2 / 3 * ((p.2.2 : ℕ) : ℝ) ^ 2 +
    ((p.1 : ℕ) : ℝ) * ((p.2.1 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ) * ((p.2.2 : ℕ) : ℝ) -
    ((p.2.1 : ℕ) : ℝ) * ((p.2.2 : ℕ) : ℝ)

theorem pair_G6m (p q : Fin 2 × Fin 2 × Fin 3) :
    intVec (labG6m q) ⬝ᵥ ratVec (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) =
      sG6m p q := by
  rw [intVec_eq_ratVec, ratVec_dotProduct]
  simp [labG6m, cosetG6m, sG6m, dotProduct, Fin.sum_univ_four]
  ring

theorem qf_rep_G6m (p : Fin 2 × Fin 2 × Fin 3) :
    qf (gramR gramG6m) (ratVec (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) =
      2 * eG6m p := by
  rw [qf_gramR_ratVec]
  simp [cosetG6m, gramG6m, eG6m, dotProduct, mulVec, Fin.sum_univ_four]
  ring

def negG6m (p : Fin 2 × Fin 2 × Fin 3) : Fin 2 × Fin 2 × Fin 3 := (-p.1, -p.2.1, -p.2.2)

theorem neg_G6m : (∀ p, negG6m (negG6m p) = p) ∧
    ∀ q j, (![2, 2, 3, 1] : Fin 4 → ℤ) j ∣
      (smithUG6m *ᵥ (labG6m (negG6m q) + labG6m q)) j := by
  decide +kernel

def thetaQG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) : ℂ :=
  latticeThetaQ (gramR gramG6m) (M.map (Rat.cast : ℚ → ℝ))
    (ratVec (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) τ

def thetaG6m (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) : ℂ :=
  latticeTheta (gramR gramG6m)
    (ratVec (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) τ

/-- **`S`-law, `G₆⁻`, harmonic weight**:
`Θ_{H,p}(-1/τ) = -τ⁴/√12 ∑_q e(-(γ_p, γ_q)) Θ_{H,q}(τ)`. -/
theorem thetaQG6m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG6m M = 0)
    (p : Fin 2 × Fin 2 × Fin 3) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG6m M p (-1 / τ) =
      -((((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * τ ^ 4) * ∑ q, eChar (-sG6m p q) * thetaQG6m M q τ := by
  have hinj : Function.Injective labG6m := by decide
  have h := latticeThetaQ_S_labels posDef_G6m (harmonic_of_pairTrace inv_G6m hM) hinj
    hR_G6m p hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_G6m)
    (transpose_eq_of_posDef posDef_G6m) labG6m negG6m neg_G6m.1
    (fun q => exists_mulVec_eq_of_dvd smith_G6m.1 smith_G6m.2.2 _ (neg_G6m.2 q))
    (labG6m p) (fun x => latticeThetaQ (gramR gramG6m) (M.map (Rat.cast : ℚ → ℝ)) x τ)
    (fun x k => latticeThetaQ_add_intVec _ _ x k τ) (fun x => latticeThetaQ_neg _ _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_G6m, pair_G6m, det_G6m, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaQG6m
  rw [h]
  ring

theorem thetaG6m_S (p : Fin 2 × Fin 2 × Fin 3) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaG6m p (-1 / τ) =
      -((((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * τ ^ 2) * ∑ q, eChar (-sG6m p q) * thetaG6m q τ := by
  have hinj : Function.Injective labG6m := by decide
  have h := latticeTheta_S_labels posDef_G6m hinj hR_G6m p hτ
  have hneg := sum_eChar_neg_of_involutive (isUnit_det_of_posDef posDef_G6m)
    (transpose_eq_of_posDef posDef_G6m) labG6m negG6m neg_G6m.1
    (fun q => exists_mulVec_eq_of_dvd smith_G6m.1 smith_G6m.2.2 _ (neg_G6m.2 q))
    (labG6m p) (fun x => latticeTheta (gramR gramG6m) x τ)
    (fun x k => latticeTheta_add_intVec _ x k τ) (fun x => latticeTheta_neg _ x τ)
  beta_reduce at hneg
  rw [hneg] at h
  simp only [rep_G6m, pair_G6m, det_G6m, neg_I_mul_cpow_card_fin_four] at h
  unfold thetaG6m
  rw [h]
  ring

theorem thetaQG6m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQG6m M p (τ + 1) = eChar (eG6m p) * thetaQG6m M p τ := by
  have h := latticeThetaQ_T posDef_G6m even_G6m (M.map (Rat.cast : ℚ → ℝ)) (labG6m p) τ
  rw [rep_G6m, qf_rep_G6m, cexp_pi_I_two_mul] at h
  exact h

theorem thetaG6m_T (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaG6m p (τ + 1) = eChar (eG6m p) * thetaG6m p τ := by
  have h := latticeTheta_T posDef_G6m even_G6m (labG6m p) τ
  rw [rep_G6m, qf_rep_G6m, cexp_pi_I_two_mul] at h
  exact h

/-- The manuscript's representatives: the vacuum coset `L` is the label `(0,0,0)`, and the
polar coset `-w/3 + L` is the label `(1,1,1)`. -/
theorem cosetG6m_zero : cosetG6m 0 0 0 = 0 := by
  funext i
  fin_cases i <;> simp [cosetG6m]

theorem ratVec_polarG6m : ratVec polarG6m = ratVec (cosetG6m 1 1 1) + intVec ![-1, -1, -1, -1] := by
  funext i
  fin_cases i <;> simp [ratVec, intVec, polarG6m, cosetG6m] <;> norm_num

/-- The interchange `b ↔ c` of `G₆⁻`. -/
def swapG6m : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

theorem iso_G6m : swapG6m * swapG6m = 1 ∧ swapG6mᵀ * gramG6m * swapG6m = gramG6m ∧
    (swapG6m.map (Int.cast : ℤ → ℚ))ᵀ * MHG6m * swapG6m.map (Int.cast : ℤ → ℚ) = MHG6m := by
  decide +kernel

theorem swap_cosetG6m (a b t : ℤ) :
    gramR swapG6m *ᵥ ratVec (cosetG6m a b t) = ratVec (cosetG6m b a t) := by
  rw [gramR_mulVec_ratVec]
  congr 1
  funext i
  fin_cases i <;> simp [swapG6m, cosetG6m, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem thetaQ_cosetG6m_swap (a b t : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramG6m) (MHG6m.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetG6m b a t)) τ =
      latticeThetaQ (gramR gramG6m) (MHG6m.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetG6m a b t)) τ := by
  rw [← swap_cosetG6m]
  exact latticeThetaQ_isometry iso_G6m.1 iso_G6m.1 (gramR_transpose_mul_mul iso_G6m.2.1)
    (ratCast_transpose_mul_mul iso_G6m.2.2) _ τ

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.existsUnique_residue_of_smith
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_isometry
#print axioms HaagerupIzumi.C8.Theta.sum_eChar_neg_of_involutive
#print axioms HaagerupIzumi.C8.Theta.posDef_L7A2
#print axioms HaagerupIzumi.C8.Theta.hR_L7A2
#print axioms HaagerupIzumi.C8.Theta.thetaQL7A2_S
#print axioms HaagerupIzumi.C8.Theta.thetaL7A2_S
#print axioms HaagerupIzumi.C8.Theta.thetaQL7A2_T
#print axioms HaagerupIzumi.C8.Theta.thetaQ_cosetL7A2_neg_r
#print axioms HaagerupIzumi.C8.Theta.thetaQG7m_S
#print axioms HaagerupIzumi.C8.Theta.thetaQG7m_S_o
#print axioms HaagerupIzumi.C8.Theta.thetaQA1A1A2_S
#print axioms HaagerupIzumi.C8.Theta.thetaQG6m_S
#print axioms HaagerupIzumi.C8.Theta.thetaG6m_T
#print axioms HaagerupIzumi.C8.Theta.thetaQ_cosetA1A1A2_conj
#print axioms HaagerupIzumi.C8.Theta.thetaQ_cosetG6m_swap
