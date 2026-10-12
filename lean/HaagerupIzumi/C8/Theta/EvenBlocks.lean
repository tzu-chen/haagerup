module

public import HaagerupIzumi.C8.Theta.WeilBlocks
public import HaagerupIzumi.C8.Theta.ThetaSupport

@[expose] public section

/-!
# The even blocks of the four theta vectors

W6 plan item 2, finite part, continued (`Theta/WeilBlocks.lean` for the full vectors).  The
manuscript (lines 3632–3647, 3690–3698, 3716–3720, 3767–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) identifies the VOA character vector with the
**even block** of the theta vector: the coordinates are orbits of labels of `L'/L` under the
symmetries used by the projections of the tables.  Here, for each lattice:

* an orbit index `E` with representatives `ιE : E → L'/L` and orbit map `π : L'/L → E`;
  the orbit property `ιE (π q) ∈ {g q}` is kernel-checked (`orbit_*`, `decide +kernel`);
  - `L₇ ⊕ A₂`: `E = Fin 4 × Fin 2`, `(r, s) ↦ (±r, ±s)` (lattice isometry `-1 ⊕ 1` and `-1`);
  - `G₇⁻`: `E = Fin 4 × Fin 2`, the manuscript labels `(r, s) ↦ 9r + 7s mod 21`, orbits under
    `j ↦ -j` and the discriminant-form isometry `j ↦ 13j` (`r ↦ -r`); the theta vector is
    replaced by its average `(F_j + F_{13j})/2` (`FaG7m`), which is what the separately even
    projection of Table 2 uses;
  - `A₁ ⊕ A₁ ⊕ A₂`: `E = Fin 3 × Fin 2` (`ab ∈ {00, 10, 11}`, `s ∈ {0, 1}`), orbits under the
    interchange of the two `A₁` and `s ↦ -s` (Table 3, weight `H = HA1A1A2`);
  - `G₆⁻`: `E = Fin 2 × Fin 2 × Fin 2`, orbits under `-1` (the projection `avgNeg` of Table 4);
* the theta vector is orbit-constant (`F*_const`), so its restriction `FE*` to `E` satisfies
  `FE(S•τ) = SθE FE(τ)`, `FE(T•τ) = TθE FE(τ)` with the **reduced matrices**
  `SθE_{e e'} = ∑_{π q = e'} Sθ_{ιE e, q}` and `TθE = diag Tθ_{ιE e}` (`reduceMat`);
* `FE*_covariant`: for any `σ_E : SL(2, ℤ) → GL(E, ℂ)` with `σ_E(S) = SθE`, `σ_E(T) = TθE`
  (named hypotheses; the VOA-side Zhu/Huang representation on the module labels),
  `FE(γ•τ) = σ_E(γ) FE(τ)`;
* `noInvariantE_*`, `noInvariantE_sigma_*`: no nonzero `σ_E`-invariant vector; the only
  `T`-fixed coordinate is `(0, 1)` for `L₇ ⊕ A₂` and `A₁ ⊕ A₁ ⊕ A₂` (kernel-checked), and the
  vacuum row of `SθE` is nonzero there (`-2/√|D|`, lines 3677, 3739: "the sole `T`-fixed
  coordinate is not `S`-invariant"); none for `G₇⁻`, `G₆⁻`.

Nothing here is an external hypothesis; `σ_E` and its values at `S`, `T` are hypotheses of
the covariance and invariant-vector statements only.
-/

noncomputable section

open Complex Matrix ModularGroup
open scoped MatrixGroups UpperHalfPlane Real

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Reduction of a matrix to an orbit block -/

section Reduce

variable {ι E : Type*} [Fintype ι] [Fintype E] [DecidableEq E]

/-- `(reduceMat ιE pr Sm)_{e e'} = ∑_{q : pr q = e'} Sm_{ιE e, q}`. -/
def reduceMat (ιE : E → ι) (pr : ι → E) (Sm : Matrix ι ι ℂ) : Matrix E E ℂ :=
  Matrix.of fun e e' => ∑ q ∈ Finset.univ.filter (fun q => pr q = e'), Sm (ιE e) q

/-- For an orbit-constant vector, `Sm u` restricted to the representatives is the reduced
matrix applied to the restriction of `u`. -/
theorem reduce_mulVec (ιE : E → ι) (pr : ι → E) (Sm : Matrix ι ι ℂ) (u : ι → ℂ)
    (hu : ∀ q, u q = u (ιE (pr q))) (e : E) :
    (Sm *ᵥ u) (ιE e) = (reduceMat ιE pr Sm *ᵥ fun e' => u (ιE e')) e := by
  simp only [mulVec, dotProduct, reduceMat, Matrix.of_apply]
  rw [← Finset.sum_fiberwise Finset.univ pr (fun q => Sm (ιE e) q * u q)]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [hu q, (Finset.mem_filter.1 hq).2]

theorem reduced_S (F : ℍ → ι → ℂ) (Sm : Matrix ι ι ℂ) (ιE : E → ι) (pr : ι → E)
    (hS : ∀ τ : ℍ, F (S • τ) = Sm *ᵥ F τ) (hc : ∀ (τ : ℍ) q, F τ q = F τ (ιE (pr q)))
    (τ : ℍ) :
    (fun e => F (S • τ) (ιE e)) = reduceMat ιE pr Sm *ᵥ fun e => F τ (ιE e) := by
  funext e
  rw [hS τ]
  exact reduce_mulVec ιE pr Sm (F τ) (hc τ) e

theorem reduced_T [DecidableEq ι] (F : ℍ → ι → ℂ) (x : ι → ℝ) (ιE : E → ι)
    (hT : ∀ τ : ℍ, F (T • τ) = Matrix.diagonal (fun p => eChar (x p)) *ᵥ F τ) (τ : ℍ) :
    (fun e => F (T • τ) (ιE e)) =
      Matrix.diagonal (fun e => eChar (x (ιE e))) *ᵥ fun e => F τ (ιE e) := by
  funext e
  rw [hT τ, mulVec_diagonal, mulVec_diagonal]

/-- No nonzero `S`-fixed vector supported on one coordinate `p₁` if some other row `p₀` has a
nonzero entry at `p₁`. -/
theorem no_invariant_of_one (Sm : Matrix E E ℂ) (v : E → ℂ) (p0 p1 : E) (h01 : p0 ≠ p1)
    (hsupp : ∀ q, q ≠ p1 → v q = 0) (hS : Sm *ᵥ v = v) (hrow0 : Sm p0 p1 ≠ 0) : v = 0 := by
  have hsum : (Sm *ᵥ v) p0 = Sm p0 p1 * v p1 := by
    simp only [mulVec, dotProduct]
    exact Fintype.sum_eq_single p1 fun q hq => by rw [hsupp q hq, mul_zero]
  have h0 := congrFun hS p0
  rw [hsum, hsupp p0 h01] at h0
  have ha : v p1 = 0 := (mul_eq_zero.1 h0).resolve_left hrow0
  funext q
  by_cases hq : q = p1
  · subst hq
    rw [ha]
    rfl
  · exact hsupp q hq

end Reduce

/-! ## `L₇ ⊕ A₂` -/

def ιL7A2 (e : Fin 4 × Fin 2) : Fin 7 × Fin 3 :=
  (⟨e.1.val, Nat.lt_of_lt_of_le e.1.isLt (by norm_num)⟩,
    ⟨e.2.val, Nat.lt_of_lt_of_le e.2.isLt (by norm_num)⟩)

def πL7A2 (q : Fin 7 × Fin 3) : Fin 4 × Fin 2 :=
  (⟨min q.1.val (7 - q.1.val), by have := q.1.isLt; omega⟩,
    ⟨min q.2.val (3 - q.2.val), by have := q.2.isLt; omega⟩)

/-- Orbits `(±r, ±s)` (kernel-checked). -/
theorem orbit_L7A2 : ∀ q : Fin 7 × Fin 3, ιL7A2 (πL7A2 q) = q ∨
    ιL7A2 (πL7A2 q) = (-q.1, q.2) ∨ ιL7A2 (πL7A2 q) = (-q.1, -q.2) ∨
      ιL7A2 (πL7A2 q) = (q.1, -q.2) := by
  decide +kernel

theorem modL7A2_self : ∀ p : Fin 7 × Fin 3, modL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ) = p := by
  decide +kernel

theorem modL7A2_negr :
    ∀ p : Fin 7 × Fin 3, modL7A2 (-((p.1 : ℕ) : ℤ)) ((p.2 : ℕ) : ℤ) = (-p.1, p.2) := by
  decide +kernel

theorem modL7A2_neg :
    ∀ p : Fin 7 × Fin 3, modL7A2 (-((p.1 : ℕ) : ℤ)) (-((p.2 : ℕ) : ℤ)) = (-p.1, -p.2) := by
  decide +kernel

theorem modL7A2_negs :
    ∀ p : Fin 7 × Fin 3, modL7A2 ((p.1 : ℕ) : ℤ) (-((p.2 : ℕ) : ℤ)) = (p.1, -p.2) := by
  decide +kernel

theorem ratVec_cosetL7A2_neg (r s : ℤ) :
    ratVec (cosetL7A2 (-r) (-s)) = -ratVec (cosetL7A2 r s) := by
  funext i
  fin_cases i <;> simp [ratVec, cosetL7A2] <;> ring

theorem thetaQL7A2_neg (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 7 × Fin 3) (τ : ℂ) :
    thetaQL7A2 M (-p.1, -p.2) τ = thetaQL7A2 M p τ := by
  rw [← modL7A2_neg p, ← latticeThetaQ_cosetL7A2, ratVec_cosetL7A2_neg, latticeThetaQ_neg,
    latticeThetaQ_cosetL7A2, modL7A2_self p]

theorem thetaQL7A2_negr {M : Matrix (Fin 4) (Fin 4) ℚ}
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (p : Fin 7 × Fin 3) (τ : ℂ) : thetaQL7A2 M (-p.1, p.2) τ = thetaQL7A2 M p τ := by
  rw [← modL7A2_negr p, ← latticeThetaQ_cosetL7A2, thetaQ_cosetL7A2_neg_r hMiso,
    latticeThetaQ_cosetL7A2, modL7A2_self p]

theorem thetaQL7A2_negs {M : Matrix (Fin 4) (Fin 4) ℚ}
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (p : Fin 7 × Fin 3) (τ : ℂ) : thetaQL7A2 M (p.1, -p.2) τ = thetaQL7A2 M p τ := by
  rw [← modL7A2_negs p, ← latticeThetaQ_cosetL7A2, ← thetaQ_cosetL7A2_neg_r hMiso,
    ratVec_cosetL7A2_neg, latticeThetaQ_neg, latticeThetaQ_cosetL7A2, modL7A2_self p]

/-- The weights `H₁`, `H₂` are invariant under the isometry `-1 ⊕ 1`. -/
theorem iso_MH1 :
    (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * MH1 * isoL7A2.map (Int.cast : ℤ → ℚ) = MH1 :=
  iso_L7A2.2.2.1

theorem iso_MH2 :
    (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * MH2 * isoL7A2.map (Int.cast : ℤ → ℚ) = MH2 :=
  iso_L7A2.2.2.2

theorem FL7A2_const {M : Matrix (Fin 4) (Fin 4) ℚ}
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (τ : ℍ) (q : Fin 7 × Fin 3) : FL7A2 M τ q = FL7A2 M τ (ιL7A2 (πL7A2 q)) := by
  unfold FL7A2
  rcases orbit_L7A2 q with h | h | h | h <;> rw [h]
  · rw [thetaQL7A2_negr hMiso q]
  · rw [thetaQL7A2_neg M q]
  · rw [thetaQL7A2_negs hMiso q]

/-- The even block `FE_{(r,s)} = Θ_{H,(r,s)}/η⁸`, `0 ≤ r ≤ 3`, `0 ≤ s ≤ 1`. -/
def FEL7A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 4 × Fin 2 → ℂ :=
  fun e => FL7A2 M τ (ιL7A2 e)

def SθEL7A2 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ := reduceMat ιL7A2 πL7A2 SθL7A2

def TθEL7A2 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ :=
  Matrix.diagonal fun e => eChar (eL7A2 (ιL7A2 e) - 1 / 3)

theorem FEL7A2_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invL7A2 M = 0)
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (τ : ℍ) : FEL7A2 M (S • τ) = SθEL7A2 *ᵥ FEL7A2 M τ :=
  reduced_S (FL7A2 M) SθL7A2 ιL7A2 πL7A2 (FL7A2_S hM) (FL7A2_const hMiso) τ

theorem FEL7A2_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    FEL7A2 M (T • τ) = TθEL7A2 *ᵥ FEL7A2 M τ :=
  reduced_T (FL7A2 M) (fun p => eL7A2 p - 1 / 3) ιL7A2 (FL7A2_T M) τ

/-- **Even-block covariance, `L₇ ⊕ A₂`**, given `σ_E(S) = SθE`, `σ_E(T) = TθE`. -/
theorem FEL7A2_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invL7A2 M = 0)
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEL7A2) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FEL7A2 M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FEL7A2 M τ :=
  covariant_of_S_T σ (FEL7A2 M) (fun τ => by rw [hσS]; exact FEL7A2_S hM hMiso τ)
    (fun τ => by rw [hσT]; exact FEL7A2_T M τ)

/-- The only `T`-fixed coordinate of the even block is `(0, 1)` (kernel-checked). -/
theorem tfixedE_L7A2 :
    ∀ e : Fin 4 × Fin 2, e ≠ (0, 1) → (eQL7A2 (ιL7A2 e) - 1 / 3).den ≠ 1 := by
  decide +kernel

theorem filter_πL7A2 :
    (Finset.univ.filter fun q : Fin 7 × Fin 3 => πL7A2 q = (0, 1)) = {(0, 1), (0, 2)} := by
  decide +kernel

/-- The vacuum row of `SθE` at the `T`-fixed coordinate: `SθE_{(0,0),(0,1)} = -2/√21`. -/
theorem SθEL7A2_vac : SθEL7A2 (0, 0) (0, 1) = 2 * -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨s1, s2, -, -⟩ := sL7A2_vals
  show (∑ q ∈ Finset.univ.filter fun q => πL7A2 q = (0, 1), SθL7A2 (ιL7A2 (0, 0)) q) = _
  rw [filter_πL7A2, Finset.sum_pair (by decide), show ιL7A2 (0, 0) = (0, 0) by decide]
  simp only [SθL7A2, Matrix.of_apply, s1, s2, neg_zero, eChar_zero, mul_one]
  ring

theorem noInvariantE_L7A2 (v : Fin 4 × Fin 2 → ℂ) (hS : SθEL7A2 *ᵥ v = v)
    (hT : TθEL7A2 *ᵥ v = v) : v = 0 := by
  have hsupp : ∀ q, q ≠ (0, 1) → v q = 0 := fun q h =>
    supp_of_T_fixed (fun e => eL7A2 (ιL7A2 e) - 1 / 3) v hT q
      (eChar_ne_one_of_den (eL7A2_sub _) (tfixedE_L7A2 q h))
  refine no_invariant_of_one SθEL7A2 v (0, 0) (0, 1) (by decide) hsupp hS ?_
  rw [SθEL7A2_vac]
  exact mul_ne_zero two_ne_zero
    (neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)))))

/-- **`hinv` of `pole_cancellation`** on the even block of `L₇ ⊕ A₂`. -/
theorem noInvariantE_sigma_L7A2 (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEL7A2) :
    ∀ v : Fin 4 × Fin 2 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariantE_L7A2

/-! ## `A₁ ⊕ A₁ ⊕ A₂` (weight `H = HA1A1A2`) -/

/-- Representatives: `ab ∈ {00, 10, 11}` (index `0, 1, 2`), `s ∈ {0, 1}`. -/
def ιA1A1A2 (e : Fin 3 × Fin 2) : Fin 2 × Fin 2 × Fin 3 :=
  (if e.1.val = 0 then 0 else 1, if e.1.val = 2 then 1 else 0,
    ⟨e.2.val, Nat.lt_of_lt_of_le e.2.isLt (by norm_num)⟩)

def πA1A1A2 (q : Fin 2 × Fin 2 × Fin 3) : Fin 3 × Fin 2 :=
  (⟨q.1.val + q.2.1.val, by have := q.1.isLt; have := q.2.1.isLt; omega⟩,
    ⟨min q.2.2.val (3 - q.2.2.val), by have := q.2.2.isLt; omega⟩)

/-- Orbits under the swap and `s ↦ -s` (kernel-checked). -/
theorem orbit_A1A1A2 : ∀ q : Fin 2 × Fin 2 × Fin 3, ιA1A1A2 (πA1A1A2 q) = q ∨
    ιA1A1A2 (πA1A1A2 q) = (q.2.1, q.1, q.2.2) ∨ ιA1A1A2 (πA1A1A2 q) = (q.1, q.2.1, -q.2.2) ∨
      ιA1A1A2 (πA1A1A2 q) = (q.2.1, q.1, -q.2.2) := by
  decide +kernel

theorem modA1A1A2_self : ∀ p : Fin 2 × Fin 2 × Fin 3,
    modA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ) = p := by
  decide +kernel

theorem modA1A1A2_swap : ∀ p : Fin 2 × Fin 2 × Fin 3,
    modA1A1A2 ((p.2.1 : ℕ) : ℤ) ((p.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ) = (p.2.1, p.1, p.2.2) := by
  decide +kernel

theorem modA1A1A2_conj : ∀ p : Fin 2 × Fin 2 × Fin 3,
    modA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) (-((p.2.2 : ℕ) : ℤ)) = (p.1, p.2.1, -p.2.2) := by
  decide +kernel

theorem modA1A1A2_swapconj : ∀ p : Fin 2 × Fin 2 × Fin 3,
    modA1A1A2 ((p.2.1 : ℕ) : ℤ) ((p.1 : ℕ) : ℤ) (-((p.2.2 : ℕ) : ℤ)) =
      (p.2.1, p.1, -p.2.2) := by
  decide +kernel

theorem thetaQA1A1A2_swap (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQA1A1A2 MHA1A1A2 (p.2.1, p.1, p.2.2) τ = thetaQA1A1A2 MHA1A1A2 p τ := by
  rw [← modA1A1A2_swap p, ← latticeThetaQ_cosetA1A1A2, thetaQ_cosetA1A1A2_swap,
    latticeThetaQ_cosetA1A1A2, modA1A1A2_self p]

theorem thetaQA1A1A2_conj (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQA1A1A2 MHA1A1A2 (p.1, p.2.1, -p.2.2) τ = thetaQA1A1A2 MHA1A1A2 p τ := by
  rw [← modA1A1A2_conj p, ← latticeThetaQ_cosetA1A1A2, thetaQ_cosetA1A1A2_conj,
    latticeThetaQ_cosetA1A1A2, modA1A1A2_self p]

theorem thetaQA1A1A2_swapconj (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQA1A1A2 MHA1A1A2 (p.2.1, p.1, -p.2.2) τ = thetaQA1A1A2 MHA1A1A2 p τ := by
  rw [← modA1A1A2_swapconj p, ← latticeThetaQ_cosetA1A1A2, thetaQ_cosetA1A1A2_conj,
    thetaQ_cosetA1A1A2_swap, latticeThetaQ_cosetA1A1A2, modA1A1A2_self p]

theorem FA1A1A2_const (τ : ℍ) (q : Fin 2 × Fin 2 × Fin 3) :
    FA1A1A2 MHA1A1A2 τ q = FA1A1A2 MHA1A1A2 τ (ιA1A1A2 (πA1A1A2 q)) := by
  unfold FA1A1A2
  rcases orbit_A1A1A2 q with h | h | h | h <;> rw [h]
  · rw [thetaQA1A1A2_swap q]
  · rw [thetaQA1A1A2_conj q]
  · rw [thetaQA1A1A2_swapconj q]

def FEA1A1A2 (τ : ℍ) : Fin 3 × Fin 2 → ℂ := fun e => FA1A1A2 MHA1A1A2 τ (ιA1A1A2 e)

def SθEA1A1A2 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  reduceMat ιA1A1A2 πA1A1A2 SθA1A1A2

def TθEA1A1A2 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  Matrix.diagonal fun e => eChar (eA1A1A2 (ιA1A1A2 e) - 1 / 3)

theorem FEA1A1A2_S (τ : ℍ) : FEA1A1A2 (S • τ) = SθEA1A1A2 *ᵥ FEA1A1A2 τ :=
  reduced_S (FA1A1A2 MHA1A1A2) SθA1A1A2 ιA1A1A2 πA1A1A2
    (FA1A1A2_S harmonic_quadratics.2.2.2.2.1) FA1A1A2_const τ

theorem FEA1A1A2_T (τ : ℍ) : FEA1A1A2 (T • τ) = TθEA1A1A2 *ᵥ FEA1A1A2 τ :=
  reduced_T (FA1A1A2 MHA1A1A2) (fun p => eA1A1A2 p - 1 / 3) ιA1A1A2 (FA1A1A2_T MHA1A1A2) τ

theorem FEA1A1A2_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FEA1A1A2 (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FEA1A1A2 τ :=
  covariant_of_S_T σ FEA1A1A2 (fun τ => by rw [hσS]; exact FEA1A1A2_S τ)
    (fun τ => by rw [hσT]; exact FEA1A1A2_T τ)

theorem tfixedE_A1A1A2 :
    ∀ e : Fin 3 × Fin 2, e ≠ (0, 1) → (eQA1A1A2 (ιA1A1A2 e) - 1 / 3).den ≠ 1 := by
  decide +kernel

theorem filter_πA1A1A2 :
    (Finset.univ.filter fun q : Fin 2 × Fin 2 × Fin 3 => πA1A1A2 q = (0, 1)) =
      {(0, 0, 1), (0, 0, 2)} := by
  decide +kernel

theorem SθEA1A1A2_vac : SθEA1A1A2 (0, 0) (0, 1) = 2 * -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨s1, s2, -, -⟩ := sA1A1A2_vals
  show (∑ q ∈ Finset.univ.filter fun q => πA1A1A2 q = (0, 1), SθA1A1A2 (ιA1A1A2 (0, 0)) q) = _
  rw [filter_πA1A1A2, Finset.sum_pair (by decide), show ιA1A1A2 (0, 0) = (0, 0, 0) by decide]
  simp only [SθA1A1A2, Matrix.of_apply, s1, s2, neg_zero, eChar_zero, mul_one]
  ring

theorem noInvariantE_A1A1A2 (v : Fin 3 × Fin 2 → ℂ) (hS : SθEA1A1A2 *ᵥ v = v)
    (hT : TθEA1A1A2 *ᵥ v = v) : v = 0 := by
  have hsupp : ∀ q, q ≠ (0, 1) → v q = 0 := fun q h =>
    supp_of_T_fixed (fun e => eA1A1A2 (ιA1A1A2 e) - 1 / 3) v hT q
      (eChar_ne_one_of_den (eA1A1A2_sub _) (tfixedE_A1A1A2 q h))
  refine no_invariant_of_one SθEA1A1A2 v (0, 0) (0, 1) (by decide) hsupp hS ?_
  rw [SθEA1A1A2_vac]
  exact mul_ne_zero two_ne_zero
    (neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)))))

theorem noInvariantE_sigma_A1A1A2
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2) :
    ∀ v : Fin 3 × Fin 2 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariantE_A1A1A2

/-! ## `G₆⁻` -/

def ιG6m (e : Fin 2 × Fin 2 × Fin 2) : Fin 2 × Fin 2 × Fin 3 :=
  (e.1, e.2.1, ⟨e.2.2.val, Nat.lt_of_lt_of_le e.2.2.isLt (by norm_num)⟩)

def πG6m (q : Fin 2 × Fin 2 × Fin 3) : Fin 2 × Fin 2 × Fin 2 :=
  (q.1, q.2.1, ⟨min q.2.2.val (3 - q.2.2.val), by have := q.2.2.isLt; omega⟩)

theorem orbit_G6m : ∀ q : Fin 2 × Fin 2 × Fin 3,
    ιG6m (πG6m q) = q ∨ ιG6m (πG6m q) = (-q.1, -q.2.1, -q.2.2) := by
  decide +kernel

theorem modG6m_self : ∀ p : Fin 2 × Fin 2 × Fin 3,
    modG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ) = p := by
  decide +kernel

theorem modG6m_neg : ∀ p : Fin 2 × Fin 2 × Fin 3,
    modG6m (-((p.1 : ℕ) : ℤ)) (-((p.2.1 : ℕ) : ℤ)) (-((p.2.2 : ℕ) : ℤ)) =
      (-p.1, -p.2.1, -p.2.2) := by
  decide +kernel

theorem ratVec_cosetG6m_neg (a b t : ℤ) :
    ratVec (cosetG6m (-a) (-b) (-t)) = -ratVec (cosetG6m a b t) := by
  funext i
  fin_cases i <;> simp [ratVec, cosetG6m] <;> ring

theorem thetaQG6m_neg (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQG6m M (-p.1, -p.2.1, -p.2.2) τ = thetaQG6m M p τ := by
  rw [← modG6m_neg p, ← latticeThetaQ_cosetG6m, ratVec_cosetG6m_neg, latticeThetaQ_neg,
    latticeThetaQ_cosetG6m, modG6m_self p]

theorem FG6m_const (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) (q : Fin 2 × Fin 2 × Fin 3) :
    FG6m M τ q = FG6m M τ (ιG6m (πG6m q)) := by
  unfold FG6m
  rcases orbit_G6m q with h | h <;> rw [h]
  rw [thetaQG6m_neg M q]

def FEG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 2 × Fin 2 × Fin 2 → ℂ :=
  fun e => FG6m M τ (ιG6m e)

def SθEG6m : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  reduceMat ιG6m πG6m SθG6m

def TθEG6m : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun e => eChar (eG6m (ιG6m e) - 1 / 3)

theorem FEG6m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG6m M = 0) (τ : ℍ) :
    FEG6m M (S • τ) = SθEG6m *ᵥ FEG6m M τ :=
  reduced_S (FG6m M) SθG6m ιG6m πG6m (FG6m_S hM) (FG6m_const M) τ

theorem FEG6m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    FEG6m M (T • τ) = TθEG6m *ᵥ FEG6m M τ :=
  reduced_T (FG6m M) (fun p => eG6m p - 1 / 3) ιG6m (FG6m_T M) τ

theorem FEG6m_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG6m M = 0)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FEG6m M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FEG6m M τ :=
  covariant_of_S_T σ (FEG6m M) (fun τ => by rw [hσS]; exact FEG6m_S hM τ)
    (fun τ => by rw [hσT]; exact FEG6m_T M τ)

theorem noInvariantE_G6m (v : Fin 2 × Fin 2 × Fin 2 → ℂ) (_hS : SθEG6m *ᵥ v = v)
    (hT : TθEG6m *ᵥ v = v) : v = 0 :=
  funext fun e => supp_of_T_fixed (fun e => eG6m (ιG6m e) - 1 / 3) v hT e
    (eChar_ne_one_of_den (eG6m_sub _) (tfixed_G6m _))

theorem noInvariantE_sigma_G6m
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG6m) :
    ∀ v : Fin 2 × Fin 2 × Fin 2 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariantE_G6m

/-! ## `G₇⁻`: the average over the `O(D)`-isometry `j ↦ 13 j` -/

/-- The manuscript label `(r, s)`, `0 ≤ r ≤ 3`, `0 ≤ s ≤ 1`, is `j = 9r + 7s mod 21`. -/
def ιG7m (e : Fin 4 × Fin 2) : Fin 21 :=
  ⟨(9 * e.1.val + 7 * e.2.val) % 21, Nat.mod_lt _ (by norm_num)⟩

/-- The orbit of `j` under `±1, ±13`: `r ≡ 4j (mod 7)` up to sign, `s ≡ j (mod 3)` up to
sign. -/
def πG7m (j : Fin 21) : Fin 4 × Fin 2 :=
  (⟨min ((4 * j.val) % 7) (7 - (4 * j.val) % 7), by omega⟩,
    ⟨if j.val % 3 = 0 then 0 else 1, by split <;> omega⟩)

theorem orbit_G7m : ∀ j : Fin 21, ιG7m (πG7m j) = j ∨ ιG7m (πG7m j) = -j ∨
    ιG7m (πG7m j) = oG7m j ∨ ιG7m (πG7m j) = -oG7m j := by
  decide +kernel

theorem oG7m_neg : ∀ j : Fin 21, oG7m (-j) = -oG7m j := by
  decide +kernel

theorem modG7m_self : ∀ j : Fin 21, modG7m ((j : ℕ) : ℤ) = j := by
  decide +kernel

theorem modG7m_neg : ∀ j : Fin 21, modG7m (-((j : ℕ) : ℤ)) = -j := by
  decide +kernel

theorem ratVec_repG7m_neg (t : ℤ) : ratVec (repG7m (-t)) = -ratVec (repG7m t) := by
  funext i
  simp [ratVec, repG7m]

theorem thetaQG7m_neg (M : Matrix (Fin 4) (Fin 4) ℚ) (j : Fin 21) (τ : ℂ) :
    thetaQG7m M (-j) τ = thetaQG7m M j τ := by
  rw [← modG7m_neg j, ← latticeThetaQ_repG7m, ratVec_repG7m_neg, latticeThetaQ_neg,
    latticeThetaQ_repG7m, modG7m_self j]

/-- The average `(F_j + F_{13 j})/2`, the separately even projection of Table 2. -/
def FaG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 21 → ℂ :=
  (1 / 2 : ℂ) • (FG7m M τ + fun j => FG7m M τ (oG7m j))

theorem FaG7m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0) (τ : ℍ) :
    FaG7m M (S • τ) = SθG7m *ᵥ FaG7m M τ := by
  funext j
  have h1 := congrFun (FG7m_S hM τ) j
  have h2 : FG7m M (S • τ) (oG7m j) = (SθG7m *ᵥ fun k => FG7m M τ (oG7m k)) j :=
    congrFun (FG7m_o_S hM τ) j
  simp only [FaG7m, mulVec_smul, mulVec_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h1, h2]

theorem FaG7m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    FaG7m M (T • τ) = TθG7m *ᵥ FaG7m M τ := by
  funext j
  have h1 := congrFun (FG7m_T M τ) j
  have h2 : FG7m M (T • τ) (oG7m j) = (TθG7m *ᵥ fun k => FG7m M τ (oG7m k)) j :=
    congrFun (FG7m_o_T M τ) j
  simp only [FaG7m, mulVec_smul, mulVec_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h1, h2]

theorem FG7m_neg (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) (j : Fin 21) :
    FG7m M τ (-j) = FG7m M τ j := by
  unfold FG7m
  rw [thetaQG7m_neg]

theorem FaG7m_neg (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) (j : Fin 21) :
    FaG7m M τ (-j) = FaG7m M τ j := by
  simp only [FaG7m, Pi.smul_apply, Pi.add_apply, oG7m_neg, FG7m_neg]

theorem FaG7m_o (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) (j : Fin 21) :
    FaG7m M τ (oG7m j) = FaG7m M τ j := by
  simp only [FaG7m, Pi.smul_apply, Pi.add_apply, oG7m_data.1 j, add_comm]

theorem FaG7m_const (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) (j : Fin 21) :
    FaG7m M τ j = FaG7m M τ (ιG7m (πG7m j)) := by
  rcases orbit_G7m j with h | h | h | h <;> rw [h]
  · rw [FaG7m_neg]
  · rw [FaG7m_o]
  · rw [FaG7m_neg, FaG7m_o]

/-- The even block `FE_{(r,s)}` of `G₇⁻` in the manuscript's labels. -/
def FEG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 4 × Fin 2 → ℂ :=
  fun e => FaG7m M τ (ιG7m e)

def SθEG7m : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ := reduceMat ιG7m πG7m SθG7m

def TθEG7m : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ :=
  Matrix.diagonal fun e => eChar (eG7m (ιG7m e) - 1 / 3)

theorem FEG7m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0) (τ : ℍ) :
    FEG7m M (S • τ) = SθEG7m *ᵥ FEG7m M τ :=
  reduced_S (FaG7m M) SθG7m ιG7m πG7m (FaG7m_S hM) (FaG7m_const M) τ

theorem FEG7m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    FEG7m M (T • τ) = TθEG7m *ᵥ FEG7m M τ :=
  reduced_T (FaG7m M) (fun j => eG7m j - 1 / 3) ιG7m (FaG7m_T M) τ

theorem FEG7m_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FEG7m M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FEG7m M τ :=
  covariant_of_S_T σ (FEG7m M) (fun τ => by rw [hσS]; exact FEG7m_S hM τ)
    (fun τ => by rw [hσT]; exact FEG7m_T M τ)

theorem noInvariantE_G7m (v : Fin 4 × Fin 2 → ℂ) (_hS : SθEG7m *ᵥ v = v)
    (hT : TθEG7m *ᵥ v = v) : v = 0 :=
  funext fun e => supp_of_T_fixed (fun e => eG7m (ιG7m e) - 1 / 3) v hT e
    (eChar_ne_one_of_den (eG7m_sub _) (tfixed_G7m _))

theorem noInvariantE_sigma_G7m (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m) :
    ∀ v : Fin 4 × Fin 2 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariantE_G7m

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.reduce_mulVec
#print axioms HaagerupIzumi.C8.Theta.FEL7A2_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariantE_sigma_L7A2
#print axioms HaagerupIzumi.C8.Theta.SθEL7A2_vac
#print axioms HaagerupIzumi.C8.Theta.FEA1A1A2_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariantE_sigma_A1A1A2
#print axioms HaagerupIzumi.C8.Theta.FEG6m_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariantE_sigma_G6m
#print axioms HaagerupIzumi.C8.Theta.FEG7m_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariantE_sigma_G7m
