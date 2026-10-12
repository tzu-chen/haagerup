module

public import HaagerupIzumi.C8.Theta.LatticeData
public import HaagerupIzumi.C8.Theta.Eta8

@[expose] public section

/-!
# The weight-zero theta vectors `Θ_H/η⁸`: their `S`/`T` matrices and the conditions on `σ`

W6 plan item 2, finite part (`Theta/W6_PLAN.md`), for the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): "multiplication by `η⁸` identifies it with
the Weil representation".  For each of the four lattices and every harmonic weight `M`:

* `F*`: the weight-zero vector `F(τ)_p = Θ_{H,p}(τ)/η⁸(τ)` on `ℍ`, indexed by `L'/L`;
* `Sθ*`, `Tθ*`: explicit matrices, `Sθ_{pq} = -1/√|D| · e(-(γ_p, γ_q))` (Borcherds' form,
  `e(-sig/8) = -1`) and `Tθ = diag e(q(γ_p) - 1/3)`; the `τ⁴` of the theta `S`-law cancels
  against `η⁸(-1/τ) = τ⁴ η⁸(τ)` and `e(1/3)` is the `T`-multiplier of `η⁸`;
* `F*_S`, `F*_T`: `F(S•τ) = Sθ F(τ)` and `F(T•τ) = Tθ F(τ)` (from `LatticeData` and `Eta8`);
* `F*_covariant`: **the identities a representation `σ` must satisfy**: for any homomorphism
  `σ : SL(2, ℤ) → GL(L'/L, ℂ)` with `σ(S) = Sθ` and `σ(T) = Tθ` (named hypotheses `hσS`,
  `hσT`; `σ` comes from the VOA side, plan item 2), `F(γ•τ) = σ(γ) F(τ)` for all `γ`;
* `noInvariant_*` and `noInvariant_sigma_*`: `Sθ` and `Tθ` have no common nonzero fixed vector,
  hence such a `σ` has no nonzero invariant vector, the hypothesis `hinv` of
  `pole_cancellation`.  The `T`-fixed coordinates are found by a kernel-checked finite
  computation over ℚ (`tfixed_*`, `decide +kernel`): none for `G₇⁻`, `G₆⁻` ("`T` has no fixed
  vector", lines 3708, 3767–3768); for `L₇ ⊕ A₂` and `A₁ ⊕ A₁ ⊕ A₂` only the two labels `(0, ±1)`,
  which the `S`-row of the vacuum and the `S`-entries among them exclude (lines 3677, 3739).

The remaining inputs for `pole_cancellation` (`σ(S) = Sθ`, `σ(T) = Tθ` from the VOA side, and
finite image of `σ`, which, `σ` being pinned at the generators, is a property of the explicit
matrices) stay hypotheses.  Nothing else is assumed.
-/

noncomputable section

open Complex Matrix ModularGroup
open scoped MatrixGroups UpperHalfPlane Real

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Generic tools -/

theorem eChar_ne_zero (x : ℝ) : eChar x ≠ 0 := by
  intro h
  have h1 := norm_eChar x
  rw [h, norm_zero] at h1
  norm_num at h1

theorem eChar_sub (x y : ℝ) : eChar (x - y) = eChar x * (eChar y)⁻¹ := by
  rw [sub_eq_add_neg, eChar_add, eChar_neg]

theorem re_eChar (x : ℝ) : (eChar x).re = Real.cos (2 * π * x) := by
  rw [eChar]
  exact Complex.exp_ofReal_mul_I_re _

/-- `e(x) = 1` only for integers `x`. -/
theorem int_of_eChar_eq_one {x : ℝ} (h : eChar x = 1) : ∃ n : ℤ, x = n := by
  rw [eChar, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have h2 : ((2 * π * x : ℝ) : ℂ) = ((2 * π * n : ℝ) : ℂ) := by
    apply mul_right_cancel₀ I_ne_zero
    rw [hn]
    push_cast
    ring
  have h3 : 2 * π * x = 2 * π * n := Complex.ofReal_injective h2
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hπ h3

/-- `e(y) ≠ 1` for a rational `y` that is not an integer (checked by `den ≠ 1`). -/
theorem eChar_ne_one_of_den {x : ℝ} {y : ℚ} (hxy : x = (y : ℝ)) (h : y.den ≠ 1) :
    eChar x ≠ 1 := by
  intro h1
  obtain ⟨n, hn⟩ := int_of_eChar_eq_one h1
  have hy : y = n := by
    have : ((y : ℚ) : ℝ) = ((n : ℚ) : ℝ) := by rw [← hxy, hn]; push_cast; rfl
    exact Rat.cast_injective this
  rw [hy, Rat.den_intCast] at h
  exact h rfl

/-- `Re (1 + r (e(x) - e(y))) = 1` when `cos 2πx = cos 2πy`. -/
theorem one_sub_add_ne_zero (r x y : ℝ) (hxy : Real.cos (2 * π * x) = Real.cos (2 * π * y)) :
    1 - (-(r : ℂ) * eChar x) + (-(r : ℂ) * eChar y) ≠ 0 := by
  intro h
  have h1 : 1 - (-(r : ℂ) * eChar x) + (-(r : ℂ) * eChar y) = 1 + (r : ℂ) * (eChar x - eChar y) := by
    ring
  rw [h1] at h
  have h2 := congrArg Complex.re h
  rw [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.sub_re, re_eChar, re_eChar,
    hxy, sub_self, mul_zero, add_zero, Complex.zero_re] at h2
  norm_num at h2

/-- `cos(2π · (-2/3)) = cos(2π · (-4/3))`. -/
theorem cos_two_pi_neg_two_thirds :
    Real.cos (2 * π * (-(2 / 3 : ℝ))) = Real.cos (2 * π * (-(4 / 3 : ℝ))) := by
  have h : 2 * π * (-(2 / 3 : ℝ)) = -(2 * π * (-(4 / 3 : ℝ))) - 2 * π - 2 * π := by ring
  rw [h, Real.cos_sub_two_pi, Real.cos_sub_two_pi, Real.cos_neg]

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **`S`-law of `Θ/η⁸`** from a weight-four theta `S`-law `Θ_p(-1/τ) = -c τ⁴ ∑ e(-s) Θ_q`. -/
theorem weight_zero_S (Θ : ι → ℂ → ℂ) (c : ℂ) (s : ι → ι → ℝ)
    (hΘ : ∀ p (τ : ℂ), 0 < τ.im → Θ p (-1 / τ) = -(c * τ ^ 4) * ∑ q, eChar (-s p q) * Θ q τ)
    (τ : ℍ) :
    (fun p => Θ p ((S • τ : ℍ) : ℂ) / eta8 ((S • τ : ℍ) : ℂ)) =
      (Matrix.of fun p q => -c * eChar (-s p q)) *ᵥ fun p => Θ p τ / eta8 τ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h4 : (τ : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 hτ0
  funext p
  rw [coe_S_smul, hΘ p _ hτ, eta8_S hτ]
  simp only [mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  calc -(c * (τ : ℂ) ^ 4) * (eChar (-s p q) * Θ q τ) / ((τ : ℂ) ^ 4 * eta8 τ)
      = -c * eChar (-s p q) * (Θ q τ / eta8 τ) * ((τ : ℂ) ^ 4 / (τ : ℂ) ^ 4) := by ring
    _ = -c * eChar (-s p q) * (Θ q τ / eta8 τ) := by rw [div_self h4, mul_one]

/-- **`T`-law of `Θ/η⁸`** from `Θ_p(τ+1) = e(e_p) Θ_p(τ)`. -/
theorem weight_zero_T (Θ : ι → ℂ → ℂ) (e : ι → ℝ)
    (hΘ : ∀ p (τ : ℂ), Θ p (τ + 1) = eChar (e p) * Θ p τ) (τ : ℍ) :
    (fun p => Θ p ((T • τ : ℍ) : ℂ) / eta8 ((T • τ : ℍ) : ℂ)) =
      (Matrix.diagonal fun p => eChar (e p - 1 / 3)) *ᵥ fun p => Θ p τ / eta8 τ := by
  funext p
  rw [coe_T_smul, hΘ, eta8_T, mulVec_diagonal, eChar_sub]
  ring

/-- A vector fixed by `diag(e(x_p))` vanishes where `e(x_p) ≠ 1`. -/
theorem supp_of_T_fixed (x : ι → ℝ) (v : ι → ℂ)
    (hT : Matrix.diagonal (fun p => eChar (x p)) *ᵥ v = v) (p : ι) (hp : eChar (x p) ≠ 1) :
    v p = 0 := by
  have h := congrFun hT p
  rw [mulVec_diagonal] at h
  have h' : (eChar (x p) - 1) * v p = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact absurd (sub_eq_zero.1 h'') hp
  · exact h''

/-- No nonzero `S`-fixed vector supported on two coordinates `p₁, p₂`, if a third row `p₀`
has equal nonzero entries at `p₁, p₂` and `1 - S_{p₁p₁} + S_{p₁p₂} ≠ 0`. -/
theorem no_invariant_of_two (Sm : Matrix ι ι ℂ) (v : ι → ℂ) (p0 p1 p2 : ι) (h01 : p0 ≠ p1)
    (h02 : p0 ≠ p2) (h12 : p1 ≠ p2) (hsupp : ∀ q, q ≠ p1 → q ≠ p2 → v q = 0)
    (hS : Sm *ᵥ v = v) (hrow : Sm p0 p1 = Sm p0 p2) (hrow0 : Sm p0 p1 ≠ 0)
    (hdiag : 1 - Sm p1 p1 + Sm p1 p2 ≠ 0) : v = 0 := by
  have hsum : ∀ p, (Sm *ᵥ v) p = Sm p p1 * v p1 + Sm p p2 * v p2 := fun p => by
    simp only [mulVec, dotProduct]
    exact Fintype.sum_eq_add p1 p2 h12 fun q hq => by rw [hsupp q hq.1 hq.2, mul_zero]
  have h0 := congrFun hS p0
  rw [hsum, hsupp p0 h01 h02, hrow] at h0
  have hab : v p2 = -v p1 := by
    have h0' : Sm p0 p2 * (v p1 + v p2) = 0 := by rw [mul_add]; exact h0
    rcases mul_eq_zero.1 h0' with h | h
    · exact absurd (hrow.trans h) hrow0
    · linear_combination h
  have h1 := congrFun hS p1
  rw [hsum, hab] at h1
  have ha : v p1 = 0 := by
    have h1' : (1 - Sm p1 p1 + Sm p1 p2) * v p1 = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h1' with h | h
    · exact absurd h hdiag
    · exact h
  funext q
  by_cases hq1 : q = p1
  · subst hq1
    rw [ha]
    rfl
  by_cases hq2 : q = p2
  · subst hq2
    rw [hab, ha, neg_zero]
    rfl
  exact hsupp q hq1 hq2

/-- Invariance under `σ` gives invariance under `σ(S)`, `σ(T)`. -/
theorem noInvariant_sigma (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup ι ℂ) (Sm Tm : Matrix ι ι ℂ)
    (hσS : (σ S : Matrix ι ι ℂ) = Sm) (hσT : (σ T : Matrix ι ι ℂ) = Tm)
    (h : ∀ v : ι → ℂ, Sm *ᵥ v = v → Tm *ᵥ v = v → v = 0) :
    ∀ v : ι → ℂ, (∀ γ, (σ γ : Matrix ι ι ℂ) *ᵥ v = v) → v = 0 := fun v hv =>
  h v (hσS ▸ hv S) (hσT ▸ hv T)

end Generic

/-! ## `L₇ ⊕ A₂` (`M3First`) -/

/-- `F_p = Θ_{H,p}/η⁸`, `H = quadOf M`. -/
def FL7A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 7 × Fin 3 → ℂ :=
  fun p => thetaQL7A2 M p τ / eta8 τ

/-- `Sθ_{pq} = -1/√21 · e(-(2rr'/7 + 2ss'/3))`. -/
def SθL7A2 : Matrix (Fin 7 × Fin 3) (Fin 7 × Fin 3) ℂ :=
  Matrix.of fun p q => -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * eChar (-sL7A2 p q)

/-- `Tθ = diag e(r²/7 + s²/3 - 1/3)`. -/
def TθL7A2 : Matrix (Fin 7 × Fin 3) (Fin 7 × Fin 3) ℂ :=
  Matrix.diagonal fun p => eChar (eL7A2 p - 1 / 3)

theorem FL7A2_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invL7A2 M = 0) (τ : ℍ) :
    FL7A2 M (S • τ) = SθL7A2 *ᵥ FL7A2 M τ :=
  weight_zero_S (thetaQL7A2 M) _ sL7A2 (fun p _ hτ => thetaQL7A2_S hM p hτ) τ

theorem FL7A2_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    FL7A2 M (T • τ) = TθL7A2 *ᵥ FL7A2 M τ :=
  weight_zero_T (thetaQL7A2 M) eL7A2 (fun p τ => thetaQL7A2_T M p τ) τ

/-- **Covariance given `σ`**: if `σ(S) = Sθ` and `σ(T) = Tθ`, then `F(γ•τ) = σ(γ) F(τ)`. -/
theorem FL7A2_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invL7A2 M = 0)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 7 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθL7A2) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FL7A2 M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FL7A2 M τ :=
  covariant_of_S_T σ (FL7A2 M) (fun τ => by rw [hσS]; exact FL7A2_S hM τ)
    (fun τ => by rw [hσT]; exact FL7A2_T M τ)

/-- The `T`-exponent `q(γ_p) = r²/7 + s²/3` over ℚ. -/
def eQL7A2 (p : Fin 7 × Fin 3) : ℚ := ((p.1 : ℕ) : ℚ) ^ 2 / 7 + ((p.2 : ℕ) : ℚ) ^ 2 / 3

theorem eL7A2_sub (p : Fin 7 × Fin 3) : eL7A2 p - 1 / 3 = ((eQL7A2 p - 1 / 3 : ℚ) : ℝ) := by
  rw [eL7A2, eQL7A2]
  push_cast
  ring

/-- **`T`-fixed coordinates** (kernel-checked): `q(γ_p) ≡ 1/3` only for `p = (0, ±1)`. -/
theorem tfixed_L7A2 :
    ∀ p : Fin 7 × Fin 3, p ≠ (0, 1) → p ≠ (0, 2) → (eQL7A2 p - 1 / 3).den ≠ 1 := by
  decide +kernel

theorem sL7A2_vals :
    sL7A2 (0, 0) (0, 1) = 0 ∧ sL7A2 (0, 0) (0, 2) = 0 ∧ sL7A2 (0, 1) (0, 1) = 2 / 3 ∧
      sL7A2 (0, 1) (0, 2) = 4 / 3 := by
  have h0 : ((0 : Fin 7) : ℕ) = 0 := rfl
  have h0' : ((0 : Fin 3) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [sL7A2, h0, h0', h1, h2]
  norm_num

/-- **No common fixed vector** of `Sθ` and `Tθ` for `L₇ ⊕ A₂`. -/
theorem noInvariant_L7A2 (v : Fin 7 × Fin 3 → ℂ) (hS : SθL7A2 *ᵥ v = v)
    (hT : TθL7A2 *ᵥ v = v) : v = 0 := by
  obtain ⟨s1, s2, s3, s4⟩ := sL7A2_vals
  have hsupp : ∀ q, q ≠ (0, 1) → q ≠ (0, 2) → v q = 0 := fun q h1 h2 =>
    supp_of_T_fixed (fun p => eL7A2 p - 1 / 3) v hT q
      (eChar_ne_one_of_den (eL7A2_sub q) (tfixed_L7A2 q h1 h2))
  have hc : -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num))))
  refine no_invariant_of_two SθL7A2 v (0, 0) (0, 1) (0, 2) (by decide) (by decide) (by decide)
    hsupp hS ?_ ?_ ?_
  · simp only [SθL7A2, Matrix.of_apply, s1, s2]
  · simp only [SθL7A2, Matrix.of_apply, s1, neg_zero, eChar_zero, mul_one]
    exact hc
  · simp only [SθL7A2, Matrix.of_apply, s3, s4]
    exact one_sub_add_ne_zero _ _ _ cos_two_pi_neg_two_thirds

/-- **`hinv` of `pole_cancellation`** for `L₇ ⊕ A₂`, given `σ(S) = Sθ`, `σ(T) = Tθ`. -/
theorem noInvariant_sigma_L7A2 (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 7 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθL7A2) (hσT : (σ T : Matrix _ _ ℂ) = TθL7A2) :
    ∀ v : Fin 7 × Fin 3 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariant_L7A2

/-! ## `G₇⁻` (`M3Reverse`) -/

def FG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 21 → ℂ :=
  fun j => thetaQG7m M j τ / eta8 τ

/-- `Sθ_{jk} = -1/√21 · e(-16jk/21)`. -/
def SθG7m : Matrix (Fin 21) (Fin 21) ℂ :=
  Matrix.of fun j k => -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * eChar (-sG7m j k)

/-- `Tθ = diag e(8j²/21 - 1/3)`. -/
def TθG7m : Matrix (Fin 21) (Fin 21) ℂ := Matrix.diagonal fun j => eChar (eG7m j - 1 / 3)

theorem FG7m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0) (τ : ℍ) :
    FG7m M (S • τ) = SθG7m *ᵥ FG7m M τ :=
  weight_zero_S (thetaQG7m M) _ sG7m (fun j _ hτ => thetaQG7m_S hM j hτ) τ

theorem FG7m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : FG7m M (T • τ) = TθG7m *ᵥ FG7m M τ :=
  weight_zero_T (thetaQG7m M) eG7m (fun j τ => thetaQG7m_T M j τ) τ

theorem FG7m_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 21) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθG7m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FG7m M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FG7m M τ :=
  covariant_of_S_T σ (FG7m M) (fun τ => by rw [hσS]; exact FG7m_S hM τ)
    (fun τ => by rw [hσT]; exact FG7m_T M τ)

/-- The `O(D)`-twisted vector `(F_{13j})_j` satisfies the same laws (`thetaQG7m_S_o`). -/
theorem FG7m_o_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG7m M = 0) (τ : ℍ) :
    (fun j => FG7m M (S • τ) (oG7m j)) = SθG7m *ᵥ fun j => FG7m M τ (oG7m j) :=
  weight_zero_S (fun j => thetaQG7m M (oG7m j)) _ sG7m (fun j _ hτ => thetaQG7m_S_o hM j hτ) τ

theorem FG7m_o_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    (fun j => FG7m M (T • τ) (oG7m j)) = TθG7m *ᵥ fun j => FG7m M τ (oG7m j) :=
  weight_zero_T (fun j => thetaQG7m M (oG7m j)) eG7m (fun j τ => thetaQG7m_T_o M j τ) τ

def eQG7m (j : Fin 21) : ℚ := 8 * ((j : ℕ) : ℚ) ^ 2 / 21

theorem eG7m_sub (j : Fin 21) : eG7m j - 1 / 3 = ((eQG7m j - 1 / 3 : ℚ) : ℝ) := by
  rw [eG7m, eQG7m]
  push_cast
  ring

/-- **No `T`-fixed coordinate** for `G₇⁻` (kernel-checked; line 3707). -/
theorem tfixed_G7m : ∀ j : Fin 21, (eQG7m j - 1 / 3).den ≠ 1 := by
  decide +kernel

theorem noInvariant_G7m (v : Fin 21 → ℂ) (_hS : SθG7m *ᵥ v = v) (hT : TθG7m *ᵥ v = v) :
    v = 0 :=
  funext fun j => supp_of_T_fixed (fun k => eG7m k - 1 / 3) v hT j
    (eChar_ne_one_of_den (eG7m_sub j) (tfixed_G7m j))

theorem noInvariant_sigma_G7m (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 21) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθG7m) :
    ∀ v : Fin 21 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariant_G7m

/-! ## `A₁ ⊕ A₁ ⊕ A₂` (`M6First`) -/

def FA1A1A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 2 × Fin 2 × Fin 3 → ℂ :=
  fun p => thetaQA1A1A2 M p τ / eta8 τ

/-- `Sθ_{pq} = -1/√12 · e(-(aa'/2 + bb'/2 + 2ss'/3))`. -/
def SθA1A1A2 : Matrix (Fin 2 × Fin 2 × Fin 3) (Fin 2 × Fin 2 × Fin 3) ℂ :=
  Matrix.of fun p q => -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * eChar (-sA1A1A2 p q)

def TθA1A1A2 : Matrix (Fin 2 × Fin 2 × Fin 3) (Fin 2 × Fin 2 × Fin 3) ℂ :=
  Matrix.diagonal fun p => eChar (eA1A1A2 p - 1 / 3)

theorem FA1A1A2_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invA1A1A2 M = 0) (τ : ℍ) :
    FA1A1A2 M (S • τ) = SθA1A1A2 *ᵥ FA1A1A2 M τ :=
  weight_zero_S (thetaQA1A1A2 M) _ sA1A1A2 (fun p _ hτ => thetaQA1A1A2_S hM p hτ) τ

theorem FA1A1A2_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) :
    FA1A1A2 M (T • τ) = TθA1A1A2 *ᵥ FA1A1A2 M τ :=
  weight_zero_T (thetaQA1A1A2 M) eA1A1A2 (fun p τ => thetaQA1A1A2_T M p τ) τ

theorem FA1A1A2_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invA1A1A2 M = 0)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθA1A1A2) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FA1A1A2 M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FA1A1A2 M τ :=
  covariant_of_S_T σ (FA1A1A2 M) (fun τ => by rw [hσS]; exact FA1A1A2_S hM τ)
    (fun τ => by rw [hσT]; exact FA1A1A2_T M τ)

def eQA1A1A2 (p : Fin 2 × Fin 2 × Fin 3) : ℚ :=
  ((p.1 : ℕ) : ℚ) ^ 2 / 4 + ((p.2.1 : ℕ) : ℚ) ^ 2 / 4 + ((p.2.2 : ℕ) : ℚ) ^ 2 / 3

theorem eA1A1A2_sub (p : Fin 2 × Fin 2 × Fin 3) :
    eA1A1A2 p - 1 / 3 = ((eQA1A1A2 p - 1 / 3 : ℚ) : ℝ) := by
  rw [eA1A1A2, eQA1A1A2]
  push_cast
  ring

/-- **`T`-fixed coordinates** (kernel-checked): only `(0, 0, ±1)`. -/
theorem tfixed_A1A1A2 : ∀ p : Fin 2 × Fin 2 × Fin 3, p ≠ (0, 0, 1) → p ≠ (0, 0, 2) →
    (eQA1A1A2 p - 1 / 3).den ≠ 1 := by
  decide +kernel

theorem sA1A1A2_vals :
    sA1A1A2 (0, 0, 0) (0, 0, 1) = 0 ∧ sA1A1A2 (0, 0, 0) (0, 0, 2) = 0 ∧
      sA1A1A2 (0, 0, 1) (0, 0, 1) = 2 / 3 ∧ sA1A1A2 (0, 0, 1) (0, 0, 2) = 4 / 3 := by
  have h0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  have h0' : ((0 : Fin 3) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [sA1A1A2, h0, h0', h1, h2]
  norm_num

theorem noInvariant_A1A1A2 (v : Fin 2 × Fin 2 × Fin 3 → ℂ) (hS : SθA1A1A2 *ᵥ v = v)
    (hT : TθA1A1A2 *ᵥ v = v) : v = 0 := by
  obtain ⟨s1, s2, s3, s4⟩ := sA1A1A2_vals
  have hsupp : ∀ q, q ≠ (0, 0, 1) → q ≠ (0, 0, 2) → v q = 0 := fun q h1 h2 =>
    supp_of_T_fixed (fun p => eA1A1A2 p - 1 / 3) v hT q
      (eChar_ne_one_of_den (eA1A1A2_sub q) (tfixed_A1A1A2 q h1 h2))
  have hc : -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num))))
  refine no_invariant_of_two SθA1A1A2 v (0, 0, 0) (0, 0, 1) (0, 0, 2) (by decide) (by decide)
    (by decide) hsupp hS ?_ ?_ ?_
  · simp only [SθA1A1A2, Matrix.of_apply, s1, s2]
  · simp only [SθA1A1A2, Matrix.of_apply, s1, neg_zero, eChar_zero, mul_one]
    exact hc
  · simp only [SθA1A1A2, Matrix.of_apply, s3, s4]
    exact one_sub_add_ne_zero _ _ _ cos_two_pi_neg_two_thirds

theorem noInvariant_sigma_A1A1A2
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθA1A1A2) :
    ∀ v : Fin 2 × Fin 2 × Fin 3 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariant_A1A1A2

/-! ## `G₆⁻` (`M6Reverse`) -/

def FG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : Fin 2 × Fin 2 × Fin 3 → ℂ :=
  fun p => thetaQG6m M p τ / eta8 τ

def SθG6m : Matrix (Fin 2 × Fin 2 × Fin 3) (Fin 2 × Fin 2 × Fin 3) ℂ :=
  Matrix.of fun p q => -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * eChar (-sG6m p q)

def TθG6m : Matrix (Fin 2 × Fin 2 × Fin 3) (Fin 2 × Fin 2 × Fin 3) ℂ :=
  Matrix.diagonal fun p => eChar (eG6m p - 1 / 3)

theorem FG6m_S {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG6m M = 0) (τ : ℍ) :
    FG6m M (S • τ) = SθG6m *ᵥ FG6m M τ :=
  weight_zero_S (thetaQG6m M) _ sG6m (fun p _ hτ => thetaQG6m_S hM p hτ) τ

theorem FG6m_T (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℍ) : FG6m M (T • τ) = TθG6m *ᵥ FG6m M τ :=
  weight_zero_T (thetaQG6m M) eG6m (fun p τ => thetaQG6m_T M p τ) τ

theorem FG6m_covariant {M : Matrix (Fin 4) (Fin 4) ℚ} (hM : pairTrace invG6m M = 0)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθG6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FG6m M (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FG6m M τ :=
  covariant_of_S_T σ (FG6m M) (fun τ => by rw [hσS]; exact FG6m_S hM τ)
    (fun τ => by rw [hσT]; exact FG6m_T M τ)

def eQG6m (p : Fin 2 × Fin 2 × Fin 3) : ℚ :=
  3 / 4 * ((p.1 : ℕ) : ℚ) ^ 2 + 3 / 4 * ((p.2.1 : ℕ) : ℚ) ^ 2 + 2 / 3 * ((p.2.2 : ℕ) : ℚ) ^ 2 +
    ((p.1 : ℕ) : ℚ) * ((p.2.1 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ) * ((p.2.2 : ℕ) : ℚ) -
    ((p.2.1 : ℕ) : ℚ) * ((p.2.2 : ℕ) : ℚ)

theorem eG6m_sub (p : Fin 2 × Fin 2 × Fin 3) : eG6m p - 1 / 3 = ((eQG6m p - 1 / 3 : ℚ) : ℝ) := by
  rw [eG6m, eQG6m]
  push_cast
  ring

/-- **No `T`-fixed coordinate** for `G₆⁻` (kernel-checked; line 3770). -/
theorem tfixed_G6m : ∀ p : Fin 2 × Fin 2 × Fin 3, (eQG6m p - 1 / 3).den ≠ 1 := by
  decide +kernel

theorem noInvariant_G6m (v : Fin 2 × Fin 2 × Fin 3 → ℂ) (_hS : SθG6m *ᵥ v = v)
    (hT : TθG6m *ᵥ v = v) : v = 0 :=
  funext fun p => supp_of_T_fixed (fun q => eG6m q - 1 / 3) v hT p
    (eChar_ne_one_of_den (eG6m_sub p) (tfixed_G6m p))

theorem noInvariant_sigma_G6m (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 3) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθG6m) :
    ∀ v : Fin 2 × Fin 2 × Fin 3 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariant_G6m

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.weight_zero_S
#print axioms HaagerupIzumi.C8.Theta.weight_zero_T
#print axioms HaagerupIzumi.C8.Theta.FL7A2_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariant_sigma_L7A2
#print axioms HaagerupIzumi.C8.Theta.FG7m_covariant
#print axioms HaagerupIzumi.C8.Theta.FG7m_o_S
#print axioms HaagerupIzumi.C8.Theta.noInvariant_sigma_G7m
#print axioms HaagerupIzumi.C8.Theta.FA1A1A2_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariant_sigma_A1A1A2
#print axioms HaagerupIzumi.C8.Theta.FG6m_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariant_sigma_G6m
