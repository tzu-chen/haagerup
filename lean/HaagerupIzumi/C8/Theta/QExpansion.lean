module

public import HaagerupIzumi.C8.Theta.LatticeData
public import HaagerupIzumi.C8.ProofMapConcreteCharacters

@[expose] public section

/-!
# `q`-expansions of the coset theta series

W6 phase 2, plan item 2 (`Theta/W6_PLAN.md`).  The theta tables of the proof of Proposition
`prop:near-group-current-obstructions` (`Theta/M3First` … `M6Reverse`, lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) are stated for the coefficients
`thetaCoeff G g H e = ∑_{x ∈ g + L, (x,x)/2 = e} H(x)` (`Theta/Basic`, ℚ coordinates).  Here we
connect them with the analytic theta series of `LatticeTheta`/`LatticeThetaHarmonic`:

* `shell_finite`: the shells of a positive definite lattice are finite;
* `latticeThetaQ_eq_tsum_thetaCoeff`, `latticeTheta_eq_tsum_thetaCount`: for `Im τ > 0`,
  `Θ_{H,g}(τ) = ∑_{e ∈ ℚ} thetaCoeff G g H e · q^e`, `q^e = exp(2πi e τ)`, with `H = quadOf M`
  (the form of `Theta/Harmonic`) — the lattice sum grouped by shells;
* `summable_norm_thetaCoeff`: `∑_e |thetaCoeff G g H e| e^{-2π e y} < ∞` for every `y > 0`;
* `tsum_rat_eq_tsum_nat`: a series supported on exponents `λ + ℕ` rewritten in the `ℕ`-indexed
  form of `ProofMap.qseries_coeff_eq_zero`;
* `qcoeff_eq_of_tsum_eq`: **uniqueness of coefficients** of such `q^{λ+ℕ}`-series, from the
  Tannery-based `ProofMap.qseries_coeff_eq_zero` (`ProofMapConcreteCharacters`).

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex Matrix

namespace HaagerupIzumi.C8
namespace Theta

/-! ## From the rational coordinates of `Theta/Basic` to the real forms -/

theorem ratVec_cosetPt (g : Fin 4 → ℚ) (n : Fin 4 → ℤ) :
    ratVec (cosetPt g n) = ratVec g + intVec n := by
  funext i
  simp [ratVec, intVec, cosetPt]

theorem dotProduct_map_mulVec_eq_gramNorm (Gz : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℚ) :
    x ⬝ᵥ (Gz.map (Int.cast : ℤ → ℚ) *ᵥ x) = gramNorm Gz x := by
  simp only [gramNorm, gramBil, dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Q_G(x) = 2 · energy`. -/
theorem qf_gramR_ratVec_eq_energy (Gz : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℚ) :
    qf (gramR Gz) (ratVec x) = 2 * ((energy Gz x : ℚ) : ℝ) := by
  rw [qf_gramR_ratVec, dotProduct_map_mulVec_eq_gramNorm, energy]
  push_cast
  ring

theorem dotProduct_mulVec_eq_quadOf (M : Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → ℚ) :
    x ⬝ᵥ (M *ᵥ x) = quadOf M x := by
  simp only [quadOf, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The real weight `Q_M` at rational points is `quadOf M` (`Theta/Harmonic`). -/
theorem qf_map_ratVec_eq_quadOf (M : Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → ℚ) :
    qf (M.map (Rat.cast : ℚ → ℝ)) (ratVec x) = ((quadOf M x : ℚ) : ℝ) := by
  rw [qf_map_ratVec, dotProduct_mulVec_eq_quadOf]

/-! ## Finiteness of shells -/

/-- The shells `{n | (g+n, g+n)/2 = e}` of a positive definite lattice are finite. -/
theorem shell_finite {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef) (g : Fin 4 → ℚ)
    (e : ℚ) : (shell Gz g e).Finite := by
  obtain ⟨P, hP, hdet⟩ := exists_factor_of_posDef hG
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hdet
  let B : Fin 4 → ℤ := fun i => ⌈|((g i : ℚ) : ℝ)| + 1 + 2 * ((e : ℚ) : ℝ) / c⌉
  refine (Set.Finite.pi (t := fun i => Set.Icc (-B i) (B i)) fun i => Set.finite_Icc _ _).subset
    fun n hn i _ => ?_
  have hq : qf (gramR Gz) (ratVec g + intVec n) = 2 * ((e : ℚ) : ℝ) := by
    rw [← ratVec_cosetPt, qf_gramR_ratVec_eq_energy, show energy Gz (cosetPt g n) = e from hn]
  have hx := hcoer (ratVec g + intVec n)
  rw [← qf_transpose_mul_self, hP, hq] at hx
  have hxx : (ratVec g + intVec n) ⬝ᵥ (ratVec g + intVec n) ≤ 2 * ((e : ℚ) : ℝ) / c := by
    rw [le_div_iff₀ hc]
    linarith
  have habs := (abs_coord_le (ratVec g + intVec n) i).trans (by linarith : 1 +
    (ratVec g + intVec n) ⬝ᵥ (ratVec g + intVec n) ≤ 1 + 2 * ((e : ℚ) : ℝ) / c)
  have hni : (ratVec g + intVec n) i = ((g i : ℚ) : ℝ) + ((n i : ℤ) : ℝ) := rfl
  rw [hni] at habs
  have hB : |((g i : ℚ) : ℝ)| + 1 + 2 * ((e : ℚ) : ℝ) / c ≤ ((B i : ℤ) : ℝ) := Int.le_ceil _
  obtain ⟨h1, h2⟩ := abs_le.1 habs
  have hg1 := neg_abs_le ((g i : ℚ) : ℝ)
  have hg2 := le_abs_self ((g i : ℚ) : ℝ)
  constructor
  · have : -((B i : ℤ) : ℝ) ≤ ((n i : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  · have : ((n i : ℤ) : ℝ) ≤ ((B i : ℤ) : ℝ) := by linarith
    exact_mod_cast this

/-! ## The shell decomposition -/

/-- A sum over a finite set of indices written as a `tsum` over the set. -/
theorem tsum_subtype_eq_finsum {β : Type*} {s : Set β} (hs : s.Finite) (h : β → ℚ) :
    ∑' b : s, ((h b : ℚ) : ℂ) = (((∑ᶠ b ∈ s, h b : ℚ)) : ℂ) := by
  classical
  rw [tsum_subtype s (fun b => ((h b : ℚ) : ℂ)),
    tsum_eq_sum (s := hs.toFinset) (fun b hb => Set.indicator_of_notMem
      (by simpa using hb) _),
    finsum_mem_eq_finite_toFinset_sum _ hs]
  push_cast
  exact Finset.sum_congr rfl fun b hb => Set.indicator_of_mem (hs.mem_toFinset.1 hb) _

/-- `|thetaCoeff| ≤` the sum of the absolute values over the shell. -/
theorem norm_finsum_le_tsum_norm {β : Type*} {s : Set β} (hs : s.Finite) (h : β → ℚ) :
    ‖(((∑ᶠ b ∈ s, h b : ℚ)) : ℂ)‖ ≤ ∑' b : s, |((h b : ℚ) : ℝ)| := by
  classical
  rw [← tsum_subtype_eq_finsum hs h]
  have hsum : Summable fun b : s => |((h b : ℚ) : ℝ)| := by
    have := hs.fintype
    exact (hasSum_fintype _).summable
  refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
  · simpa [Complex.norm_ratCast] using hsum
  · exact tsum_congr fun b => by simp [Complex.norm_ratCast]

/-- The lattice sum written with the `ℚ`-coordinates of `Theta/Basic`. -/
theorem latticeThetaQ_term (Gz : Matrix (Fin 4) (Fin 4) ℤ) (M : Matrix (Fin 4) (Fin 4) ℚ)
    (g : Fin 4 → ℚ) (τ : ℂ) (m : Fin 4 → ℤ) :
    (qf (M.map (Rat.cast : ℚ → ℝ)) (ratVec g + intVec m) : ℂ) *
        cexp (π * I * τ * (qf (gramR Gz) (ratVec g + intVec m) : ℂ)) =
      ((quadOf M (cosetPt g m) : ℚ) : ℂ) *
        cexp (2 * π * I * ((energy Gz (cosetPt g m) : ℚ) : ℂ) * τ) := by
  rw [← ratVec_cosetPt, qf_map_ratVec_eq_quadOf, qf_gramR_ratVec_eq_energy]
  push_cast
  congr 2
  ring

/-- Absolute convergence of the lattice sum with the weight `quadOf M`. -/
theorem summable_norm_latticeThetaQ_term {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    (hG : (gramR Gz).PosDef) (M : Matrix (Fin 4) (Fin 4) ℚ) (g : Fin 4 → ℚ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    Summable fun m : Fin 4 → ℤ => ‖((quadOf M (cosetPt g m) : ℚ) : ℂ) *
      cexp (2 * π * I * ((energy Gz (cosetPt g m) : ℚ) : ℂ) * τ)‖ := by
  obtain ⟨P, hP, hdet⟩ := exists_factor_of_posDef hG
  have h := summable_norm_translates (translatesSummable_qgaussCM hdet (a := -I * τ)
    (by rwa [re_neg_I_mul]) (M.map (Rat.cast : ℚ → ℝ))) (ratVec g)
  refine h.congr fun m => ?_
  rw [← latticeThetaQ_term, qgaussCM_apply, gaussCM_apply, ← qf_transpose_mul_self, hP]
  congr 3
  ring

/-- **Shell decomposition**: `Θ_{H,g}(τ) = ∑_{e ∈ ℚ} thetaCoeff G g H e · q^e` with
`H = quadOf M`, for `Im τ > 0`. -/
theorem latticeThetaQ_eq_tsum_thetaCoeff {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    (hG : (gramR Gz).PosDef) (M : Matrix (Fin 4) (Fin 4) ℚ) (g : Fin 4 → ℚ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    latticeThetaQ (gramR Gz) (M.map (Rat.cast : ℚ → ℝ)) (ratVec g) τ =
      ∑' e : ℚ, ((thetaCoeff Gz g (quadOf M) e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) := by
  unfold latticeThetaQ
  simp only [latticeThetaQ_term]
  have hsum := (summable_norm_latticeThetaQ_term hG M g hτ).of_norm
  rw [← (hsum.hasSum.tsum_fiberwise fun m => energy Gz (cosetPt g m)).tsum_eq]
  refine tsum_congr fun e => ?_
  show ∑' b : shell Gz g e, ((quadOf M (cosetPt g b) : ℚ) : ℂ) *
      cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * τ) = _
  have h1 : ∀ b : shell Gz g e, ((quadOf M (cosetPt g b) : ℚ) : ℂ) *
      cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * τ) =
      ((quadOf M (cosetPt g b) : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) := by
    intro b
    rw [show energy Gz (cosetPt g b) = e from b.2]
  rw [tsum_congr h1, tsum_mul_right,
    tsum_subtype_eq_finsum (shell_finite hG g e) (fun b => quadOf M (cosetPt g b))]
  rfl

/-- **Shell decomposition, no weight**: `Θ_g(τ) = ∑_{e ∈ ℚ} thetaCount G g e · q^e`. -/
theorem latticeTheta_eq_tsum_thetaCount {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    (hG : (gramR Gz).PosDef) (g : Fin 4 → ℚ) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeTheta (gramR Gz) (ratVec g) τ =
      ∑' e : ℚ, ((thetaCount Gz g e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) := by
  have hsum : Summable fun m : Fin 4 → ℤ =>
      cexp (2 * π * I * ((energy Gz (cosetPt g m) : ℚ) : ℂ) * τ) := by
    refine (summable_norm_latticeTheta hG (ratVec g) hτ).of_norm.congr fun m => ?_
    rw [← ratVec_cosetPt, qf_gramR_ratVec_eq_energy]
    push_cast
    congr 1
    ring
  have hL : latticeTheta (gramR Gz) (ratVec g) τ =
      ∑' m : Fin 4 → ℤ, cexp (2 * π * I * ((energy Gz (cosetPt g m) : ℚ) : ℂ) * τ) := by
    unfold latticeTheta
    refine tsum_congr fun m => ?_
    rw [← ratVec_cosetPt, qf_gramR_ratVec_eq_energy]
    push_cast
    congr 1
    ring
  rw [hL, ← (hsum.hasSum.tsum_fiberwise fun m => energy Gz (cosetPt g m)).tsum_eq]
  refine tsum_congr fun e => ?_
  show ∑' b : shell Gz g e, cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * τ) = _
  have h1 : ∀ b : shell Gz g e, cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * τ) =
      ((1 : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) := by
    intro b
    rw [show energy Gz (cosetPt g b) = e from b.2, Rat.cast_one, one_mul]
  rw [tsum_congr h1, tsum_mul_right,
    tsum_subtype_eq_finsum (shell_finite hG g e) (fun _ => (1 : ℚ))]
  rfl

/-- Summability of the coefficients at every height. -/
theorem summable_norm_thetaCoeff {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (M : Matrix (Fin 4) (Fin 4) ℚ) (g : Fin 4 → ℚ) {y : ℝ} (hy : 0 < y) :
    Summable fun e : ℚ => ‖((thetaCoeff Gz g (quadOf M) e : ℚ) : ℂ)‖ *
      Real.exp (-2 * π * (e : ℝ) * y) := by
  have hτ : 0 < ((y : ℂ) * I).im := by simpa using hy
  have hs := summable_norm_latticeThetaQ_term hG M g hτ
  have hfib := hs.hasSum.tsum_fiberwise fun m => energy Gz (cosetPt g m)
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) hfib.summable
  show _ ≤ ∑' b : shell Gz g e, ‖((quadOf M (cosetPt g b) : ℚ) : ℂ) *
      cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * ((y : ℂ) * I))‖
  have hE : ∀ b : shell Gz g e, ‖((quadOf M (cosetPt g b) : ℚ) : ℂ) *
      cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * ((y : ℂ) * I))‖ =
      |((quadOf M (cosetPt g b) : ℚ) : ℝ)| * Real.exp (-2 * π * (e : ℝ) * y) := by
    intro b
    have hre : 2 * (π : ℂ) * I * ((e : ℚ) : ℂ) * ((y : ℂ) * I) =
        ((-2 * π * ((e : ℚ) : ℝ) * y : ℝ) : ℂ) := by
      push_cast
      linear_combination (2 * (π : ℂ) * (e : ℂ) * (y : ℂ)) * I_sq
    rw [show energy Gz (cosetPt g b) = e from b.2, norm_mul, Complex.norm_ratCast, hre,
      Complex.norm_exp_ofReal]
  rw [tsum_congr hE, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (norm_finsum_le_tsum_norm (shell_finite hG g e) _)
    (Real.exp_pos _).le

/-! ## Uniqueness of coefficients of `q^{λ + ℕ}`-series -/

/-- A series over rational exponents supported on `λ + ℕ` in the `ℕ`-indexed form of
`ProofMap.qseries_coeff_eq_zero`. -/
theorem tsum_rat_eq_tsum_nat (lam : ℚ) (a : ℚ → ℂ)
    (ha : ∀ e, a e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam) (τ : ℂ) :
    ∑' e : ℚ, a e * cexp (2 * π * I * (e : ℂ) * τ) =
      ∑' n : ℕ, a ((n : ℚ) + lam) * cexp (2 * π * I * ((((n : ℝ) + (lam : ℝ)) : ℝ) : ℂ) * τ) := by
  have hinj : Function.Injective fun n : ℕ => (n : ℚ) + lam := fun x y h => by
    simpa using h
  refine ((hinj.tsum_eq (f := fun e : ℚ => a e * cexp (2 * π * I * (e : ℂ) * τ))
    fun e he => ?_).symm).trans (tsum_congr fun n => ?_)
  · have hae : a e ≠ 0 := fun h0 => he (by simp [h0])
    obtain ⟨n, hn⟩ := ha e hae
    exact ⟨n, hn.symm⟩
  · simp only [Rat.cast_add, Rat.cast_natCast, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_ratCast]

/-- **Uniqueness of `q`-expansion coefficients** for series supported on `λ + ℕ`, absolutely
convergent at every height: equality on `ℍ` forces equality of all coefficients. -/
theorem qcoeff_eq_of_tsum_eq (lam : ℚ) (a b : ℚ → ℂ)
    (ha : ∀ e, a e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam)
    (hb : ∀ e, b e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam)
    (hsa : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖a e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hsb : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖b e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (h : ∀ τ : UpperHalfPlane, ∑' e : ℚ, a e * cexp (2 * π * I * (e : ℂ) * τ) =
      ∑' e : ℚ, b e * cexp (2 * π * I * (e : ℂ) * τ)) :
    ∀ e, a e = b e := by
  have hinj : Function.Injective fun n : ℕ => (n : ℚ) + lam := fun x y h => by
    simpa using h
  have hsn : ∀ (c : ℚ → ℂ) (y : ℝ), 0 < y →
      (∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖c e‖ * Real.exp (-2 * π * (e : ℝ) * y)) →
      Summable fun n : ℕ => ‖c ((n : ℚ) + lam)‖ *
        Real.exp (-2 * π * ((n : ℝ) + (lam : ℝ)) * y) := by
    intro c y hy hc
    refine ((hc y hy).comp_injective hinj).congr fun n => ?_
    simp only [Function.comp_apply, Rat.cast_add, Rat.cast_natCast]
  have hc : ∀ y : ℝ, 0 < y → Summable fun n : ℕ => ‖a ((n : ℚ) + lam) - b ((n : ℚ) + lam)‖ *
      Real.exp (-2 * π * ((n : ℝ) + (lam : ℝ)) * y) := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hsn a y hy hsa).add (hsn b y hy hsb))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
  have h0 : ∀ τ : UpperHalfPlane, ∑' n : ℕ, (a ((n : ℚ) + lam) - b ((n : ℚ) + lam)) *
      cexp (2 * π * I * ((((n : ℝ) + (lam : ℝ)) : ℝ) : ℂ) * τ) = 0 := by
    intro τ
    have h1 := h τ
    rw [tsum_rat_eq_tsum_nat lam a ha, tsum_rat_eq_tsum_nat lam b hb] at h1
    have hs1 := ProofMap.summable_qterm (lam : ℝ) (fun n => a ((n : ℚ) + lam))
      (fun y hy => hsn a y hy hsa) τ
    have hs2 := ProofMap.summable_qterm (lam : ℝ) (fun n => b ((n : ℚ) + lam))
      (fun y hy => hsn b y hy hsb) τ
    simp only [sub_mul]
    rw [hs1.tsum_sub hs2, h1, sub_self]
  have hzero := ProofMap.qseries_coeff_eq_zero (lam : ℝ)
    (fun n => a ((n : ℚ) + lam) - b ((n : ℚ) + lam)) hc h0
  intro e
  by_contra hne
  have hor : a e ≠ 0 ∨ b e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (hcon.1.trans hcon.2.symm)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e = (n : ℚ) + lam := hor.elim (ha e) (hb e)
  exact hne (by rw [hn]; exact sub_eq_zero.1 (hzero n))

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.shell_finite
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_eq_tsum_thetaCoeff
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_eq_tsum_thetaCount
#print axioms HaagerupIzumi.C8.Theta.summable_norm_thetaCoeff
#print axioms HaagerupIzumi.C8.Theta.qcoeff_eq_of_tsum_eq
