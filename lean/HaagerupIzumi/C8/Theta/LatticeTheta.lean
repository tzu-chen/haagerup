module

public import HaagerupIzumi.C8.Theta.PoissonGaussian

@[expose] public section

/-!
# Lattice theta series and their modular `S`- and `T`-transformations

Third step of work item W6 (`C8/ROADMAP.md`; the theta identities in the proof of Proposition
`prop:near-group-current-obstructions`, lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).

## Conventions

A lattice is `L = ℤ^d` with a Gram matrix `G` (real, positive definite; for the integral case
`G = gramR Gz` with `Gz : Matrix d d ℤ`), so `(x, y) = x·Gy` and `Q_G(x) = (x, x)` (`qf`).  The
dual lattice is `L' = G⁻¹ℤ^d`; its points are `G⁻¹ s`, `s ∈ ℤ^d`.  For a shift `γ ∈ ℝ^d` the
theta series of the coset `γ + L` is (`latticeTheta`)
`Θ_γ(τ) = ∑_{m ∈ ℤ^d} exp(πiτ Q_G(γ + m)) = ∑_{x ∈ γ + L} q^{(x,x)/2}`, `q = e^{2πiτ}`,
the convention of `Theta/Basic.lean` (`q`-exponent `(x,x)/2`).

## Main results

* `latticeTheta_S_poisson` (any positive definite `G`, any `γ`, `Im τ > 0`):
  `Θ_γ(-1/τ) = (det G)^{-1/2} (-iτ)^{d/2} ∑_{k ∈ ℤ^d} exp(πiτ Q_{G⁻¹}(k)) e(k·γ)`,
  i.e. the dual-lattice theta series; `(-iτ)^{d/2} = (τ/i)^{d/2}` is the principal branch.
* `latticeTheta_S` (integral `G`, `γ = G⁻¹ s ∈ L'`, `R` a complete system of representatives
  of `ℤ^d / Gℤ^d ≅ L'/L`, given as the hypothesis `hR`):
  `Θ_γ(-1/τ) = (det G)^{-1/2} (-iτ)^{d/2} ∑_{r ∈ R} e((γ, δ_r)) Θ_{δ_r}(τ)`, `δ_r = G⁻¹ r`.
  Here `s` and `r` are vectors of `ℤ^d`, not the coset labels `(r, s)` of the tables; the
  bridge is `G⁻¹ ![0, r, s, 0] = cosetL7A2 r s` (`m3First_dual_generated`) and
  `G⁻¹ ((9r+7s) e₀) = cosetG7m r s` (`m3Reverse_dual_cyclic`), see `Theta/LatticeData`.
* `cexp_qf_add_one`, the termwise `T`-law `e(Q_G(γ+m)/2) = e(Q_G(γ)/2)` for even integral
  `G`, `γ ∈ L'`, `m ∈ ℤ^d`; hence `latticeTheta_T`: `Θ_γ(τ + 1) = e(Q_G(γ)/2) Θ_γ(τ)`.
* `latticeTheta_add_intVec`: `Θ_γ` depends only on the coset `γ + L`; `latticeTheta_neg`:
  `Θ_{-γ} = Θ_γ`.

## Which representation

With `q(γ) = Q_G(γ)/2`, `latticeTheta_T` is `T ↦ e(q(γ))`, the convention of Borcherds'
Weil representation `ρ_L`, under which `Θ_L = (Θ_δ)_δ` has weight `d/2` (`L` positive
definite).  The matrix printed in `latticeTheta_S`, `c · (e(+(γ, δ)))`, equals `ρ_L(S) · C`
with `C : γ ↦ -γ`.  It agrees with `ρ_L(S)` on `C`-even vectors, such as `Θ_L` itself
(`latticeTheta_neg`), but together with `T` it does **not** define an `SL₂(ℤ)`-representation
on all of `ℂ[L'/L]` when `C ≠ 1` (e.g. for `L'/L ≅ ℤ/21`, `(S'T)³ = 1 ≠ S'² = C`).  For
vector-valued covariance (`covariant_of_S_T`) use the form with `e(-(γ, δ))`, obtained by
replacing `R` by `-R`; `Theta/LatticeData` states the four concrete lattices in that form.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex Matrix

namespace HaagerupIzumi.C8
namespace Theta

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The theta series `Θ_γ(τ) = ∑_{m ∈ ℤ^d} exp(πiτ Q_G(γ + m))` of the coset `γ + L`. -/
def latticeTheta (G : Matrix d d ℝ) (γ : d → ℝ) (τ : ℂ) : ℂ :=
  ∑' m : d → ℤ, cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))

/-! ## Preliminaries on positive definite forms -/

/-- `G = PᵀP` with `P` invertible. -/
theorem exists_factor_of_posDef {G : Matrix d d ℝ} (hG : G.PosDef) :
    ∃ P : Matrix d d ℝ, Pᵀ * P = G ∧ P.det ≠ 0 := by
  obtain ⟨P, rfl⟩ := exists_transpose_mul_self_eq_of_posDef hG
  refine ⟨P, rfl, fun h => ?_⟩
  have hpos := hG.det_pos
  rw [det_mul, det_transpose, h, mul_zero] at hpos
  exact lt_irrefl _ hpos

omit [Fintype d] [DecidableEq d] in
theorem transpose_eq_of_posDef {G : Matrix d d ℝ} (hG : G.PosDef) : Gᵀ = G := by
  have h : Gᴴ = G := hG.isHermitian
  rwa [conjTranspose_eq_transpose_of_trivial] at h

theorem isUnit_det_of_posDef {G : Matrix d d ℝ} (hG : G.PosDef) : IsUnit G.det :=
  isUnit_iff_ne_zero.2 hG.det_pos.ne'

omit [DecidableEq d] in
theorem qf_neg (G : Matrix d d ℝ) (x : d → ℝ) : qf G (-x) = qf G x := by
  simp only [qf, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

omit [DecidableEq d] in
/-- `Q_G(x + y) = Q_G(x) + 2 (y, x) + Q_G(y)` for symmetric `G`. -/
theorem qf_add {G : Matrix d d ℝ} (hGt : Gᵀ = G) (x y : d → ℝ) :
    qf G (x + y) = qf G x + 2 * (y ⬝ᵥ (G *ᵥ x)) + qf G y := by
  have h : x ⬝ᵥ (G *ᵥ y) = y ⬝ᵥ (G *ᵥ x) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hGt, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct]
  rw [h]
  ring

/-- `Q_{G⁻¹}(v + Gw) = Q_G(G⁻¹v + w)`. -/
theorem qf_inv_add_mulVec {G : Matrix d d ℝ} (hG : IsUnit G.det) (v w : d → ℝ) :
    qf G⁻¹ (v + G *ᵥ w) = qf G (G⁻¹ *ᵥ v + w) := by
  have h1 : G⁻¹ *ᵥ (v + G *ᵥ w) = G⁻¹ *ᵥ v + w := by
    rw [mulVec_add, mulVec_mulVec, nonsing_inv_mul G hG, one_mulVec]
  have h2 : G *ᵥ (G⁻¹ *ᵥ v + w) = v + G *ᵥ w := by
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv G hG, one_mulVec]
  rw [qf, qf, h1, h2, dotProduct_comm]

/-- `(Gw)·(G⁻¹u) = w·u` for symmetric invertible `G`. -/
theorem mulVec_dotProduct_inv_mulVec {G : Matrix d d ℝ} (hGt : Gᵀ = G) (hG : IsUnit G.det)
    (w u : d → ℝ) : (G *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ u) = w ⬝ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, hGt, mulVec_mulVec,
    nonsing_inv_mul G hG, one_mulVec]

/-! ## Convergence and elementary symmetries -/

theorem summable_norm_cexp_qf {G : Matrix d d ℝ} (hG : G.PosDef) {b : ℂ} (hb : 0 < b.re)
    (x : d → ℝ) :
    Summable fun m : d → ℤ => ‖cexp (-π * b * (qf G (x + intVec m) : ℂ))‖ := by
  obtain ⟨P, rfl, hdet⟩ := exists_factor_of_posDef hG
  obtain ⟨u, hu, -, hbound⟩ := exists_summable_gauss_bound hdet (mul_pos pi_pos hb) (∑ i, |x i|)
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hu
  rw [qf_transpose_mul_self, norm_cexp_neg_pi_mul]
  exact hbound m x fun i =>
    Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem re_neg_I_mul {τ : ℂ} : (-I * τ).re = τ.im := by
  rw [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

/-- The series defining `Θ_γ(τ)` converges absolutely for `Im τ > 0`. -/
theorem summable_norm_latticeTheta {G : Matrix d d ℝ} (hG : G.PosDef) (γ : d → ℝ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    Summable fun m : d → ℤ => ‖cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))‖ := by
  refine (summable_norm_cexp_qf hG (b := -I * τ) (by rwa [re_neg_I_mul]) γ).congr fun m => ?_
  congr 2
  ring

omit [DecidableEq d] in
/-- `Θ_γ` depends only on the coset `γ + ℤ^d`. -/
theorem latticeTheta_add_intVec (G : Matrix d d ℝ) (γ : d → ℝ) (n : d → ℤ) (τ : ℂ) :
    latticeTheta G (γ + intVec n) τ = latticeTheta G γ τ := by
  unfold latticeTheta
  conv_rhs => rw [← (Equiv.addLeft n).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addLeft, intVec_add, add_assoc]

omit [DecidableEq d] in
/-- `Θ_{-γ} = Θ_γ`. -/
theorem latticeTheta_neg (G : Matrix d d ℝ) (γ : d → ℝ) (τ : ℂ) :
    latticeTheta G (-γ) τ = latticeTheta G γ τ := by
  unfold latticeTheta
  rw [← (Equiv.neg (d → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  have h : -γ + intVec (Equiv.neg (d → ℤ) m) = -(γ + intVec m) := by
    rw [Equiv.neg_apply, intVec_neg, neg_add]
  rw [h, qf_neg]

/-! ## The `S`-transformation -/

/-- **`S`-transformation, Poisson form.**  For positive definite `G`, any shift `γ` and
`Im τ > 0`: `Θ_γ(-1/τ) = (det G)^{-1/2} (-iτ)^{d/2} ∑_{k ∈ ℤ^d} exp(πiτ Q_{G⁻¹}(k)) e(k·γ)`. -/
theorem latticeTheta_S_poisson {G : Matrix d d ℝ} (hG : G.PosDef) (γ : d → ℝ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    latticeTheta G γ (-1 / τ) =
      (((Real.sqrt G.det)⁻¹ : ℝ) : ℂ) * (-I * τ) ^ (Fintype.card d / 2 : ℂ) *
        ∑' k : d → ℤ, cexp (π * I * τ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ γ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have ha : 0 < (I / τ).re := by
    rw [Complex.div_re, Complex.I_re, Complex.I_im, zero_mul, zero_div, zero_add, one_mul]
    exact div_pos hτ (Complex.normSq_pos.2 hτ0)
  have e2 : (I / τ)⁻¹ = -I * τ := by
    rw [inv_div, div_eq_mul_inv, Complex.inv_I]
    ring
  have h := tsum_exp_qf_poisson hG ha γ
  rw [one_div, e2] at h
  unfold latticeTheta
  calc ∑' m : d → ℤ, cexp (π * I * (-1 / τ) * (qf G (γ + intVec m) : ℂ))
      = ∑' m : d → ℤ, cexp (-π * (I / τ) * (qf G (γ + intVec m) : ℂ)) :=
        tsum_congr fun m => by
          congr 1
          ring
    _ = _ := h
    _ = _ := by
        congr 1
        refine tsum_congr fun k => ?_
        congr 2
        ring

/-- The real Gram matrix of an integral Gram matrix. -/
def gramR (Gz : Matrix d d ℤ) : Matrix d d ℝ := Gz.map (Int.cast : ℤ → ℝ)

omit [DecidableEq d] in
theorem intVec_mulVec (Gz : Matrix d d ℤ) (m : d → ℤ) :
    intVec (Gz *ᵥ m) = gramR Gz *ᵥ intVec m := by
  ext i
  simp [intVec, gramR, mulVec, dotProduct]

/-- **`S`-transformation of the vector of coset theta series.**  Let `Gz` be an integral
Gram matrix with `G = gramR Gz` positive definite, and let `R ⊂ ℤ^d` be a complete system
of representatives of `ℤ^d / Gz ℤ^d` (hypothesis `hR`; `r ↦ G⁻¹ r` identifies it with
`L'/L`).  Then for `γ = G⁻¹ s ∈ L'` and `Im τ > 0`
`Θ_γ(-1/τ) = (det G)^{-1/2} (-iτ)^{d/2} ∑_{r ∈ R} e((γ, G⁻¹r)) Θ_{G⁻¹r}(τ)`,
where `(γ, G⁻¹r) = r·γ`.  (`s`, `r ∈ ℤ^d` here are not the coset labels of the tables; see the
module docstring for the bridge, and for the sign convention of the exponent.) -/
theorem latticeTheta_S {Gz : Matrix d d ℤ} (hG : (gramR Gz).PosDef) (R : Finset (d → ℤ))
    (hR : ∀ k : d → ℤ, ∃! p : R × (d → ℤ), (p.1 : d → ℤ) + Gz *ᵥ p.2 = k)
    (s : d → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeTheta (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) (-1 / τ) =
      (((Real.sqrt (gramR Gz).det)⁻¹ : ℝ) : ℂ) * (-I * τ) ^ (Fintype.card d / 2 : ℂ) *
        ∑ r ∈ R, eChar (intVec r ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec s)) *
          latticeTheta (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec r) τ := by
  set G := gramR Gz with hGdef
  set γ := G⁻¹ *ᵥ intVec s with hγ
  have hunit := isUnit_det_of_posDef hG
  have hGt := transpose_eq_of_posDef hG
  rw [latticeTheta_S_poisson hG γ hτ]
  congr 1
  have hFsum : Summable fun k : d → ℤ =>
      cexp (π * I * τ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ γ) := by
    refine (summable_norm_latticeTheta hG.inv 0 hτ).of_norm_bounded fun k => ?_
    rw [norm_mul, norm_eChar, mul_one, zero_add]
  let e : R × (d → ℤ) ≃ (d → ℤ) :=
    Equiv.ofBijective (fun p => (p.1 : d → ℤ) + Gz *ᵥ p.2)
      ((Function.bijective_iff_existsUnique _).2 hR)
  have hFe : Summable fun p : R × (d → ℤ) =>
      cexp (π * I * τ * (qf G⁻¹ (intVec (e p)) : ℂ)) * eChar (intVec (e p) ⬝ᵥ γ) :=
    e.summable_iff.2 hFsum
  rw [← e.tsum_eq, hFe.tsum_prod, tsum_fintype, ← Finset.sum_coe_sort R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [latticeTheta, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hv : intVec (e (r, m)) = intVec (r : d → ℤ) + G *ᵥ intVec m := by
    show intVec ((r : d → ℤ) + Gz *ᵥ m) = _
    rw [intVec_add, intVec_mulVec]
  rw [hv, qf_inv_add_mulVec hunit, add_dotProduct, hγ, mulVec_dotProduct_inv_mulVec hGt hunit,
    intVec_dotProduct, eChar_add, eChar_intCast, mul_one, mul_comm]

/-! ## The `T`-transformation -/

/-- **The termwise `T`-law** `e(Q_G(γ+m)/2) = e(Q_G(γ)/2)` for even integral `G`,
`γ = G⁻¹ s ∈ L'` and `m ∈ ℤ^d`, in the form
`exp(πi(τ+1) Q_G(γ+m)) = exp(πi Q_G(γ)) · exp(πiτ Q_G(γ+m))`.  Both `latticeTheta_T` and
`latticeThetaQ_T` are derived from it. -/
theorem cexp_qf_add_one {Gz : Matrix d d ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : d → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) (s m : d → ℤ) (τ : ℂ) :
    cexp (π * I * (τ + 1) * (qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s + intVec m) : ℂ)) =
      cexp (π * I * (qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) : ℂ)) *
        cexp (π * I * τ * (qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s + intVec m) : ℂ)) := by
  set G := gramR Gz with hGdef
  set γ := G⁻¹ *ᵥ intVec s with hγ
  have hunit := isUnit_det_of_posDef hG
  have hGt := transpose_eq_of_posDef hG
  have hGγ : G *ᵥ γ = intVec s := by
    rw [hγ, mulVec_mulVec, mul_nonsing_inv G hunit, one_mulVec]
  obtain ⟨k, hk⟩ := hEven m
  have hqm : qf G (intVec m) = ((m ⬝ᵥ (Gz *ᵥ m) : ℤ) : ℝ) := by
    rw [qf, hGdef, ← intVec_mulVec, intVec_dotProduct]
  have hq : qf G (γ + intVec m) = qf G γ + 2 * (((m ⬝ᵥ s : ℤ) : ℝ) + (k : ℝ)) := by
    rw [qf_add hGt, hGγ, intVec_dotProduct, hqm, hk]
    push_cast
    ring
  rw [hq]
  calc _ = cexp (π * I * (qf G γ : ℂ) +
          π * I * τ * ((qf G γ + 2 * (((m ⬝ᵥ s : ℤ) : ℝ) + (k : ℝ)) : ℝ) : ℂ)) *
        cexp (((m ⬝ᵥ s + k : ℤ) : ℂ) * (2 * π * I)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = _ := by
        rw [Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add]

/-- **`T`-transformation.**  For an even integral `G` (`m·Gz m` even for all `m`) and
`γ = G⁻¹ s ∈ L'`: `Θ_γ(τ + 1) = e(Q_G(γ)/2) Θ_γ(τ)`. -/
theorem latticeTheta_T {Gz : Matrix d d ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : d → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) (s : d → ℤ) (τ : ℂ) :
    latticeTheta (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) (τ + 1) =
      cexp (π * I * (qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) : ℂ)) *
        latticeTheta (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) τ := by
  unfold latticeTheta
  rw [← tsum_mul_left]
  exact tsum_congr fun m => cexp_qf_add_one hG hEven s m τ

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.latticeTheta_S_poisson
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_S
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_T
#print axioms HaagerupIzumi.C8.Theta.cexp_qf_add_one
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_add_intVec
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_neg
