module

public import HaagerupIzumi.C8.Theta.E2Theta

@[expose] public section

/-!
# Absolute convergence of the `q`-series of `F = -6 D₂ Θ`

W6 plan item 3, `F` orientations (`Theta/W6_PLAN.md`): the coefficients
`minusSixD2Coeff (thetaCount G g)` of `F = -6 D₂ Θ_{g+L}` (`E2Theta.minusSixSerre_theta_qexp`)
are absolutely summable at every height (`summable_norm_minusSixD2Coeff`), as needed by the
coefficient extraction `qcoeff_eq_lincomb` and the remainder bound
`isBoundedAtImInfty_tsum_div_eta8`.  The `E₂ Θ` part is the Cauchy product
(`cauchy_term`, `summable_norm_e2ThetaCoeff`).

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-- The coefficients of `E₂ Θ`: `∑_{0 ≤ j ≤ x} E₂[j] N(x - j)`. -/
def e2ThetaCoeff (N : ℚ → ℚ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (⌊x⌋₊ + 1), e2Coeff j * N (x - j)

/-- The `k`-th Cauchy-product term is the `E₂ Θ` term at the exponent `k + λ`. -/
theorem cauchy_term (N : ℚ → ℚ) (lam : ℚ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (z : ℍ) (k : ℕ) :
    ∑ kl ∈ Finset.antidiagonal k, ((e2Coeff kl.1 : ℚ) : ℂ) * cexp (2 * π * I * (kl.1 : ℂ) * z) *
        (((N ((kl.2 : ℚ) + lam) : ℚ) : ℂ) *
          cexp (2 * π * I * ((((kl.2 : ℚ) + lam : ℚ)) : ℂ) * z)) =
      ((e2ThetaCoeff N ((k : ℚ) + lam) : ℚ) : ℂ) *
        cexp (2 * π * I * ((((k : ℚ) + lam : ℚ)) : ℂ) * z) := by
  have hfloor : ⌊((k : ℚ) + lam)⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  rw [e2ThetaCoeff, hfloor, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Rat.cast_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have harg : (((k - i : ℕ) : ℚ) + lam) = (k : ℚ) + lam - i := by
    rw [Nat.cast_sub hik]
    ring
  simp only []
  rw [harg]
  have hexp : cexp (2 * π * I * ((i : ℕ) : ℂ) * z) *
      cexp (2 * π * I * ((((k : ℚ) + lam - i : ℚ)) : ℂ) * z) =
        cexp (2 * π * I * ((((k : ℚ) + lam : ℚ)) : ℂ) * z) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hexp]
  push_cast
  ring

/-- Absolute convergence of the `E₂ Θ` coefficients at every height. -/
theorem summable_norm_e2ThetaCoeff {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) {y : ℝ} (hy : 0 < y) :
    Summable fun x : ℚ => ‖((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ)‖ *
      Real.exp (-2 * π * (x : ℝ) * y) := by
  set lam := Int.fract (energy Gz g) with hlam
  have hlam0 : 0 ≤ lam := Int.fract_nonneg _
  have hlam1 : lam < 1 := Int.fract_lt_one _
  have hsupp : ∀ x, thetaCount Gz g x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lam :=
    fun x hx => thetaCoeff_support_fract hG hEven hg hx
  have hinj : Function.Injective fun n : ℕ => (n : ℚ) + lam := fun a b h => by simpa using h
  let τ₀ : ℍ := ⟨(y : ℂ) * I, by simpa using hy⟩
  have him : τ₀.im = y := by simp [τ₀, UpperHalfPlane.im]
  have hb : Summable fun n : ℕ => ‖((thetaCount Gz g ((n : ℚ) + lam) : ℚ) : ℂ) *
      cexp (2 * π * I * ((((n : ℚ) + lam : ℚ)) : ℂ) * τ₀)‖ := by
    refine ((summable_norm_thetaCount hG g τ₀.im_pos).comp_injective hinj).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [norm_qterm_rat]
  have hk := summable_norm_sum_mul_antidiagonal_of_summable_norm (summable_norm_E2_terms τ₀) hb
  have hk' : Summable fun k : ℕ => ‖((e2ThetaCoeff (thetaCount Gz g) ((k : ℚ) + lam) : ℚ) : ℂ) *
      cexp (2 * π * I * ((((k : ℚ) + lam : ℚ)) : ℂ) * τ₀)‖ := by
    refine hk.congr fun k => ?_
    rw [cauchy_term (thetaCount Gz g) lam hlam0 hlam1 τ₀ k]
  have hsuppC : ∀ x ∉ Set.range (fun n : ℕ => (n : ℚ) + lam),
      ‖((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ₀)‖ = 0 := by
    intro x hx
    have hsum0 : e2ThetaCoeff (thetaCount Gz g) x = 0 := by
      by_contra hne
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hj' : thetaCount Gz g (x - j) ≠ 0 := fun h0 => hj (by rw [h0, mul_zero])
      obtain ⟨n, hn⟩ := hsupp _ hj'
      exact hx ⟨n + j, by push_cast; linarith⟩
    rw [hsum0]
    simp
  have hQ := (hinj.summable_iff hsuppC).mp hk'
  refine hQ.congr fun x => ?_
  rw [norm_qterm_rat, him]

/-- **Absolute convergence of the `F = -6 D₂ Θ` coefficients** at every height. -/
theorem summable_norm_minusSixD2Coeff {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) {y : ℝ} (hy : 0 < y) :
    Summable fun x : ℚ => ‖((minusSixD2Coeff (thetaCount Gz g) x : ℚ) : ℂ)‖ *
      Real.exp (-2 * π * (x : ℝ) * y) := by
  have h1 : Summable fun x : ℚ => ‖((x * thetaCount Gz g x : ℚ) : ℂ)‖ *
      Real.exp (-2 * π * (x : ℝ) * y) := by
    have hw := summable_norm_thetaCoeff hG (Gz.map (Int.cast : ℤ → ℚ)) g hy
    refine (hw.mul_left (1 / 2)).congr fun x => ?_
    rw [thetaCoeff_quadOf_gram]
    have h2 : ((2 * x * thetaCount Gz g x : ℚ) : ℂ) = 2 * ((x * thetaCount Gz g x : ℚ) : ℂ) := by
      push_cast
      ring
    rw [h2, norm_mul]
    norm_num
    ring
  have h2 := summable_norm_e2ThetaCoeff hG hEven hg hy
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) ((h1.mul_left 6).add h2)
  have hdef : ((minusSixD2Coeff (thetaCount Gz g) x : ℚ) : ℂ) =
      -6 * ((x * thetaCount Gz g x : ℚ) : ℂ) + ((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ) := by
    rw [minusSixD2Coeff, e2ThetaCoeff]
    push_cast
    ring
  rw [hdef]
  have hn : ‖-6 * ((x * thetaCount Gz g x : ℚ) : ℂ) + ((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ)‖ ≤
      6 * ‖((x * thetaCount Gz g x : ℚ) : ℂ)‖ + ‖((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ)‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    norm_num
  have hE := (Real.exp_pos (-2 * π * (x : ℝ) * y)).le
  calc ‖-6 * ((x * thetaCount Gz g x : ℚ) : ℂ) + ((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ)‖ *
        Real.exp (-2 * π * (x : ℝ) * y)
      ≤ (6 * ‖((x * thetaCount Gz g x : ℚ) : ℂ)‖ +
          ‖((e2ThetaCoeff (thetaCount Gz g) x : ℚ) : ℂ)‖) * Real.exp (-2 * π * (x : ℝ) * y) :=
        mul_le_mul_of_nonneg_right hn hE
    _ = _ := by ring

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.cauchy_term
#print axioms HaagerupIzumi.C8.Theta.summable_norm_e2ThetaCoeff
#print axioms HaagerupIzumi.C8.Theta.summable_norm_minusSixD2Coeff
