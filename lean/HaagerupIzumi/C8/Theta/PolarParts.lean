module

public import HaagerupIzumi.C8.Theta.EvenBlocks

@[expose] public section

/-!
# Polar parts and holomorphy of the weight-zero theta vectors

W6 plan item 3 (`Theta/W6_PLAN.md`), the theta side, for the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).

* **Full polar part** (audit item 4).  `Θ_{H,p}/η⁸` has a pole at `i∞` only through the
  coefficients `[q^e] Θ_{H,p}` with `e < 1/3`.  By the support lemma such an `e` equals the
  fractional part of `q(γ_p)` (`thetaCoeff_polar`, any `e < c ≤ 1`).  The labels with
  `frac q(γ_p) < 1/3` are found by a kernel-checked computation (`polarExp_*_table`), giving
  the complete list of polar entries (`polar_*`):
  - `L₇ ⊕ A₂`: `(0,0)` at `q⁰`, `(±1,0)` at `q^{1/7}`, `(±3,0)` at `q^{2/7}`;
  - `G₇⁻`: `j = 0` at `q⁰`, `j ∈ {4, 10, 11, 17}` (the orbit of `(2,1)`) at `q^{2/21}`;
  - `A₁ ⊕ A₁ ⊕ A₂`: `(0,0,0)` at `q⁰`, `(1,0,0)`, `(0,1,0)` at `q^{1/4}`;
  - `G₆⁻`: `(0,0,0)` at `q⁰`, `(1,1,±1)` (the polar coset `-w/3`) at `q^{1/6}`.
  These are exactly the polar rows of Tables 1–4 together with the vacuum `q⁰` entry (whose
  `Θ_H`-coefficient vanishes, `thetaCoeff_at_zero`).
* **Holomorphy** on `ℍ` of the weight-zero vectors (hypothesis `hF` of `pole_cancellation`):
  `mdifferentiable_div_eta8`, `mdifferentiable_F*`, `mdifferentiable_FE*`.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Manifold UpperHalfPlane

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Polar exponents -/

/-- A nonzero coefficient at an exponent `e < c ≤ 1` sits at `e = frac q(γ)`. -/
theorem thetaCoeff_polar {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) {H : (Fin 4 → ℚ) → ℚ} {e c : ℚ} (hc : c ≤ 1)
    (he : e < c) (h : thetaCoeff Gz g H e ≠ 0) : e = Int.fract (energy Gz g) := by
  obtain ⟨k, hk⟩ := thetaCoeff_support hG hEven hg h
  have he0 := nonneg_of_thetaCoeff_ne_zero hG h
  have hf0 := Int.fract_nonneg (energy Gz g)
  have hf1 := Int.fract_lt_one (energy Gz g)
  have hm : e - Int.fract (energy Gz g) = ((k + ⌊energy Gz g⌋ : ℤ) : ℚ) := by
    rw [hk, ← Int.self_sub_floor]
    push_cast
    ring
  have h1 : ((k + ⌊energy Gz g⌋ : ℤ) : ℚ) < 1 := by rw [← hm]; linarith
  have h2 : (-1 : ℚ) < ((k + ⌊energy Gz g⌋ : ℤ) : ℚ) := by rw [← hm]; linarith
  have h1' : k + ⌊energy Gz g⌋ < 1 := by exact_mod_cast h1
  have h2' : -1 < k + ⌊energy Gz g⌋ := by exact_mod_cast h2
  have h0 : k + ⌊energy Gz g⌋ = 0 := by omega
  rw [h0, Int.cast_zero] at hm
  linarith

/-! ### `L₇ ⊕ A₂` -/

def polarExpL7A2 (p : Fin 7 × Fin 3) : ℚ :=
  Int.fract (energy gramL7A2 (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ)))

/-- The labels with `frac q(γ_p) < 1/3` (kernel-checked). -/
theorem polarExp_L7A2_table : ∀ p : Fin 7 × Fin 3, polarExpL7A2 p < 1 / 3 →
    (p = (0, 0) ∧ polarExpL7A2 p = 0) ∨ ((p = (1, 0) ∨ p = (6, 0)) ∧ polarExpL7A2 p = 1 / 7) ∨
      ((p = (3, 0) ∨ p = (4, 0)) ∧ polarExpL7A2 p = 2 / 7) := by
  decide +kernel

/-- **All polar entries, `L₇ ⊕ A₂`**: a nonzero `[q^e] Θ_{H,p}` with `e < 1/3` is one of the
vacuum entry `(0,0), q⁰` and the Table 1 polar rows `(±1,0), q^{1/7}`, `(±3,0), q^{2/7}`. -/
theorem polar_L7A2 (p : Fin 7 × Fin 3) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ} (he : e < 1 / 3)
    (h : thetaCoeff gramL7A2 (cosetL7A2 ((p.1 : ℕ) : ℤ) ((p.2 : ℕ) : ℤ)) H e ≠ 0) :
    (p = (0, 0) ∧ e = 0) ∨ ((p = (1, 0) ∨ p = (6, 0)) ∧ e = 1 / 7) ∨
      ((p = (3, 0) ∨ p = (4, 0)) ∧ e = 2 / 7) := by
  have he' : e = polarExpL7A2 p :=
    thetaCoeff_polar posDef_L7A2 even_L7A2 (ratVec_cosetL7A2_eq_inv _ _) (by norm_num) he h
  rw [he'] at he ⊢
  exact polarExp_L7A2_table p he

/-! ### `G₇⁻` -/

def polarExpG7m (j : Fin 21) : ℚ := Int.fract (energy gramG7m (repG7m ((j : ℕ) : ℤ)))

theorem polarExp_G7m_table : ∀ j : Fin 21, polarExpG7m j < 1 / 3 →
    (j = 0 ∧ polarExpG7m j = 0) ∨
      ((j = 4 ∨ j = 10 ∨ j = 11 ∨ j = 17) ∧ polarExpG7m j = 2 / 21) := by
  decide +kernel

/-- **All polar entries, `G₇⁻`**: `j = 0` at `q⁰` and the orbit `{4, 10, 11, 17}` of the
manuscript coset `(2,1)` (`9·2 + 7 = 25 ≡ 4`) at `q^{2/21}`. -/
theorem polar_G7m (j : Fin 21) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ} (he : e < 1 / 3)
    (h : thetaCoeff gramG7m (repG7m ((j : ℕ) : ℤ)) H e ≠ 0) :
    (j = 0 ∧ e = 0) ∨ ((j = 4 ∨ j = 10 ∨ j = 11 ∨ j = 17) ∧ e = 2 / 21) := by
  have he' : e = polarExpG7m j :=
    thetaCoeff_polar posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) (by norm_num) he h
  rw [he'] at he ⊢
  exact polarExp_G7m_table j he

/-! ### `A₁ ⊕ A₁ ⊕ A₂` -/

def polarExpA1A1A2 (p : Fin 2 × Fin 2 × Fin 3) : ℚ :=
  Int.fract (energy gramA1A1A2 (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)))

theorem polarExp_A1A1A2_table : ∀ p : Fin 2 × Fin 2 × Fin 3, polarExpA1A1A2 p < 1 / 3 →
    (p = (0, 0, 0) ∧ polarExpA1A1A2 p = 0) ∨
      ((p = (1, 0, 0) ∨ p = (0, 1, 0)) ∧ polarExpA1A1A2 p = 1 / 4) := by
  decide +kernel

/-- **All polar entries, `A₁ ⊕ A₁ ⊕ A₂`**: `(0,0,0)` at `q⁰` and the quarter-twist cosets
`(1,0,0)`, `(0,1,0)` at `q^{1/4}`. -/
theorem polar_A1A1A2 (p : Fin 2 × Fin 2 × Fin 3) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (he : e < 1 / 3)
    (h : thetaCoeff gramA1A1A2
      (cosetA1A1A2 ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) H e ≠ 0) :
    (p = (0, 0, 0) ∧ e = 0) ∨ ((p = (1, 0, 0) ∨ p = (0, 1, 0)) ∧ e = 1 / 4) := by
  have he' : e = polarExpA1A1A2 p :=
    thetaCoeff_polar posDef_A1A1A2 even_A1A1A2 (ratVec_cosetA1A1A2_eq_inv _ _ _) (by norm_num)
      he h
  rw [he'] at he ⊢
  exact polarExp_A1A1A2_table p he

/-! ### `G₆⁻` -/

def polarExpG6m (p : Fin 2 × Fin 2 × Fin 3) : ℚ :=
  Int.fract (energy gramG6m (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)))

theorem polarExp_G6m_table : ∀ p : Fin 2 × Fin 2 × Fin 3, polarExpG6m p < 1 / 3 →
    (p = (0, 0, 0) ∧ polarExpG6m p = 0) ∨
      ((p = (1, 1, 1) ∨ p = (1, 1, 2)) ∧ polarExpG6m p = 1 / 6) := by
  decide +kernel

/-- **All polar entries, `G₆⁻`**: `(0,0,0)` at `q⁰` and the polar coset `±(-w/3)`, labels
`(1,1,±1)`, at `q^{1/6}`. -/
theorem polar_G6m (p : Fin 2 × Fin 2 × Fin 3) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ} (he : e < 1 / 3)
    (h : thetaCoeff gramG6m
      (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) H e ≠ 0) :
    (p = (0, 0, 0) ∧ e = 0) ∨ ((p = (1, 1, 1) ∨ p = (1, 1, 2)) ∧ e = 1 / 6) := by
  have he' : e = polarExpG6m p :=
    thetaCoeff_polar posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) (by norm_num) he h
  rw [he'] at he ⊢
  exact polarExp_G6m_table p he

/-! ## Holomorphy of the weight-zero vectors -/

/-- `f/η⁸` is holomorphic on `ℍ` for `f` holomorphic on `{Im τ > 0}`. -/
theorem mdifferentiable_div_eta8 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {τ : ℂ | 0 < τ.im}) :
    MDiff (fun τ : ℍ => f τ / eta8 τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (hf.div differentiableOn_eta8 fun z hz => eta8_ne_zero hz).congr fun z hz => ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem mdifferentiable_FL7A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 7 × Fin 3) :
    MDiff (fun τ : ℍ => FL7A2 M τ p) :=
  mdifferentiable_div_eta8 (f := thetaQL7A2 M p) (differentiableOn_latticeThetaQ posDef_L7A2 _ _)

theorem mdifferentiable_FG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (j : Fin 21) :
    MDiff (fun τ : ℍ => FG7m M τ j) :=
  mdifferentiable_div_eta8 (f := thetaQG7m M j) (differentiableOn_latticeThetaQ posDef_G7m _ _)

theorem mdifferentiable_FA1A1A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) :
    MDiff (fun τ : ℍ => FA1A1A2 M τ p) :=
  mdifferentiable_div_eta8 (f := thetaQA1A1A2 M p)
    (differentiableOn_latticeThetaQ posDef_A1A1A2 _ _)

theorem mdifferentiable_FG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 2 × Fin 2 × Fin 3) :
    MDiff (fun τ : ℍ => FG6m M τ p) :=
  mdifferentiable_div_eta8 (f := thetaQG6m M p) (differentiableOn_latticeThetaQ posDef_G6m _ _)

theorem mdifferentiable_FEL7A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 × Fin 2) :
    MDiff (fun τ : ℍ => FEL7A2 M τ e) :=
  mdifferentiable_FL7A2 M (ιL7A2 e)

theorem mdifferentiable_FEA1A1A2 (e : Fin 3 × Fin 2) : MDiff (fun τ : ℍ => FEA1A1A2 τ e) :=
  mdifferentiable_FA1A1A2 MHA1A1A2 (ιA1A1A2 e)

theorem mdifferentiable_FEG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 2 × Fin 2 × Fin 2) :
    MDiff (fun τ : ℍ => FEG6m M τ e) :=
  mdifferentiable_FG6m M (ιG6m e)

theorem mdifferentiable_FEG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 × Fin 2) :
    MDiff (fun τ : ℍ => FEG7m M τ e) := by
  have h : (fun τ : ℍ => FEG7m M τ e) = fun τ : ℍ =>
      (fun z : ℂ => (1 / 2 : ℂ) * (thetaQG7m M (ιG7m e) z + thetaQG7m M (oG7m (ιG7m e)) z))
        τ / eta8 τ := by
    funext τ
    simp only [FEG7m, FaG7m, FG7m, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [h]
  exact mdifferentiable_div_eta8 (((differentiableOn_latticeThetaQ posDef_G7m _ _).add
    (differentiableOn_latticeThetaQ posDef_G7m _ _)).const_mul _)

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_polar
#print axioms HaagerupIzumi.C8.Theta.polar_L7A2
#print axioms HaagerupIzumi.C8.Theta.polar_G7m
#print axioms HaagerupIzumi.C8.Theta.polar_A1A1A2
#print axioms HaagerupIzumi.C8.Theta.polar_G6m
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_div_eta8
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_FEL7A2
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_FEG7m
