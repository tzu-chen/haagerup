module

public import HaagerupIzumi.C8.Theta.QExpansion

@[expose] public section

/-!
# Support of the coset theta series and the table labels

W6 plan item 0 (`Theta/W6_PLAN.md`, additions after compiling the drafts), for the proof of
Proposition `prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).

* **Support.**  For an even integral `G` and `γ = G⁻¹ s ∈ L'`, every vector of `γ + L` has
  energy in `q(γ) + ℤ` (`qf_add_intVec_eq`, the computation behind `cexp_qf_add_one`;
  `energy_cosetPt_eq_add_int` in the ℚ coordinates of `Theta/Basic`).  Hence the coefficients
  `thetaCoeff G g H e` vanish unless `e ∈ q(γ) + ℤ` and `e ≥ 0` (`thetaCoeff_support`,
  `nonneg_of_thetaCoeff_ne_zero`), i.e. they are supported on `λ + ℕ` for every `λ ≤ 0` with
  `λ ≡ q(γ)` (`thetaCoeff_support_nat`), the form required by `qcoeff_eq_of_tsum_eq`.
* **Table labels.**  The tables (`Theta/M3First` … `M6Reverse`) use integer labels, e.g.
  `cosetL7A2 3 0` or `cosetG7m 2 1 = repG7m 25`.  Via the `*_emod` lemmas of `LatticeData`,
  the theta series at an integer label is the component of the theta vector at the reduced
  label (`latticeThetaQ_cosetL7A2`, …), and its `q`-expansion has the table coefficients
  `thetaCoeff G (label) (quadOf M) e` (`thetaQL7A2_mod_eq_tsum`, …).  Every integer label is
  `G⁻¹` of an explicit integral vector (`ratVec_cosetL7A2_eq_inv`, …), which is the hypothesis
  of the support lemmas.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex Matrix

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Energies of a coset lie in `q(γ) + ℤ` -/

section Support

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `Q_G(γ + m) ∈ Q_G(γ) + 2ℤ` for even integral `G`, `γ = G⁻¹ s ∈ L'`, `m ∈ ℤ^d`. -/
theorem qf_add_intVec_eq {Gz : Matrix d d ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : d → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) (s m : d → ℤ) :
    ∃ k : ℤ, qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s + intVec m) =
      qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) + 2 * (k : ℝ) := by
  set G := gramR Gz with hGdef
  set γ := G⁻¹ *ᵥ intVec s with hγ
  have hunit := isUnit_det_of_posDef hG
  have hGt := transpose_eq_of_posDef hG
  have hGγ : G *ᵥ γ = intVec s := by
    rw [hγ, mulVec_mulVec, mul_nonsing_inv G hunit, one_mulVec]
  obtain ⟨k, hk⟩ := hEven m
  have hqm : qf G (intVec m) = ((m ⬝ᵥ (Gz *ᵥ m) : ℤ) : ℝ) := by
    rw [qf, hGdef, ← intVec_mulVec, intVec_dotProduct]
  refine ⟨m ⬝ᵥ s + k, ?_⟩
  rw [qf_add hGt, hGγ, intVec_dotProduct, hqm, hk]
  push_cast
  ring

end Support

/-- **Energies of `γ + L` lie in `q(γ) + ℤ`** (ℚ coordinates): for `γ = G⁻¹ s`. -/
theorem energy_cosetPt_eq_add_int {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) (n : Fin 4 → ℤ) :
    ∃ k : ℤ, energy Gz (cosetPt g n) = energy Gz g + k := by
  obtain ⟨k, hk⟩ := qf_add_intVec_eq hG hEven s n
  refine ⟨k, ?_⟩
  have h1 := qf_gramR_ratVec_eq_energy Gz (cosetPt g n)
  have h2 := qf_gramR_ratVec_eq_energy Gz g
  rw [ratVec_cosetPt, hg, hk] at h1
  rw [hg] at h2
  have h3 : ((energy Gz (cosetPt g n) : ℚ) : ℝ) = ((energy Gz g + k : ℚ) : ℝ) := by
    push_cast
    linarith
  exact Rat.cast_injective h3

/-- Energies are nonnegative for a positive definite lattice. -/
theorem energy_nonneg {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (x : Fin 4 → ℚ) : 0 ≤ energy Gz x := by
  have h := qf_nonneg_of_posDef hG (ratVec x)
  rw [qf_gramR_ratVec_eq_energy] at h
  have h' : (0 : ℝ) ≤ ((energy Gz x : ℚ) : ℝ) := by linarith
  exact_mod_cast h'

theorem shell_nonempty_of_thetaCoeff_ne_zero {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    {g : Fin 4 → ℚ} {H : (Fin 4 → ℚ) → ℚ} {e : ℚ} (h : thetaCoeff Gz g H e ≠ 0) :
    (shell Gz g e).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  apply h
  rw [thetaCoeff, hne, finsum_mem_empty]

/-- A nonzero coefficient sits at a nonnegative exponent. -/
theorem nonneg_of_thetaCoeff_ne_zero {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    {g : Fin 4 → ℚ} {H : (Fin 4 → ℚ) → ℚ} {e : ℚ} (h : thetaCoeff Gz g H e ≠ 0) : 0 ≤ e := by
  obtain ⟨n, hn⟩ := shell_nonempty_of_thetaCoeff_ne_zero h
  rw [← (show energy Gz (cosetPt g n) = e from hn)]
  exact energy_nonneg hG _

/-- **Support lemma**: `thetaCoeff G g H e ≠ 0` forces `e ∈ q(γ) + ℤ`. -/
theorem thetaCoeff_support {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (h : thetaCoeff Gz g H e ≠ 0) : ∃ k : ℤ, e = energy Gz g + k := by
  obtain ⟨n, hn⟩ := shell_nonempty_of_thetaCoeff_ne_zero h
  obtain ⟨k, hk⟩ := energy_cosetPt_eq_add_int hG hEven hg n
  exact ⟨k, (show energy Gz (cosetPt g n) = e from hn).symm.trans hk⟩

/-- **Support lemma, `λ + ℕ` form**: for every `λ ≤ 0` with `λ ≡ q(γ) (mod 1)`, the
coefficients are supported on `λ + ℕ` (hypothesis `ha` of `qcoeff_eq_of_tsum_eq`). -/
theorem thetaCoeff_support_nat {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) (lam : ℚ) (hlam0 : lam ≤ 0)
    (hlam : ∃ k : ℤ, lam = energy Gz g + k) (H : (Fin 4 → ℚ) → ℚ) (e : ℚ)
    (h : thetaCoeff Gz g H e ≠ 0) : ∃ n : ℕ, e = (n : ℚ) + lam := by
  obtain ⟨k1, hk1⟩ := thetaCoeff_support hG hEven hg h
  obtain ⟨k2, hk2⟩ := hlam
  have he := nonneg_of_thetaCoeff_ne_zero hG h
  have hk : (0 : ℚ) ≤ ((k1 - k2 : ℤ) : ℚ) := by
    push_cast
    linarith
  have hk' : 0 ≤ k1 - k2 := by exact_mod_cast hk
  refine ⟨(k1 - k2).toNat, ?_⟩
  have hc : (((k1 - k2).toNat : ℕ) : ℚ) = ((k1 - k2 : ℤ) : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk']
  rw [hc]
  push_cast
  linarith

/-- The same, for the complex coefficients appearing in `latticeThetaQ_eq_tsum_thetaCoeff`. -/
theorem thetaCoeff_support_nat_complex {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    (hG : (gramR Gz).PosDef) (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m)))
    {g : Fin 4 → ℚ} {s : Fin 4 → ℤ} (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) (lam : ℚ)
    (hlam0 : lam ≤ 0) (hlam : ∃ k : ℤ, lam = energy Gz g + k) (H : (Fin 4 → ℚ) → ℚ) :
    ∀ e : ℚ, ((thetaCoeff Gz g H e : ℚ) : ℂ) ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam := by
  intro e he
  refine thetaCoeff_support_nat hG hEven hg lam hlam0 hlam H e fun h0 => he ?_
  rw [h0, Rat.cast_zero]

/-! ## Table labels: `L₇ ⊕ A₂` -/

/-- The integer label `(r, s)` is `G⁻¹ (0, r, s, 0)`. -/
theorem ratVec_cosetL7A2_eq_inv (r s : ℤ) :
    ratVec (cosetL7A2 r s) = (gramR gramL7A2)⁻¹ *ᵥ intVec ![0, r, s, 0] := by
  rw [inv_L7A2, intVec_eq_ratVec, map_ratCast_mulVec]
  congr 1
  funext i
  fin_cases i <;> simp [invL7A2, cosetL7A2, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The reduction of an integer label `(r, s)` to `ℤ/7 × ℤ/3`. -/
def modL7A2 (r s : ℤ) : Fin 7 × Fin 3 := (⟨(r % 7).toNat, by omega⟩, ⟨(s % 3).toNat, by omega⟩)

theorem modL7A2_val (r s : ℤ) :
    (((modL7A2 r s).1 : ℕ) : ℤ) = r % 7 ∧ (((modL7A2 r s).2 : ℕ) : ℤ) = s % 3 := by
  refine ⟨?_, ?_⟩ <;> simp only [modL7A2, Fin.val_mk] <;> omega

/-- The theta series at an integer label is the component at the reduced label. -/
theorem latticeThetaQ_cosetL7A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (r s : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramL7A2) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetL7A2 r s)) τ =
      thetaQL7A2 M (modL7A2 r s) τ := by
  rw [thetaQL7A2, (modL7A2_val r s).1, (modL7A2_val r s).2, ratVec_cosetL7A2_emod r s,
    latticeThetaQ_add_intVec]

theorem latticeTheta_cosetL7A2 (r s : ℤ) (τ : ℂ) :
    latticeTheta (gramR gramL7A2) (ratVec (cosetL7A2 r s)) τ = thetaL7A2 (modL7A2 r s) τ := by
  rw [thetaL7A2, (modL7A2_val r s).1, (modL7A2_val r s).2, ratVec_cosetL7A2_emod r s,
    latticeTheta_add_intVec]

/-- **Table 1 coefficients are the `q`-coefficients of the theta vector**: the component of
`Θ_{H}` (`H = quadOf M`, e.g. `H₁ = quadOf MH1`) at the reduced label of `(r, s)`. -/
theorem thetaQL7A2_mod_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) (r s : ℤ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    thetaQL7A2 M (modL7A2 r s) τ =
      ∑' e : ℚ, ((thetaCoeff gramL7A2 (cosetL7A2 r s) (quadOf M) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeThetaQ_cosetL7A2]
  exact latticeThetaQ_eq_tsum_thetaCoeff posDef_L7A2 M _ hτ

/-- Support of the Table 1 coefficients. -/
theorem thetaCoeff_L7A2_support (r s : ℤ) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (h : thetaCoeff gramL7A2 (cosetL7A2 r s) H e ≠ 0) :
    0 ≤ e ∧ ∃ k : ℤ, e = energy gramL7A2 (cosetL7A2 r s) + k :=
  ⟨nonneg_of_thetaCoeff_ne_zero posDef_L7A2 h,
    thetaCoeff_support posDef_L7A2 even_L7A2 (ratVec_cosetL7A2_eq_inv r s) h⟩

/-! ## Table labels: `G₇⁻` -/

/-- The integer label `t` (`t ℓ`) is `G⁻¹ (t, 0, 0, 0)`. -/
theorem ratVec_repG7m_eq_inv (t : ℤ) :
    ratVec (repG7m t) = (gramR gramG7m)⁻¹ *ᵥ intVec ![t, 0, 0, 0] := by
  rw [inv_G7m, intVec_eq_ratVec, map_ratCast_mulVec]
  congr 1
  funext i
  fin_cases i <;> simp [invG7m, repG7m, ellG7m, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

def modG7m (t : ℤ) : Fin 21 := ⟨(t % 21).toNat, by omega⟩

theorem modG7m_val (t : ℤ) : (((modG7m t) : ℕ) : ℤ) = t % 21 := by
  simp only [modG7m, Fin.val_mk]
  omega

theorem latticeThetaQ_repG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (t : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramG7m) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (repG7m t)) τ =
      thetaQG7m M (modG7m t) τ := by
  rw [thetaQG7m, modG7m_val, ratVec_repG7m_emod t, latticeThetaQ_add_intVec]

theorem latticeTheta_repG7m (t : ℤ) (τ : ℂ) :
    latticeTheta (gramR gramG7m) (ratVec (repG7m t)) τ = thetaG7m (modG7m t) τ := by
  rw [thetaG7m, modG7m_val, ratVec_repG7m_emod t, latticeTheta_add_intVec]

/-- **Table 2 labels**: the manuscript coset `(r, s)` is the component `9r + 7s mod 21`. -/
theorem latticeThetaQ_cosetG7m (M : Matrix (Fin 4) (Fin 4) ℚ) (r s : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramG7m) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetG7m r s)) τ =
      thetaQG7m M (modG7m (9 * r + 7 * s)) τ := by
  rw [cosetG7m_eq, latticeThetaQ_repG7m]

theorem thetaQG7m_mod_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) (r s : ℤ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    thetaQG7m M (modG7m (9 * r + 7 * s)) τ =
      ∑' e : ℚ, ((thetaCoeff gramG7m (cosetG7m r s) (quadOf M) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeThetaQ_cosetG7m]
  exact latticeThetaQ_eq_tsum_thetaCoeff posDef_G7m M _ hτ

theorem thetaG7m_mod_eq_tsum (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaG7m (modG7m (9 * r + 7 * s)) τ =
      ∑' e : ℚ, ((thetaCount gramG7m (cosetG7m r s) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeTheta_repG7m, ← cosetG7m_eq]
  exact latticeTheta_eq_tsum_thetaCount posDef_G7m _ hτ

theorem thetaCoeff_G7m_support (r s : ℤ) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (h : thetaCoeff gramG7m (cosetG7m r s) H e ≠ 0) :
    0 ≤ e ∧ ∃ k : ℤ, e = energy gramG7m (cosetG7m r s) + k :=
  ⟨nonneg_of_thetaCoeff_ne_zero posDef_G7m h,
    thetaCoeff_support posDef_G7m even_G7m (ratVec_repG7m_eq_inv (9 * r + 7 * s)) h⟩

/-! ## Table labels: `A₁ ⊕ A₁ ⊕ A₂` -/

theorem ratVec_cosetA1A1A2_eq_inv (a b s : ℤ) :
    ratVec (cosetA1A1A2 a b s) = (gramR gramA1A1A2)⁻¹ *ᵥ intVec ![a, b, s, 0] := by
  rw [inv_A1A1A2, intVec_eq_ratVec, map_ratCast_mulVec]
  congr 1
  funext i
  fin_cases i <;> simp [invA1A1A2, cosetA1A1A2, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

def modA1A1A2 (a b s : ℤ) : Fin 2 × Fin 2 × Fin 3 :=
  (⟨(a % 2).toNat, by omega⟩, ⟨(b % 2).toNat, by omega⟩, ⟨(s % 3).toNat, by omega⟩)

theorem modA1A1A2_val (a b s : ℤ) :
    (((modA1A1A2 a b s).1 : ℕ) : ℤ) = a % 2 ∧ (((modA1A1A2 a b s).2.1 : ℕ) : ℤ) = b % 2 ∧
      (((modA1A1A2 a b s).2.2 : ℕ) : ℤ) = s % 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [modA1A1A2, Fin.val_mk] <;> omega

theorem latticeThetaQ_cosetA1A1A2 (M : Matrix (Fin 4) (Fin 4) ℚ) (a b s : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramA1A1A2) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetA1A1A2 a b s)) τ =
      thetaQA1A1A2 M (modA1A1A2 a b s) τ := by
  obtain ⟨ha, hb, hs⟩ := modA1A1A2_val a b s
  rw [thetaQA1A1A2, ha, hb, hs, ratVec_cosetA1A1A2_emod a b s, latticeThetaQ_add_intVec]

theorem latticeTheta_cosetA1A1A2 (a b s : ℤ) (τ : ℂ) :
    latticeTheta (gramR gramA1A1A2) (ratVec (cosetA1A1A2 a b s)) τ =
      thetaA1A1A2 (modA1A1A2 a b s) τ := by
  obtain ⟨ha, hb, hs⟩ := modA1A1A2_val a b s
  rw [thetaA1A1A2, ha, hb, hs, ratVec_cosetA1A1A2_emod a b s, latticeTheta_add_intVec]

theorem thetaQA1A1A2_mod_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) (a b s : ℤ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    thetaQA1A1A2 M (modA1A1A2 a b s) τ =
      ∑' e : ℚ, ((thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) (quadOf M) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeThetaQ_cosetA1A1A2]
  exact latticeThetaQ_eq_tsum_thetaCoeff posDef_A1A1A2 M _ hτ

theorem thetaCoeff_A1A1A2_support (a b s : ℤ) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (h : thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) H e ≠ 0) :
    0 ≤ e ∧ ∃ k : ℤ, e = energy gramA1A1A2 (cosetA1A1A2 a b s) + k :=
  ⟨nonneg_of_thetaCoeff_ne_zero posDef_A1A1A2 h,
    thetaCoeff_support posDef_A1A1A2 even_A1A1A2 (ratVec_cosetA1A1A2_eq_inv a b s) h⟩

/-! ## Table labels: `G₆⁻` -/

/-- Integer labels of `G₆⁻` reduce modulo `(2, 2, 3)`. -/
theorem ratVec_cosetG6m_emod (a b t : ℤ) :
    ratVec (cosetG6m a b t) = ratVec (cosetG6m (a % 2) (b % 2) (t % 3)) +
      intVec ![2 * (t / 3), a / 2 + t / 3, b / 2 + t / 3, a / 2 + b / 2 - t / 3] := by
  have ha : (a : ℝ) = ((a % 2 : ℤ) : ℝ) + 2 * ((a / 2 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a 2).symm
  have hb : (b : ℝ) = ((b % 2 : ℤ) : ℝ) + 2 * ((b / 2 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b 2).symm
  have ht : (t : ℝ) = ((t % 3 : ℤ) : ℝ) + 3 * ((t / 3 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv t 3).symm
  funext i
  fin_cases i <;> simp [ratVec, intVec, cosetG6m] <;> linarith

theorem ratVec_cosetG6m_eq_inv (a b t : ℤ) :
    ratVec (cosetG6m a b t) =
      (gramR gramG6m)⁻¹ *ᵥ intVec ![-a - b + t, a, b, 2 * a + 2 * b - 2 * t] := by
  rw [inv_G6m, intVec_eq_ratVec, map_ratCast_mulVec]
  congr 1
  funext i
  fin_cases i <;> simp [invG6m, cosetG6m, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

def modG6m (a b t : ℤ) : Fin 2 × Fin 2 × Fin 3 :=
  (⟨(a % 2).toNat, by omega⟩, ⟨(b % 2).toNat, by omega⟩, ⟨(t % 3).toNat, by omega⟩)

theorem modG6m_val (a b t : ℤ) :
    (((modG6m a b t).1 : ℕ) : ℤ) = a % 2 ∧ (((modG6m a b t).2.1 : ℕ) : ℤ) = b % 2 ∧
      (((modG6m a b t).2.2 : ℕ) : ℤ) = t % 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [modG6m, Fin.val_mk] <;> omega

theorem latticeThetaQ_cosetG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (a b t : ℤ) (τ : ℂ) :
    latticeThetaQ (gramR gramG6m) (M.map (Rat.cast : ℚ → ℝ)) (ratVec (cosetG6m a b t)) τ =
      thetaQG6m M (modG6m a b t) τ := by
  obtain ⟨ha, hb, ht⟩ := modG6m_val a b t
  rw [thetaQG6m, ha, hb, ht, ratVec_cosetG6m_emod a b t, latticeThetaQ_add_intVec]

theorem latticeTheta_cosetG6m (a b t : ℤ) (τ : ℂ) :
    latticeTheta (gramR gramG6m) (ratVec (cosetG6m a b t)) τ = thetaG6m (modG6m a b t) τ := by
  obtain ⟨ha, hb, ht⟩ := modG6m_val a b t
  rw [thetaG6m, ha, hb, ht, ratVec_cosetG6m_emod a b t, latticeTheta_add_intVec]

/-- **Table 4 labels**: the vacuum coordinate is the label `(0,0,0)` and the polar coordinate
`-w/3 + L` is the label `(1,1,1)`. -/
theorem latticeThetaQ_polarG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℂ) :
    latticeThetaQ (gramR gramG6m) (M.map (Rat.cast : ℚ → ℝ)) (ratVec polarG6m) τ =
      thetaQG6m M (modG6m 1 1 1) τ := by
  rw [← latticeThetaQ_cosetG6m, ratVec_polarG6m, latticeThetaQ_add_intVec]

theorem latticeThetaQ_zeroG6m (M : Matrix (Fin 4) (Fin 4) ℚ) (τ : ℂ) :
    latticeThetaQ (gramR gramG6m) (M.map (Rat.cast : ℚ → ℝ)) (ratVec 0) τ =
      thetaQG6m M (modG6m 0 0 0) τ := by
  rw [← latticeThetaQ_cosetG6m, cosetG6m_zero]

theorem thetaQG6m_mod_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) (a b t : ℤ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    thetaQG6m M (modG6m a b t) τ =
      ∑' e : ℚ, ((thetaCoeff gramG6m (cosetG6m a b t) (quadOf M) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeThetaQ_cosetG6m]
  exact latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m M _ hτ

/-- The Table 4 coordinates `0` and `polarG6m` in `q`-expansion form. -/
theorem thetaQG6m_polar_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG6m M (modG6m 1 1 1) τ =
      ∑' e : ℚ, ((thetaCoeff gramG6m polarG6m (quadOf M) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeThetaQ_polarG6m]
  exact latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m M _ hτ

theorem thetaQG6m_zero_eq_tsum (M : Matrix (Fin 4) (Fin 4) ℚ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG6m M (modG6m 0 0 0) τ =
      ∑' e : ℚ, ((thetaCoeff gramG6m 0 (quadOf M) e : ℚ) : ℂ) *
        cexp (2 * π * I * (e : ℂ) * τ) := by
  rw [← latticeThetaQ_zeroG6m]
  exact latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m M _ hτ

theorem thetaCoeff_G6m_support (a b t : ℤ) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (h : thetaCoeff gramG6m (cosetG6m a b t) H e ≠ 0) :
    0 ≤ e ∧ ∃ k : ℤ, e = energy gramG6m (cosetG6m a b t) + k :=
  ⟨nonneg_of_thetaCoeff_ne_zero posDef_G6m h,
    thetaCoeff_support posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv a b t) h⟩

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.qf_add_intVec_eq
#print axioms HaagerupIzumi.C8.Theta.energy_cosetPt_eq_add_int
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_support
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_support_nat
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_support_nat_complex
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_cosetL7A2
#print axioms HaagerupIzumi.C8.Theta.thetaQL7A2_mod_eq_tsum
#print axioms HaagerupIzumi.C8.Theta.thetaQG7m_mod_eq_tsum
#print axioms HaagerupIzumi.C8.Theta.thetaQA1A1A2_mod_eq_tsum
#print axioms HaagerupIzumi.C8.Theta.thetaQG6m_mod_eq_tsum
#print axioms HaagerupIzumi.C8.Theta.thetaQG6m_polar_eq_tsum
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_G6m_support
