module

public import HaagerupIzumi.C8.Theta.EvenBlockData

@[expose] public section

/-!
# The even `S`-block of `G₇⁻` in cosine form

W6 plan item 2, optional part (`Theta/W6_PLAN.md`).  For Table 2 (lines 3682–3712 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) the even block uses the labels
`(r, s) ↦ 9r + 7s mod 21` and the orbits under `j ↦ ±j, ±13j`.  The reduced `S`-matrix
`SθEG7m` (hypothesis `hσS` of `FEG7m_covariant`, `m3_reverse_dimension_of_voa`,
`m3_reverse_obstruction_of_voa`) has the same cosine form as for `L₇ ⊕ A₂`:

`SθEG7m (r,s) (r',s') = -(1/√21) · C₇(r, r') · C₃(s, s')` (`SθEG7m_eq`), hence
**`SθEG7m = SθEL7A2`** (`SθEG7m_eq_SθEL7A2`).

This reflects that `G₇⁻` realizes the negative discriminant form: `e(-(γ,δ))` becomes
`e(+(2rr'/7 + 2ss'/3))`, and the orbit sums are real.  The orbits are parametrized by
`crtG7m (r, s) = 12r + 14s = -(9r + 7s) mod 21`; orbit lists and the congruence
`16 j k ≡ 6 r r' + 14 s s' (mod 21)` are kernel-checked.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-- `(r, s) ↦ -(9r + 7s) = 12r + 14s mod 21`. -/
def crtG7m (x : Fin 7 × Fin 3) : Fin 21 :=
  ⟨(12 * x.1.val + 14 * x.2.val) % 21, Nat.mod_lt _ (by norm_num)⟩

theorem crtG7m_injective : Function.Injective crtG7m := by
  decide +kernel

/-- The orbit of the even-block label `(r', s')` (kernel-checked). -/
theorem filter_πG7m_image : ∀ e' : Fin 4 × Fin 2,
    (Finset.univ.filter fun q : Fin 21 => πG7m q = e') = (R7 e'.1 ×ˢ R3 e'.2).image crtG7m := by
  decide +kernel

/-- `16 j k ≡ 6 r r'' + 14 s s'' (mod 21)` for `j = ιG7m (r, s)`, `k = crtG7m (r'', s'')`. -/
theorem sG7m_crt_data : ∀ (e : Fin 4 × Fin 2) (x : Fin 7 × Fin 3),
    (21 : ℤ) ∣ 16 * (((ιG7m e : Fin 21) : ℕ) : ℤ) * (((crtG7m x : Fin 21) : ℕ) : ℤ) -
      6 * ((e.1 : ℕ) : ℤ) * ((x.1 : ℕ) : ℤ) - 14 * ((e.2 : ℕ) : ℤ) * ((x.2 : ℕ) : ℤ) := by
  decide +kernel

theorem eChar_sG7m_crt (e : Fin 4 × Fin 2) (a : Fin 7) (b : Fin 3) :
    eChar (-sG7m (ιG7m e) (crtG7m (a, b))) =
      eChar (-(2 * ((e.1 : ℕ) : ℝ) * ((a : ℕ) : ℝ) / 7)) *
        eChar (-(2 * ((e.2 : ℕ) : ℝ) * ((b : ℕ) : ℝ) / 3)) := by
  obtain ⟨c, hc⟩ := sG7m_crt_data e (a, b)
  rw [← eChar_add]
  refine eChar_eq_of_sub_eq_int (-c) ?_
  have hc' : 16 * (((ιG7m e : Fin 21) : ℕ) : ℝ) * (((crtG7m (a, b) : Fin 21) : ℕ) : ℝ) -
      6 * ((e.1 : ℕ) : ℝ) * ((a : ℕ) : ℝ) - 14 * ((e.2 : ℕ) : ℝ) * ((b : ℕ) : ℝ) =
        21 * (c : ℝ) := by
    exact_mod_cast hc
  simp only [sG7m]
  push_cast
  linarith

/-- **The even `S`-block of `G₇⁻`**: `SθE_{(r,s),(r',s')} = -(1/√21) C₇(r, r') C₃(s, s')`. -/
theorem SθEG7m_eq (e e' : Fin 4 × Fin 2) :
    SθEG7m e e' =
      -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * (((c7 e.1 e'.1 : ℝ) : ℂ) * ((c3 e.2 e'.2 : ℝ) : ℂ)) := by
  show (∑ q ∈ Finset.univ.filter fun q => πG7m q = e', SθG7m (ιG7m e) q) = _
  rw [filter_πG7m_image e', Finset.sum_image (fun x _ y _ h => crtG7m_injective h),
    Finset.sum_product, ← sum_R7 e.1 e'.1, ← sum_R3 e.2 e'.2, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [SθG7m, Matrix.of_apply]
  rw [eChar_sG7m_crt e a b]

/-- The even `S`-blocks of `G₇⁻` and `L₇ ⊕ A₂` coincide. -/
theorem SθEG7m_eq_SθEL7A2 : SθEG7m = SθEL7A2 := by
  ext e e'
  rw [SθEG7m_eq, SθEL7A2_eq]

/-- The `T`-block of `G₇⁻`: `e(8 j²/21 - 1/3)` at `j = 9r + 7s`, i.e. `e(6r²/7 + 2s²/3 - 1/3)`
(kernel-checked congruence). -/
theorem eG7m_ι_data : ∀ e : Fin 4 × Fin 2,
    (21 : ℤ) ∣ 8 * (((ιG7m e : Fin 21) : ℕ) : ℤ) ^ 2 - 18 * ((e.1 : ℕ) : ℤ) ^ 2 -
      14 * ((e.2 : ℕ) : ℤ) ^ 2 := by
  decide +kernel

theorem TθEG7m_eq (e : Fin 4 × Fin 2) :
    TθEG7m e e = eChar (6 * ((e.1 : ℕ) : ℝ) ^ 2 / 7 + 2 * ((e.2 : ℕ) : ℝ) ^ 2 / 3 - 1 / 3) := by
  simp only [TθEG7m, Matrix.diagonal_apply_eq]
  obtain ⟨c, hc⟩ := eG7m_ι_data e
  refine eChar_eq_of_sub_eq_int c ?_
  have hc' : 8 * (((ιG7m e : Fin 21) : ℕ) : ℝ) ^ 2 - 18 * ((e.1 : ℕ) : ℝ) ^ 2 -
      14 * ((e.2 : ℕ) : ℝ) ^ 2 = 21 * (c : ℝ) := by
    exact_mod_cast hc
  simp only [eG7m]
  linarith

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.SθEG7m_eq
#print axioms HaagerupIzumi.C8.Theta.SθEG7m_eq_SθEL7A2
#print axioms HaagerupIzumi.C8.Theta.TθEG7m_eq
