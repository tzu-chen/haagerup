module

public import HaagerupIzumi.C8.Theta.EvenBlockData

@[expose] public section

/-!
# The even `S`-blocks of `A₁ ⊕ A₁ ⊕ A₂` and `G₆⁻` in closed form

W6 plan item 2, optional part (`Theta/W6_PLAN.md`), for Tables 3 and 4 of the proof of
Proposition `prop:near-group-current-obstructions` (lines 3714–3777 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  The reduced `S`-matrices of
`Theta/EvenBlocks` (hypotheses `hσS` of the `m = 6` capstones) are:

* `SθEA1A1A2 (ab, s) (ab', s') = -(1/√12) · C₂₂(ab, ab') · C₃(s, s')` (`SθEA1A1A2_eq`), with
  the `A₁ ⊕ A₁` orbit block `C₂₂ = [[1, 2, 1], [1, 0, -1], [1, -2, 1]]` in the order
  `ab ∈ {00, 10, 11}` and `C₃` as for `L₇ ⊕ A₂` (`C₃(s, 1) = 2cos(4πs/3)`);
* `SθEG6m (a, b, t) (a', b', t') = -(1/√12) · (-1)^{aa' + bb'} · C₃(t, t')` (`SθEG6m_eq`).

The orbits and the congruences of the exponents are kernel-checked; `e(-n/2) = (-1)ⁿ`
(`eChar_neg_half_nat`).

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-- `e(-n/2) = (-1)ⁿ`. -/
theorem eChar_neg_half_nat (n : ℕ) : eChar (-((n : ℝ) / 2)) = (-1 : ℂ) ^ n := by
  rw [eChar]
  have h : ((2 * π * -((n : ℝ) / 2) : ℝ) : ℂ) * I = (n : ℂ) * (-(π * I)) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

/-! ## `A₁ ⊕ A₁ ⊕ A₂` -/

/-- The `A₁ ⊕ A₁` part of the orbits: `00 ↦ {00}`, `10 ↦ {10, 01}`, `11 ↦ {11}`. -/
def O2 : Fin 3 → Finset (Fin 2 × Fin 2) := ![{(0, 0)}, {(1, 0), (0, 1)}, {(1, 1)}]

theorem filter_πA1A1A2_image : ∀ e' : Fin 3 × Fin 2,
    (Finset.univ.filter fun q : Fin 2 × Fin 2 × Fin 3 => πA1A1A2 q = e') =
      (O2 e'.1 ×ˢ R3 e'.2).image (fun y : (Fin 2 × Fin 2) × Fin 3 => (y.1.1, y.1.2, y.2)) := by
  decide +kernel

/-- The `A₁ ⊕ A₁` orbit block. -/
def c22 : Fin 3 → Fin 3 → ℤ := ![![1, 2, 1], ![1, 0, -1], ![1, -2, 1]]

theorem sum_O2_int : ∀ (e : Fin 3 × Fin 2) (ab' : Fin 3),
    ∑ u ∈ O2 ab', (-1 : ℤ) ^ (((ιA1A1A2 e).1 : ℕ) * (u.1 : ℕ) + ((ιA1A1A2 e).2.1 : ℕ) * (u.2 : ℕ)) =
      c22 e.1 ab' := by
  decide +kernel

theorem sum_O2 (e : Fin 3 × Fin 2) (ab' : Fin 3) :
    ∑ u ∈ O2 ab', (-1 : ℂ) ^ (((ιA1A1A2 e).1 : ℕ) * (u.1 : ℕ) + ((ιA1A1A2 e).2.1 : ℕ) * (u.2 : ℕ)) =
      ((c22 e.1 ab' : ℤ) : ℂ) := by
  have h := congrArg (Int.cast : ℤ → ℂ) (sum_O2_int e ab')
  push_cast at h
  exact h

theorem eChar_sA1A1A2_ι (e : Fin 3 × Fin 2) (u : Fin 2 × Fin 2) (x : Fin 3) :
    eChar (-sA1A1A2 (ιA1A1A2 e) (u.1, u.2, x)) =
      (-1 : ℂ) ^ (((ιA1A1A2 e).1 : ℕ) * (u.1 : ℕ) + ((ιA1A1A2 e).2.1 : ℕ) * (u.2 : ℕ)) *
        eChar (-(2 * ((e.2 : ℕ) : ℝ) * ((x : ℕ) : ℝ) / 3)) := by
  have hval : (((ιA1A1A2 e).2.2 : Fin 3) : ℕ) = (e.2 : ℕ) := rfl
  have h : sA1A1A2 (ιA1A1A2 e) (u.1, u.2, x) =
      ((((ιA1A1A2 e).1 : ℕ) * (u.1 : ℕ) + ((ιA1A1A2 e).2.1 : ℕ) * (u.2 : ℕ) : ℕ) : ℝ) / 2 +
        2 * ((e.2 : ℕ) : ℝ) * ((x : ℕ) : ℝ) / 3 := by
    simp only [sA1A1A2, hval]
    push_cast
    ring
  rw [h, neg_add, eChar_add, eChar_neg_half_nat]

/-- **The even `S`-block of `A₁ ⊕ A₁ ⊕ A₂`**: `-(1/√12) C₂₂(ab, ab') C₃(s, s')`. -/
theorem SθEA1A1A2_eq (e e' : Fin 3 × Fin 2) :
    SθEA1A1A2 e e' =
      -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * (((c22 e.1 e'.1 : ℤ) : ℂ) * ((c3 e.2 e'.2 : ℝ) : ℂ)) := by
  show (∑ q ∈ Finset.univ.filter fun q => πA1A1A2 q = e', SθA1A1A2 (ιA1A1A2 e) q) = _
  rw [filter_πA1A1A2_image e', Finset.sum_image (fun x _ y _ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2),
    Finset.sum_product, ← sum_R3 e.2 e'.2, ← sum_O2 e e'.1, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [SθA1A1A2, Matrix.of_apply]
  rw [eChar_sA1A1A2_ι e u x]

/-! ## `G₆⁻` -/

theorem filter_πG6m_image : ∀ e' : Fin 2 × Fin 2 × Fin 2,
    (Finset.univ.filter fun q : Fin 2 × Fin 2 × Fin 3 => πG6m q = e') =
      (R3 e'.2.2).image (fun x : Fin 3 => (e'.1, e'.2.1, -x)) := by
  decide +kernel

/-- `6 s(γ, δ) ≡ 3(aa' + bb') + 4tx (mod 6)` at `δ = (a', b', -x)` (kernel-checked). -/
theorem sG6m_ι_data : ∀ (e : Fin 2 × Fin 2 × Fin 2) (a' b' : Fin 2) (x : Fin 3),
    (6 : ℤ) ∣ (9 * ((e.1 : ℕ) : ℤ) * ((a' : ℕ) : ℤ) + 9 * ((e.2.1 : ℕ) : ℤ) * ((b' : ℕ) : ℤ) +
      8 * ((e.2.2 : ℕ) : ℤ) * (((-x : Fin 3) : ℕ) : ℤ) +
      6 * (((e.1 : ℕ) : ℤ) * ((b' : ℕ) : ℤ) + ((e.2.1 : ℕ) : ℤ) * ((a' : ℕ) : ℤ)) -
      6 * (((e.1 : ℕ) : ℤ) * (((-x : Fin 3) : ℕ) : ℤ) + ((e.2.2 : ℕ) : ℤ) * ((a' : ℕ) : ℤ)) -
      6 * (((e.2.1 : ℕ) : ℤ) * (((-x : Fin 3) : ℕ) : ℤ) + ((e.2.2 : ℕ) : ℤ) * ((b' : ℕ) : ℤ))) -
      3 * (((e.1 : ℕ) : ℤ) * ((a' : ℕ) : ℤ) + ((e.2.1 : ℕ) : ℤ) * ((b' : ℕ) : ℤ)) -
      4 * ((e.2.2 : ℕ) : ℤ) * ((x : ℕ) : ℤ) := by
  decide +kernel

theorem eChar_sG6m_ι (e : Fin 2 × Fin 2 × Fin 2) (a' b' : Fin 2) (x : Fin 3) :
    eChar (-sG6m (ιG6m e) (a', b', -x)) =
      (-1 : ℂ) ^ ((e.1 : ℕ) * (a' : ℕ) + (e.2.1 : ℕ) * (b' : ℕ)) *
        eChar (-(2 * ((e.2.2 : ℕ) : ℝ) * ((x : ℕ) : ℝ) / 3)) := by
  obtain ⟨c, hc⟩ := sG6m_ι_data e a' b' x
  have hc' : (9 * ((e.1 : ℕ) : ℝ) * ((a' : ℕ) : ℝ) + 9 * ((e.2.1 : ℕ) : ℝ) * ((b' : ℕ) : ℝ) +
      8 * ((e.2.2 : ℕ) : ℝ) * (((-x : Fin 3) : ℕ) : ℝ) +
      6 * (((e.1 : ℕ) : ℝ) * ((b' : ℕ) : ℝ) + ((e.2.1 : ℕ) : ℝ) * ((a' : ℕ) : ℝ)) -
      6 * (((e.1 : ℕ) : ℝ) * (((-x : Fin 3) : ℕ) : ℝ) + ((e.2.2 : ℕ) : ℝ) * ((a' : ℕ) : ℝ)) -
      6 * (((e.2.1 : ℕ) : ℝ) * (((-x : Fin 3) : ℕ) : ℝ) + ((e.2.2 : ℕ) : ℝ) * ((b' : ℕ) : ℝ))) -
      3 * (((e.1 : ℕ) : ℝ) * ((a' : ℕ) : ℝ) + ((e.2.1 : ℕ) : ℝ) * ((b' : ℕ) : ℝ)) -
      4 * ((e.2.2 : ℕ) : ℝ) * ((x : ℕ) : ℝ) = 6 * (c : ℝ) := by
    exact_mod_cast hc
  have hval : (((ιG6m e).2.2 : Fin 3) : ℕ) = (e.2.2 : ℕ) := rfl
  have h1 : (ιG6m e).1 = e.1 := rfl
  have h2 : (ιG6m e).2.1 = e.2.1 := rfl
  rw [← eChar_neg_half_nat, ← eChar_add]
  refine eChar_eq_of_sub_eq_int (-c) ?_
  simp only [sG6m, hval, h1, h2]
  push_cast
  linear_combination (-1 / 6 : ℝ) * hc'

/-- **The even `S`-block of `G₆⁻`**: `-(1/√12) (-1)^{aa' + bb'} C₃(t, t')`. -/
theorem SθEG6m_eq (e e' : Fin 2 × Fin 2 × Fin 2) :
    SθEG6m e e' = -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) *
      ((-1 : ℂ) ^ ((e.1 : ℕ) * (e'.1 : ℕ) + (e.2.1 : ℕ) * (e'.2.1 : ℕ)) *
        ((c3 e.2.2 e'.2.2 : ℝ) : ℂ)) := by
  show (∑ q ∈ Finset.univ.filter fun q => πG6m q = e', SθG6m (ιG6m e) q) = _
  rw [filter_πG6m_image e', Finset.sum_image (fun x _ y _ h => by
      simp only [Prod.mk.injEq, neg_inj] at h
      exact h.2.2),
    ← sum_R3 e.2.2 e'.2.2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [SθG6m, Matrix.of_apply]
  rw [eChar_sG6m_ι e e'.1 e'.2.1 x]

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.eChar_neg_half_nat
#print axioms HaagerupIzumi.C8.Theta.SθEA1A1A2_eq
#print axioms HaagerupIzumi.C8.Theta.SθEG6m_eq
