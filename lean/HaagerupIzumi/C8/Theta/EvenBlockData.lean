module

public import HaagerupIzumi.C8.Theta.EvenBlocks

@[expose] public section

/-!
# The even `S`-block of `L₇ ⊕ A₂` in the manuscript's cosine form

W6 plan item 2, finite part (`Theta/W6_PLAN.md`).  The manuscript (lines 3632–3647 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) prints the even Fourier block on `ℤ/7`,
`S_{00} = -1/√7`, `S_{0r} = -2/√7`, `S_{r0} = -1/√7`, `S_{rs} = -2cos(4πrs/7)/√7`, `0 ≤ r ≤ 3`,
together with the even `A₂` block, and says that multiplication by `η⁸` identifies the
character vector with the Weil representation.  Here the reduced theta matrix `SθEL7A2` of
`Theta/EvenBlocks` (the matrix in the hypothesis `hσS` of `FEL7A2_covariant`,
`m3_first_dimension_of_voa`) is computed in that form:

`SθEL7A2 (r,s) (r',s') = -(1/√21) · C₇(r, r') · C₃(s, s')`, with `C₇(r, 0) = 1`,
`C₇(r, r') = 2cos(4πrr'/7)` (`r' ≠ 0`) and `C₃(s, 0) = 1`, `C₃(s, 1) = 2cos(4πs/3)`
(`SθEL7A2_eq`).  The orbits are listed by a kernel-checked computation
(`filter_πL7A2_product`); the rest is `e(x) + e(-x) = 2cos 2πx`.

Hence `hσS` says that `σ(S)` is the tensor product of the printed `ℤ/7` block (up to the
normalization `-1/√7` vs `-(1/√7)(1/√3)`, absorbed into the `A₂` factor) and the even `A₂`
block, which is the form in which the VOA side provides it.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-- `e(x) + e(-x) = 2 cos 2πx`. -/
theorem eChar_add_eChar_neg (x : ℝ) :
    eChar x + eChar (-x) = ((2 * Real.cos (2 * π * x) : ℝ) : ℂ) := by
  have h : ((2 * π * -x : ℝ) : ℂ) = -((2 * π * x : ℝ) : ℂ) := by push_cast; ring
  rw [eChar, eChar, h, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- `e(-2ra/N) + e(-2rb/N) = 2cos(4πra/N)` when `a + b = N`. -/
theorem pair_eChar (N : ℝ) (hN : N ≠ 0) (r a b : ℕ) (hab : (a : ℝ) + b = N) :
    eChar (-(2 * (r : ℝ) * (a : ℝ) / N)) + eChar (-(2 * (r : ℝ) * (b : ℝ) / N)) =
      ((2 * Real.cos (4 * π * (r : ℝ) * (a : ℝ) / N) : ℝ) : ℂ) := by
  have hb : (b : ℝ) = N - a := by linarith
  have hshift : -(2 * (r : ℝ) * (b : ℝ) / N) = 2 * (r : ℝ) * (a : ℝ) / N + ((-(2 * (r : ℤ)) : ℤ) : ℝ) := by
    rw [hb]
    push_cast
    calc -(2 * (r : ℝ) * (N - a) / N) = 2 * r * a / N - 2 * r * (N / N) := by ring
      _ = 2 * r * a / N + -(2 * r) := by rw [div_self hN]; ring
  rw [eChar_eq_of_sub_eq_int _ hshift, add_comm, eChar_add_eChar_neg]
  congr 2
  ring_nf

theorem sum_pair_fin {n : ℕ} (a b : Fin n) (hab : a ≠ b) (N : ℝ) (hN : N ≠ 0)
    (hsum : ((a : ℕ) : ℝ) + ((b : ℕ) : ℝ) = N) (r : ℕ) :
    ∑ x ∈ ({a, b} : Finset (Fin n)), eChar (-(2 * (r : ℝ) * ((x : ℕ) : ℝ) / N)) =
      ((2 * Real.cos (4 * π * (r : ℝ) * ((a : ℕ) : ℝ) / N) : ℝ) : ℂ) := by
  rw [Finset.sum_pair hab]
  exact pair_eChar N hN r a b hsum

/-- The `ℤ/7` part of the orbits `(±r, ±s)`. -/
def R7 : Fin 4 → Finset (Fin 7) := ![{0}, {1, 6}, {2, 5}, {3, 4}]

/-- The `ℤ/3` part of the orbits. -/
def R3 : Fin 2 → Finset (Fin 3) := ![{0}, {1, 2}]

/-- The orbit of `(r', s')` is `R7 r' × R3 s'` (kernel-checked). -/
theorem filter_πL7A2_product : ∀ e' : Fin 4 × Fin 2,
    (Finset.univ.filter fun q : Fin 7 × Fin 3 => πL7A2 q = e') = R7 e'.1 ×ˢ R3 e'.2 := by
  decide +kernel

/-- `C₇(r, r')`: `1` for `r' = 0`, `2cos(4πrr'/7)` otherwise. -/
def c7 (r r' : Fin 4) : ℝ :=
  if r' = 0 then 1 else 2 * Real.cos (4 * π * ((r : ℕ) : ℝ) * ((r' : ℕ) : ℝ) / 7)

/-- `C₃(s, s')`: `1` for `s' = 0`, `2cos(4πss'/3)` otherwise. -/
def c3 (s s' : Fin 2) : ℝ :=
  if s' = 0 then 1 else 2 * Real.cos (4 * π * ((s : ℕ) : ℝ) * ((s' : ℕ) : ℝ) / 3)

theorem sum_R7 (r r' : Fin 4) :
    ∑ x ∈ R7 r', eChar (-(2 * ((r : ℕ) : ℝ) * ((x : ℕ) : ℝ) / 7)) = ((c7 r r' : ℝ) : ℂ) := by
  fin_cases r'
  · show ∑ x ∈ ({0} : Finset (Fin 7)), _ = _
    rw [Finset.sum_singleton]
    simp [c7, eChar_zero]
  · show ∑ x ∈ ({1, 6} : Finset (Fin 7)), _ = _
    rw [sum_pair_fin (1 : Fin 7) 6 (by decide) 7 (by norm_num)
      (by show ((1 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) = 7; norm_num)]
    rw [c7, if_neg (by decide)]
    rfl
  · show ∑ x ∈ ({2, 5} : Finset (Fin 7)), _ = _
    rw [sum_pair_fin (2 : Fin 7) 5 (by decide) 7 (by norm_num)
      (by show ((2 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) = 7; norm_num)]
    rw [c7, if_neg (by decide)]
    rfl
  · show ∑ x ∈ ({3, 4} : Finset (Fin 7)), _ = _
    rw [sum_pair_fin (3 : Fin 7) 4 (by decide) 7 (by norm_num)
      (by show ((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) = 7; norm_num)]
    rw [c7, if_neg (by decide)]
    rfl

theorem sum_R3 (s s' : Fin 2) :
    ∑ x ∈ R3 s', eChar (-(2 * ((s : ℕ) : ℝ) * ((x : ℕ) : ℝ) / 3)) = ((c3 s s' : ℝ) : ℂ) := by
  fin_cases s'
  · show ∑ x ∈ ({0} : Finset (Fin 3)), _ = _
    rw [Finset.sum_singleton]
    simp [c3, eChar_zero]
  · show ∑ x ∈ ({1, 2} : Finset (Fin 3)), _ = _
    rw [sum_pair_fin (1 : Fin 3) 2 (by decide) 3 (by norm_num)
      (by show ((1 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) = 3; norm_num)]
    rw [c3, if_neg (by decide)]
    rfl

/-- **The even `S`-block of `L₇ ⊕ A₂`**:
`SθE_{(r,s),(r',s')} = -(1/√21) C₇(r, r') C₃(s, s')`. -/
theorem SθEL7A2_eq (e e' : Fin 4 × Fin 2) :
    SθEL7A2 e e' =
      -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) * (((c7 e.1 e'.1 : ℝ) : ℂ) * ((c3 e.2 e'.2 : ℝ) : ℂ)) := by
  show (∑ q ∈ Finset.univ.filter fun q => πL7A2 q = e', SθL7A2 (ιL7A2 e) q) = _
  rw [filter_πL7A2_product e', Finset.sum_product, ← sum_R7 e.1 e'.1, ← sum_R3 e.2 e'.2,
    Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [SθL7A2, Matrix.of_apply, sL7A2]
  rw [neg_add, eChar_add]
  rfl

/-- The `T`-block: `TθE_{(r,s)} = e(r²/7 + s²/3 - 1/3)`. -/
theorem TθEL7A2_eq (e : Fin 4 × Fin 2) :
    TθEL7A2 e e = eChar (((e.1 : ℕ) : ℝ) ^ 2 / 7 + ((e.2 : ℕ) : ℝ) ^ 2 / 3 - 1 / 3) := by
  simp only [TθEL7A2, Matrix.diagonal_apply_eq]
  rfl

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.eChar_add_eChar_neg
#print axioms HaagerupIzumi.C8.Theta.filter_πL7A2_product
#print axioms HaagerupIzumi.C8.Theta.SθEL7A2_eq
#print axioms HaagerupIzumi.C8.Theta.TθEL7A2_eq
