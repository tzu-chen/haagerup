module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import HaagerupIzumi.C8.Data.Lattice
public import HaagerupIzumi.CFT.FiniteClosure

@[expose] public section

/-!
# Bounds for the current projectors and bounded-weight nilpotence

Formalizes Lemma `lem:current-bounds` (lines 2224–2236) and the termination bound after
Lemma `lem:raising` (lines 2289–2295) of `c8_expanded_20260929/haagerup_c8_expanded.tex`.

* `sq_le_mul_of_psd`: Cauchy–Schwarz `(x,y)² ≤ (x,x)(y,y)` for a positive semidefinite
  symmetric bilinear form over any linearly ordered commutative ring (given through its
  quadratic expansion), and `formR_sq_le` for the lattice form on `L ⊗ R` (e.g. `R = ℝ`).
* `cartan_eigenvalue_sq_le`: if `(α,α) ≤ 2d` then `m = (h,α)` satisfies `m² ≤ 2d (h,h)`;
  `momentum_norm_le` derives `(α,α) ≤ 2d` from the weight `(α,α)/2 + N = d` of a Fock
  monomial.  The integral consequences for the two Cartan directions `α_L`
  (`(α_L,α_L) = 2`) and `h_R` (`(h_R,h_R) = 78`): at weight four `|m_L| ≤ 4`,
  `|m_R| ≤ 24`; at weight three `|m_L| ≤ 3`, `|m_R| ≤ 21` and `|m_L + m_R| ≤ 24`.
* Nilpotence: `raisingWord_eq_zero_of_bounded`: in a module spanned by `ℤ`-graded pieces
  supported in `[-B, B]`, every word of length `> B` in two operators raising the grading
  by two vanishes; `raisingWord_length_25_eq_zero` is the case `B = 24` (grading
  `m_L + m_R` at weight three) in the exact form of the nilpotence hypothesis of
  `HaagerupIzumi.CFT.nilpotent_raising_saturation`, and `bounded_raising_saturation`
  combines the two.

Hypotheses: the grading, its support, and the raising property of `E, F` are explicit
hypotheses of the nilpotence statements (in the application they come from the Cartan
eigenvalue bounds above, which are proved).  Identifying Cartan zero modes with
`(h,α)` on Fock monomials is the lattice-VOA construction and is not formalized here.
-/

namespace HaagerupIzumi.C8
namespace Sl2

open _root_.HaagerupIzumi.C8.Lattice

/-! ## Cauchy–Schwarz -/

/-- Cauchy–Schwarz for a positive semidefinite symmetric bilinear form, given through its
quadratic expansion. -/
theorem sq_le_mul_of_psd {R V : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] (B : V → V → R)
    (hexp : ∀ (s t : R) (x y : V), B (s • x + t • y) (s • x + t • y) =
      s ^ 2 * B x x + 2 * s * t * B x y + t ^ 2 * B y y)
    (hpsd : ∀ x, 0 ≤ B x x) (x y : V) : B x y ^ 2 ≤ B x x * B y y := by
  have hP := hpsd x
  have hQ := hpsd y
  have h1 := hpsd (B y y • x + (-B x y) • y)
  have h2 := hpsd ((-B x y) • x + B x x • y)
  have h3 := hpsd ((1 : R) • x + (1 : R) • y)
  have h4 := hpsd ((1 : R) • x + (-1 : R) • y)
  rw [hexp] at h1 h2 h3 h4
  have h1' : 0 ≤ B y y * (B x x * B y y - B x y ^ 2) := by linarith
  have h2' : 0 ≤ B x x * (B x x * B y y - B x y ^ 2) := by linarith
  rcases hQ.lt_or_eq with hQpos | hQ0
  · have := nonneg_of_mul_nonneg_right h1' hQpos
    linarith
  · rcases hP.lt_or_eq with hPpos | hP0
    · have := nonneg_of_mul_nonneg_right h2' hPpos
      linarith
    · have hC : B x y = 0 := by linarith
      rw [hC, ← hP0]
      norm_num

/-- Cauchy–Schwarz for the lattice form on `L ⊗ R`. -/
theorem formR_sq_le {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (h α : Fin 8 → R) : formR h α ^ 2 ≤ formR h h * formR α α :=
  sq_le_mul_of_psd formR formR_expand formR_self_nonneg h α

/-- Lemma `lem:current-bounds`: if `(α,α) ≤ 2d`, the Cartan eigenvalue `m = (h,α)` satisfies
`m² ≤ 2d (h,h)`, for any `h ∈ L ⊗ R`. -/
theorem cartan_eigenvalue_sq_le {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (h α : Fin 8 → R) (d : R) (hα : formR α α ≤ 2 * d) :
    formR h α ^ 2 ≤ 2 * d * formR h h :=
  calc formR h α ^ 2 ≤ formR h h * formR α α := formR_sq_le h α
    _ ≤ formR h h * (2 * d) := mul_le_mul_of_nonneg_left hα (formR_self_nonneg h)
    _ = 2 * d * formR h h := by ring

/-- Cauchy–Schwarz for the integral lattice form. -/
theorem form_sq_le (h α : Fin 8 → ℤ) : form h α ^ 2 ≤ form h h * form α α :=
  sq_le_mul_of_psd form
    (fun s t x y => by simp only [form_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    form_self_nonneg h α

/-- A Fock monomial `h₁(-n₁)⋯h_r(-n_r) e^α` of weight `d = (α,α)/2 + ∑ nᵢ` has
`(α,α) ≤ 2d`. -/
theorem momentum_norm_le (α : Fin 8 → ℤ) (N d : ℤ) (hN : 0 ≤ N)
    (hd : form α α / 2 + N = d) : form α α ≤ 2 * d := by
  obtain ⟨q, hq⟩ : ∃ q, form α α = 2 * q := ⟨_, form_self_eq_two_mul α⟩
  omega

/-- At weight four, `|m_L| ≤ 4`. -/
theorem leftWeight_bound_four (α : Fin 8 → ℤ) (hα : form α α ≤ 2 * 4) :
    |form alphaL α| ≤ 4 := by
  have h1 := form_sq_le alphaL α
  rw [alphaL_norm] at h1
  have h2 : form alphaL α ^ 2 < 5 ^ 2 := by linarith
  have h3 := abs_lt_of_sq_lt_sq h2 (by norm_num)
  linarith

/-- At weight four, `|m_R| ≤ 24`. -/
theorem rightWeight_bound_four (α : Fin 8 → ℤ) (hα : form α α ≤ 2 * 4) :
    |form hR α| ≤ 24 := by
  have h1 := form_sq_le hR α
  rw [hR_norm] at h1
  have h2 : form hR α ^ 2 < 25 ^ 2 := by linarith
  have h3 := abs_lt_of_sq_lt_sq h2 (by norm_num)
  linarith

/-- At weight three, `|m_L| ≤ 3`. -/
theorem leftWeight_bound_three (α : Fin 8 → ℤ) (hα : form α α ≤ 2 * 3) :
    |form alphaL α| ≤ 3 := by
  have h1 := form_sq_le alphaL α
  rw [alphaL_norm] at h1
  have h2 : form alphaL α ^ 2 < 4 ^ 2 := by linarith
  have h3 := abs_lt_of_sq_lt_sq h2 (by norm_num)
  linarith

/-- At weight three, `|m_R| ≤ 21`. -/
theorem rightWeight_bound_three (α : Fin 8 → ℤ) (hα : form α α ≤ 2 * 3) :
    |form hR α| ≤ 21 := by
  have h1 := form_sq_le hR α
  rw [hR_norm] at h1
  have h2 : form hR α ^ 2 < 22 ^ 2 := by linarith
  have h3 := abs_lt_of_sq_lt_sq h2 (by norm_num)
  linarith

/-- At weight three the grading `m_L + m_R` lies in `[-24, 24]`. -/
theorem totalWeight_bound_three (α : Fin 8 → ℤ) (hα : form α α ≤ 2 * 3) :
    |form alphaL α + form hR α| ≤ 24 := by
  have hL := abs_le.mp (leftWeight_bound_three α hα)
  have hR' := abs_le.mp (rightWeight_bound_three α hα)
  rw [abs_le]
  constructor <;> linarith [hL.1, hL.2, hR'.1, hR'.2]

/-! ## Bounded-weight nilpotence -/

section Nilpotence

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

open HaagerupIzumi.CFT

/-- A word of length `n` in two operators raising a `ℤ`-grading by two raises it by `2n`. -/
theorem raisingWord_mem_grade (gr : ℤ → Submodule R M) (E F : M →ₗ[R] M)
    (hE : ∀ k, ∀ x ∈ gr k, E x ∈ gr (k + 2)) (hF : ∀ k, ∀ x ∈ gr k, F x ∈ gr (k + 2)) :
    ∀ (w : List Bool) (k : ℤ) (x : M), x ∈ gr k →
      raisingWord E F w x ∈ gr (k + 2 * (w.length : ℤ)) := by
  intro w
  induction w with
  | nil =>
    intro k x hx
    simpa [raisingWord] using hx
  | cons b w ih =>
    intro k x hx
    have hw := ih k x hx
    have e : k + 2 * ((b :: w).length : ℤ) = (k + 2 * (w.length : ℤ)) + 2 := by
      simp only [List.length_cons]; push_cast; ring
    rw [e]
    cases b with
    | false => exact hF _ _ hw
    | true => exact hE _ _ hw

/-- Words of length `> B` vanish when the grading is supported in `[-B, B]`. -/
theorem raisingWord_eq_zero_of_bounded (gr : ℤ → Submodule R M) (hspan : ⨆ k, gr k = ⊤)
    (B : ℕ) (hsupp : ∀ k : ℤ, (k < -(B : ℤ) ∨ (B : ℤ) < k) → gr k = ⊥)
    (E F : M →ₗ[R] M)
    (hE : ∀ k, ∀ x ∈ gr k, E x ∈ gr (k + 2)) (hF : ∀ k, ∀ x ∈ gr k, F x ∈ gr (k + 2))
    (w : List Bool) (hw : B < w.length) (v : M) : raisingWord E F w v = 0 := by
  have hv : v ∈ ⨆ k, gr k := by rw [hspan]; exact Submodule.mem_top
  refine Submodule.iSup_induction gr (motive := fun x => raisingWord E F w x = 0) hv
    ?_ ?_ ?_
  · intro k x hx
    by_cases hk : k < -(B : ℤ)
    · rw [hsupp k (Or.inl hk)] at hx
      rw [(Submodule.mem_bot R).mp hx, map_zero]
    · have h1 := raisingWord_mem_grade gr E F hE hF w k x hx
      rw [hsupp (k + 2 * (w.length : ℤ)) (Or.inr (by omega))] at h1
      exact (Submodule.mem_bot R).mp h1
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The weight-three case: with grading `m_L + m_R` supported in `[-24, 24]`, every word of
length `25` in the two raising operators vanishes.  This is the nilpotence hypothesis
`hnil` of `HaagerupIzumi.CFT.nilpotent_raising_saturation` with `N = 25`. -/
theorem raisingWord_length_25_eq_zero (gr : ℤ → Submodule R M) (hspan : ⨆ k, gr k = ⊤)
    (hsupp : ∀ k : ℤ, (k < -24 ∨ 24 < k) → gr k = ⊥) (E F : M →ₗ[R] M)
    (hE : ∀ k, ∀ x ∈ gr k, E x ∈ gr (k + 2)) (hF : ∀ k, ∀ x ∈ gr k, F x ∈ gr (k + 2)) :
    ∀ w : List Bool, w.length = 25 → ∀ v : M, raisingWord E F w v = 0 :=
  fun w hw v => raisingWord_eq_zero_of_bounded gr hspan 24 (by exact_mod_cast hsupp) E F hE hF
    w (by omega) v

/-- Raising saturation with the explicit termination bound: a subspace `C` stable under
`E, F` with `M = E M + F M + C` is everything, when `M` is graded in `[-24, 24]` and `E, F`
raise the grading by two. -/
theorem bounded_raising_saturation (C : Submodule R M) (gr : ℤ → Submodule R M)
    (hspan : ⨆ k, gr k = ⊤) (hsupp : ∀ k : ℤ, (k < -24 ∨ 24 < k) → gr k = ⊥)
    (E F : M →ₗ[R] M)
    (hE : ∀ k, ∀ x ∈ gr k, E x ∈ gr (k + 2)) (hF : ∀ k, ∀ x ∈ gr k, F x ∈ gr (k + 2))
    (hEC : ∀ x ∈ C, E x ∈ C) (hFC : ∀ x ∈ C, F x ∈ C)
    (hspanC : ∀ v : M, ∃ x y c : M, c ∈ C ∧ v = E x + F y + c) : ∀ v : M, v ∈ C :=
  nilpotent_raising_saturation C E F hEC hFC hspanC 25
    (raisingWord_length_25_eq_zero gr hspan hsupp E F hE hF)

end Nilpotence

#print axioms sq_le_mul_of_psd
#print axioms formR_sq_le
#print axioms cartan_eigenvalue_sq_le
#print axioms form_sq_le
#print axioms momentum_norm_le
#print axioms leftWeight_bound_four
#print axioms rightWeight_bound_four
#print axioms leftWeight_bound_three
#print axioms rightWeight_bound_three
#print axioms totalWeight_bound_three
#print axioms raisingWord_mem_grade
#print axioms raisingWord_eq_zero_of_bounded
#print axioms raisingWord_length_25_eq_zero
#print axioms bounded_raising_saturation

end Sl2
end HaagerupIzumi.C8
