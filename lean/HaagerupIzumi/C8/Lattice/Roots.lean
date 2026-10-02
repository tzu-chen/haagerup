module

public import HaagerupIzumi.C8.Lattice.Data
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The 78 roots of `E₆ ⊕ A₂` are all its norm-two vectors

Work item W1 of `C8/ROADMAP.md`; the weight-one count `dim B₁ = 8 + 78 = 86` (line 222 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`, weight formula at line 1890) needs the roots of
`L = E₆ ⊕ A₂`.

* `norm_eq_two_iff`: `(x,x) = 2 ↔ x ∈ roots` for every `x : Mom` (also `form_eq_two_iff` for
  `Lattice.form`), with `roots_length : roots.length = 78` and `roots_nodup`.
* Method: the sum-of-squares certificate `Lattice.four_mul_form_self`, read as
  `4(x,x) = 3x₀² + y₅² + y₄² + y₃² + y₂² + y₁² + 4(x₆² + x₇² + (x₆-x₇)²)` (`four_mul_norm`),
  bounds each coordinate given the previous ones (`|yᵢ| ≤ 2`, Fincke–Pohst); `roots_check`
  enumerates the resulting finite tree by kernel evaluation (`decide +kernel`).
* `Mom.norm_nonneg`, `Mom.norm_even`, `Mom.eq_zero_of_norm_eq_zero`: positivity and evenness
  transported from `Data/Lattice`.

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

-- Sequential elaboration keeps the kernel evaluations from running concurrently (memory).
set_option Elab.async false

/-! ## Facts about the norm -/

theorem Mom.norm_nonneg (x : Mom) : 0 ≤ x.norm := by
  rw [Mom.norm, Mom.form_eq]
  exact Lattice.form_self_nonneg _

theorem Mom.norm_even (x : Mom) : ∃ q, x.norm = 2 * q := by
  have h := Lattice.form_self_eq_two_mul x.toVec
  rw [Mom.norm, Mom.form_eq]
  exact ⟨_, h⟩

theorem Mom.eq_zero_of_norm_eq_zero {x : Mom} (h : x.norm = 0) : x = Mom.zero := by
  by_contra hx
  have hv : x.toVec ≠ 0 := by
    intro h0
    apply hx
    have h1 := congrArg Mom.ofVec h0
    rw [Mom.ofVec_toVec] at h1
    exact h1
  have hp := Lattice.form_self_pos hv
  rw [Mom.norm, Mom.form_eq] at h
  omega

/-! ## The norm-two vectors -/

/-- The integers `lo, …, hi`. -/
def zr (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun k : ℕ => lo + (k : ℤ)

theorem mem_zr {lo hi n : ℤ} (h1 : lo ≤ n) (h2 : n ≤ hi) : n ∈ zr lo hi := by
  unfold zr
  rw [List.mem_map]
  exact ⟨(n - lo).toNat, List.mem_range.mpr (by omega), by omega⟩

/-- Partial sums of the sum-of-squares certificate of `4 (x,x)` on `E₆`
(`y₅ = 2x₄ - x₀`, `y₄ = 2x₃ - 2x₄ - x₀`, `y₃ = 2x₂ - 2x₃ - x₀`,
`y₂ = 2x₁ - 2x₂ + 2x₅ - x₀`, `y₁ = x₀ - 2x₁ + 2x₅`). -/
def pE0 (a e : ℤ) : ℤ := 3 * (a * a) + (-a + 2 * e) * (-a + 2 * e)

def pE1 (a e d : ℤ) : ℤ := pE0 a e + (-a + 2 * d - 2 * e) * (-a + 2 * d - 2 * e)

def pE2 (a e d c : ℤ) : ℤ := pE1 a e d + (-a + 2 * c - 2 * d) * (-a + 2 * c - 2 * d)

def pE3 (a e d c f b : ℤ) : ℤ :=
  pE2 a e d c + (-a + 2 * b - 2 * c + 2 * f) * (-a + 2 * b - 2 * c + 2 * f)
    + (a - 2 * b + 2 * f) * (a - 2 * b + 2 * f)

theorem four_mul_norm (x : Mom) :
    4 * x.norm = pE3 x.x0 x.x4 x.x3 x.x2 x.x5 x.x1
      + 4 * (x.x6 * x.x6 + x.x7 * x.x7 + (x.x6 - x.x7) * (x.x6 - x.x7)) := by
  simp only [Mom.norm, Mom.form, pE3, pE2, pE1, pE0]
  ring

/-- **Finite check** (kernel evaluation): every lattice vector in the Fincke–Pohst tree of
the certificate with norm two is in `roots`.  The ranges are those forced by
`|yᵢ| ≤ 2` given the previous coordinates. -/
theorem roots_check :
    ∀ a ∈ zr (-1) 1, ∀ e ∈ zr ((a - 1) / 2) ((a + 2) / 2), pE0 a e ≤ 8 →
    ∀ d ∈ zr ((a + 2 * e - 1) / 2) ((a + 2 * e + 2) / 2), pE1 a e d ≤ 8 →
    ∀ c ∈ zr ((a + 2 * d - 1) / 2) ((a + 2 * d + 2) / 2), pE2 a e d c ≤ 8 →
    ∀ f ∈ zr ((2 * c - 1) / 4) ((2 * c + 4) / 4),
    ∀ b ∈ zr ((a + 2 * f - 1) / 2) ((a + 2 * f + 2) / 2), pE3 a e d c f b ≤ 8 →
    ∀ g ∈ zr (-1) 1, ∀ h ∈ zr (-1) 1,
      pE3 a e d c f b + 4 * (g * g + h * h + (g - h) * (g - h)) = 8 →
        (⟨a, b, c, d, e, f, g, h⟩ : Mom) ∈ roots := by
  decide +kernel

theorem roots_norm : ∀ r ∈ roots, r.norm = 2 := by
  decide +kernel

/-- An integer key of a lattice vector, for cheap duplicate checks (`List.Nodup.of_map`). -/
def Mom.key (x : Mom) : ℤ :=
  ((((((x.x0 * 8 + x.x1) * 8 + x.x2) * 8 + x.x3) * 8 + x.x4) * 8 + x.x5) * 8 + x.x6) * 8 + x.x7

theorem roots_keys_nodup : (roots.map Mom.key).Nodup := by
  decide +kernel

theorem roots_nodup : roots.Nodup := List.Nodup.of_map _ roots_keys_nodup

theorem roots_length : roots.length = 78 := by
  decide +kernel

theorem bound8 {y : ℤ} (h : y * y ≤ 8) : -2 ≤ y ∧ y ≤ 2 := by
  constructor <;> nlinarith

theorem bound2 {y : ℤ} (h : y * y ≤ 2) : -1 ≤ y ∧ y ≤ 1 := by
  constructor <;> nlinarith

/-- **The norm-two vectors of `E₆ ⊕ A₂` are exactly the 78 listed roots.** -/
theorem norm_eq_two_iff (x : Mom) : x.norm = 2 ↔ x ∈ roots := by
  refine ⟨fun hn => ?_, fun hr => roots_norm x hr⟩
  obtain ⟨a, b, c, d, e, f, g, h⟩ := x
  have hs0 := four_mul_norm ⟨a, b, c, d, e, f, g, h⟩
  simp only at hs0
  rw [hn] at hs0
  have hleaf : pE3 a e d c f b + 4 * (g * g + h * h + (g - h) * (g - h)) = 8 := by linarith
  have hs := hs0
  simp only [pE3, pE2, pE1, pE0] at hs
  have s1 := mul_self_nonneg a
  have s2 := mul_self_nonneg (-a + 2 * e)
  have s3 := mul_self_nonneg (-a + 2 * d - 2 * e)
  have s4 := mul_self_nonneg (-a + 2 * c - 2 * d)
  have s5 := mul_self_nonneg (-a + 2 * b - 2 * c + 2 * f)
  have s6 := mul_self_nonneg (a - 2 * b + 2 * f)
  have s7 := mul_self_nonneg g
  have s8 := mul_self_nonneg h
  have s9 := mul_self_nonneg (g - h)
  have p0 : pE0 a e ≤ 8 := by simp only [pE0]; linarith
  have p1 : pE1 a e d ≤ 8 := by simp only [pE1, pE0]; linarith
  have p2 : pE2 a e d c ≤ 8 := by simp only [pE2, pE1, pE0]; linarith
  have p3 : pE3 a e d c f b ≤ 8 := by simp only [pE3, pE2, pE1, pE0]; linarith
  have ha := bound2 (show a * a ≤ 2 by linarith)
  have hy5 := bound8 (show (-a + 2 * e) * (-a + 2 * e) ≤ 8 by linarith)
  have hy4 := bound8 (show (-a + 2 * d - 2 * e) * (-a + 2 * d - 2 * e) ≤ 8 by linarith)
  have hy3 := bound8 (show (-a + 2 * c - 2 * d) * (-a + 2 * c - 2 * d) ≤ 8 by linarith)
  have hy2 := bound8
    (show (-a + 2 * b - 2 * c + 2 * f) * (-a + 2 * b - 2 * c + 2 * f) ≤ 8 by linarith)
  have hy1 := bound8 (show (a - 2 * b + 2 * f) * (a - 2 * b + 2 * f) ≤ 8 by linarith)
  have hg := bound2 (show g * g ≤ 2 by linarith)
  have hh := bound2 (show h * h ≤ 2 by linarith)
  exact roots_check a (mem_zr (by omega) (by omega)) e (mem_zr (by omega) (by omega)) p0
    d (mem_zr (by omega) (by omega)) p1 c (mem_zr (by omega) (by omega)) p2
    f (mem_zr (by omega) (by omega)) b (mem_zr (by omega) (by omega)) p3
    g (mem_zr (by omega) (by omega)) h (mem_zr (by omega) (by omega)) hleaf

/-- The same statement for the form of `Data/Lattice`. -/
theorem form_eq_two_iff (x : Fin 8 → ℤ) : Lattice.form x x = 2 ↔ Mom.ofVec x ∈ roots := by
  rw [← Mom.form_ofVec]
  exact norm_eq_two_iff _

#print axioms norm_eq_two_iff
#print axioms form_eq_two_iff
#print axioms roots_nodup
#print axioms Mom.eq_zero_of_norm_eq_zero

end LatticeVOA
end HaagerupIzumi.C8
