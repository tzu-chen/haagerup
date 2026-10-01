module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Cube-root twists in the near-group and rank-six induction lemmas

Two steps of Appendix G separate a twist equation over the disjoint fields `ℚ(d)` and
`ℚ(ζ₃)`:

* Lemma `lem:near-group-induction` (lines 3434–3444): the first indicator gives
  `2 + 2θ_C + θ_D + θ_E = 0` with cube-root twists, which "forces `θ_C = ζ` and
  `θ_D = θ_E = ζ²`, up to simultaneous conjugation"; the second gives `c = k`, `p + q = k`.
* Lemma `lem:rank6-induction` (lines 3883–3897): `∑_j (2 + 3 b_j d) θ_{C_j} = 0`, with
  cube-root twists and `d` irrational, forces the twists to be `1, ζ₃, ζ₃²` once each and
  `b_j = m` for all `j` (given `∑ b_j = 3m`).

Here `ζ₃ = -1/2 + (√3/2) i`.  That the twists are cube roots of unity follows from the
Ng–Schauenburg twist-trace formula with `ν₃(a) = 1` by equality in the triangle inequality
(`eq_one_of_weighted_sum`, applied to `w_j = θ_j³`); the trace formula and the indicator
equations themselves (Ostrik's induction–codegree correspondence) are external.
-/

namespace HaagerupIzumi.C8.CubeRootTwists

open Complex

/-- `ζ₃ = -1/2 + (√3/2) i`. -/
noncomputable def zeta3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

private lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

theorem zeta3_sq : zeta3 ^ 2 = -1 - zeta3 := by
  apply Complex.ext <;> simp [zeta3, pow_two] <;> nlinarith [sqrt3_sq]

theorem zeta3_cube : zeta3 ^ 3 = 1 := by
  have h : zeta3 ^ 3 = zeta3 * zeta3 ^ 2 := by ring
  rw [h, zeta3_sq]
  have h2 := zeta3_sq
  linear_combination (-1 : ℂ) * h2

theorem zeta3_im : zeta3.im = Real.sqrt 3 / 2 := rfl

/-- `1` and `ζ₃` are linearly independent over `ℝ`. -/
theorem indep (a b : ℝ) (h : (a : ℂ) + (b : ℂ) * zeta3 = 0) : a = 0 ∧ b = 0 := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zeta3_im,
    Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re] at him hre
  have hz : zeta3.re = -1 / 2 := rfl
  rw [hz] at hre
  have hs := sqrt3_pos
  have hb : b = 0 := by nlinarith
  subst hb
  constructor <;> linarith

theorem isPrimitiveRoot_zeta3 : IsPrimitiveRoot zeta3 3 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) zeta3_cube fun l hl0 hl3 => ?_
  have hs := sqrt3_pos
  interval_cases l
  · intro h
    rw [pow_one] at h
    have := congrArg Complex.im h
    rw [zeta3_im, Complex.one_im] at this
    linarith
  · intro h
    rw [zeta3_sq] at h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.neg_im, Complex.one_im, zeta3_im] at this
    linarith

/-- Every cube root of unity is a power of `ζ₃`. -/
theorem eq_zeta3_pow {θ : ℂ} (hθ : θ ^ 3 = 1) : ∃ e : Fin 3, θ = zeta3 ^ (e : ℕ) := by
  obtain ⟨i, hi, h⟩ := isPrimitiveRoot_zeta3.eq_pow_of_pow_eq_one hθ
  exact ⟨⟨i, hi⟩, h.symm⟩

/-- Coordinates of `ζ₃^e` in the basis `1, ζ₃`. -/
def powZ : Fin 3 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, -1)

theorem zeta3_pow (e : Fin 3) :
    zeta3 ^ (e : ℕ) = ((powZ e).1 : ℂ) + ((powZ e).2 : ℂ) * zeta3 := by
  fin_cases e
  · simp [powZ]
  · simp [powZ]
  · simp only [powZ]
    rw [zeta3_sq]
    push_cast
    ring

/-- **Near-group twists** (Lemma `lem:near-group-induction`).  If
`2 + 2θ_C + θ_D + θ_E = 0` for cube roots of unity, then `θ_C = ζ₃`, `θ_D = θ_E = ζ₃²`, or
the simultaneous conjugate. -/
theorem neargroup_twists (eC eD eE : Fin 3)
    (h : (2 : ℂ) + 2 * zeta3 ^ (eC : ℕ) + zeta3 ^ (eD : ℕ) + zeta3 ^ (eE : ℕ) = 0) :
    (eC = 1 ∧ eD = 2 ∧ eE = 2) ∨ (eC = 2 ∧ eD = 1 ∧ eE = 1) := by
  rw [zeta3_pow, zeta3_pow, zeta3_pow] at h
  have h' : (((2 + 2 * (powZ eC).1 + (powZ eD).1 + (powZ eE).1 : ℤ) : ℝ) : ℂ) +
      (((2 * (powZ eC).2 + (powZ eD).2 + (powZ eE).2 : ℤ) : ℝ) : ℂ) * zeta3 = 0 := by
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ := indep _ _ h'
  have h1' : 2 + 2 * (powZ eC).1 + (powZ eD).1 + (powZ eE).1 = 0 := by exact_mod_cast h1
  have h2' : 2 * (powZ eC).2 + (powZ eD).2 + (powZ eE).2 = 0 := by exact_mod_cast h2
  clear h h' h1 h2
  revert h1' h2'
  revert eC eD eE
  decide

/-- The second near-group equation `k + c θ_C + p θ_D + q θ_E = 0` with
`θ_D = θ_E = conj θ_C` primitive gives `c = k` and `p + q = k`. -/
theorem neargroup_multiplicities (k c p q : ℕ) (eC eD : Fin 3)
    (hC : (eC = 1 ∧ eD = 2) ∨ (eC = 2 ∧ eD = 1))
    (h : (k : ℂ) + c * zeta3 ^ (eC : ℕ) + p * zeta3 ^ (eD : ℕ) + q * zeta3 ^ (eD : ℕ) = 0) :
    c = k ∧ p + q = k := by
  rw [zeta3_pow, zeta3_pow] at h
  have h' : (((k + c * (powZ eC).1 + (p + q) * (powZ eD).1 : ℤ) : ℝ) : ℂ) +
      (((c * (powZ eC).2 + (p + q) * (powZ eD).2 : ℤ) : ℝ) : ℂ) * zeta3 = 0 := by
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ := indep _ _ h'
  have h1' : (k : ℤ) + c * (powZ eC).1 + (p + q) * (powZ eD).1 = 0 := by exact_mod_cast h1
  have h2' : (c : ℤ) * (powZ eC).2 + (p + q) * (powZ eD).2 = 0 := by exact_mod_cast h2
  rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [powZ] at h1' h2' <;> constructor <;> omega

/-- The permutations of `Fin 3` are the only exponent triples with `1 + ζ + ζ²`-type sum zero. -/
theorem sum_zero_iff_perm :
    ∀ e₀ e₁ e₂ : Fin 3, (powZ e₀).1 + (powZ e₁).1 + (powZ e₂).1 = 0 →
      (powZ e₀).2 + (powZ e₁).2 + (powZ e₂).2 = 0 →
      e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ := by
  decide

/-- The six permutations of `Fin 3`. -/
theorem perm_cases : ∀ e₀ e₁ e₂ : Fin 3, e₀ ≠ e₁ → e₀ ≠ e₂ → e₁ ≠ e₂ →
    (e₀ = 0 ∧ e₁ = 1 ∧ e₂ = 2) ∨ (e₀ = 0 ∧ e₁ = 2 ∧ e₂ = 1) ∨ (e₀ = 1 ∧ e₁ = 0 ∧ e₂ = 2) ∨
    (e₀ = 1 ∧ e₁ = 2 ∧ e₂ = 0) ∨ (e₀ = 2 ∧ e₁ = 0 ∧ e₂ = 1) ∨ (e₀ = 2 ∧ e₁ = 1 ∧ e₂ = 0) := by
  decide

/-- **Rank-six twists** (Lemma `lem:rank6-induction`).  If `d` is irrational,
`∑_j (2 + 3 b_j d) θ_j = 0` for three cube roots of unity `θ_j = ζ₃^{e_j}`, and
`b₀ + b₁ + b₂ = 3m`, then the `θ_j` are `1, ζ₃, ζ₃²` once each and `b_j = m` for all `j`. -/
theorem rank6_twists (m : ℕ) (d : ℝ) (hd : Irrational d) (e₀ e₁ e₂ : Fin 3) (b₀ b₁ b₂ : ℕ)
    (hb : b₀ + b₁ + b₂ = 3 * m)
    (h : ((2 : ℂ) + 3 * b₀ * d) * zeta3 ^ (e₀ : ℕ) + ((2 : ℂ) + 3 * b₁ * d) * zeta3 ^ (e₁ : ℕ) +
      ((2 : ℂ) + 3 * b₂ * d) * zeta3 ^ (e₂ : ℕ) = 0) :
    (e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂) ∧ b₀ = m ∧ b₁ = m ∧ b₂ = m := by
  rw [zeta3_pow, zeta3_pow, zeta3_pow] at h
  set U1 : ℤ := (powZ e₀).1 + (powZ e₁).1 + (powZ e₂).1
  set V1 : ℤ := (powZ e₀).2 + (powZ e₁).2 + (powZ e₂).2
  set U2 : ℤ := b₀ * (powZ e₀).1 + b₁ * (powZ e₁).1 + b₂ * (powZ e₂).1
  set V2 : ℤ := b₀ * (powZ e₀).2 + b₁ * (powZ e₁).2 + b₂ * (powZ e₂).2
  have h' : ((((2 * U1 : ℤ) : ℝ) + 3 * d * (U2 : ℝ) : ℝ) : ℂ) +
      ((((2 * V1 : ℤ) : ℝ) + 3 * d * (V2 : ℝ) : ℝ) : ℂ) * zeta3 = 0 := by
    simp only [U1, V1, U2, V2]
    push_cast
    linear_combination h
  obtain ⟨hA, hB⟩ := indep _ _ h'
  have key : ∀ X Y : ℤ, ((2 * X : ℤ) : ℝ) + 3 * d * (Y : ℝ) = 0 → X = 0 ∧ Y = 0 := by
    intro X Y hXY
    by_cases hY : Y = 0
    · subst hY
      simp at hXY
      exact ⟨by exact_mod_cast hXY, rfl⟩
    · exfalso
      apply hd.ne_rational (-2 * X) (3 * Y)
      have hY' : (Y : ℝ) ≠ 0 := by exact_mod_cast hY
      push_cast at hXY ⊢
      field_simp
      linarith
  obtain ⟨hU1, hU2⟩ := key U1 U2 hA
  obtain ⟨hV1, hV2⟩ := key V1 V2 hB
  have hperm := sum_zero_iff_perm e₀ e₁ e₂ hU1 hV1
  refine ⟨hperm, ?_⟩
  simp only [U2, V2] at hU2 hV2
  clear h h' hA hB key hU1 hV1
  obtain ⟨h01, h02, h12⟩ := hperm
  rcases perm_cases e₀ e₁ e₂ h01 h02 h12 with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ <;>
  · simp only [powZ] at hU2 hV2
    refine ⟨?_, ?_, ?_⟩ <;> omega


/-- **The cube-root step** (lines 3434–3436 and 3883–3890): if unit complex numbers `w_j`
(here `w_j = θ_j³`) and positive reals `d_j` satisfy `∑ d_j w_j = ∑ d_j` (the center-twist
formula with `ν₃(a) = 1`: `∑ d_{C_j} θ_{C_j}³ = Dim 𝓕 = ∑ d_{C_j}`), then every `w_j = 1`
(equality in the triangle inequality). -/
theorem eq_one_of_weighted_sum {ι : Type*} (s : Finset ι) (d : ι → ℝ) (w : ι → ℂ)
    (hd : ∀ j ∈ s, 0 < d j) (hw : ∀ j ∈ s, ‖w j‖ = 1)
    (hsum : ∑ j ∈ s, (d j : ℂ) * w j = ∑ j ∈ s, (d j : ℂ)) : ∀ j ∈ s, w j = 1 := by
  -- real parts: `∑ d_j (1 - Re w_j) = 0` with nonnegative terms
  have hre := congrArg Complex.re hsum
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  have hle : ∀ j ∈ s, (w j).re ≤ 1 := fun j hj => by
    have := Complex.re_le_norm (w j)
    rw [hw j hj] at this
    exact this
  have hterm : ∀ j ∈ s, d j * (1 - (w j).re) = 0 := by
    have hnn : ∀ j ∈ s, 0 ≤ d j * (1 - (w j).re) := fun j hj =>
      mul_nonneg (hd j hj).le (by linarith [hle j hj])
    have htot : ∑ j ∈ s, d j * (1 - (w j).re) = 0 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 htot
  intro j hj
  have h1 : (w j).re = 1 := by
    have := hterm j hj
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hd j hj).ne'
    · linarith
  -- `|w| = 1` and `Re w = 1` force `Im w = 0`
  have hn := hw j hj
  have hsq : (w j).re ^ 2 + (w j).im ^ 2 = 1 := by
    have := Complex.sq_norm (w j)
    rw [hn, Complex.normSq_apply] at this
    nlinarith
  have him : (w j).im = 0 := by
    rw [h1] at hsq
    nlinarith
  exact Complex.ext h1 (by simpa using him)

#print axioms eq_one_of_weighted_sum
#print axioms neargroup_twists
#print axioms rank6_twists

end HaagerupIzumi.C8.CubeRootTwists
