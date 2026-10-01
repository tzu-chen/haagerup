module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Finite arithmetic of the complete character vector

Section `sec:characters` (lines 4136–4211 of the expanded draft) uses the twelve
center twists of Lemma `lem:six-residual-twists` (line 4053) and strict positivity
of nonvacuum lowest weights.  This file checks the finite steps of that argument:

* `pole_iff`: with central charge `8` (character exponent `h - 1/3`), a nonvacuum
  simple whose lowest weight `h > 0` is congruent to its twist exponent can have
  a polar term `q^(h-1/3)` only if its twist exponent is `2/13` and `h = 2/13`;
  the pole is then `q^(-7/39)` (`pole_exponent`).
* `character_T_fixed_iff`: the character `T` eigenvalue `exp(2πi(t - 1/3))` is
  trivial only for the twist exponent `1/3`, i.e. for the single label `c₁`; this is
  the finite part of Lemma `lem:haagerup-character-unique`.
* `gamma_eq_zero`: `dim U₁ = 6 + 13γ` and `dim U₁ = 6` give `γ = 0`.
* The lowest-weight table (line 4178): its twist exponents are the center twist
  list, its maximum is `15/13 < 17/10`, and the next tops `4/3`, `5/3` of the
  unmixed lattice sectors exceed `15/13` (Corollary
  `cor:unmixed-lattice-restrictions`).

The table `lowestWeight`/`topDim`/`twistExp` is *input data*: the twists are those of Lemma
`lem:six-residual-twists` (`NumberTheory.six_residual_twists`), and the lowest weights and top
dimensions are read off the `γ = 0` Evans–Gannon vector.  The theorems here are finite
consequences of that table, not a derivation of it.  Lemma `lem:pole-cancellation` is proved in
`Analytic/PoleCancellation.lean`; finite image (DLN) and the Evans–Gannon fundamental matrix
are external.
-/

namespace HaagerupIzumi.C8.Characters

/-- Labels of the twelve simple `U`-modules, as in the table at line 4178. -/
inductive Label
  | o | b | a | c0 | c1 | c2 | d1 | d2 | d3 | d4 | d5 | d6
  deriving DecidableEq, Repr

/-- All twelve labels, in the order of the table at line 4178. -/
def allLabels : List Label := [.o, .b, .a, .c0, .c1, .c2, .d1, .d2, .d3, .d4, .d5, .d6]

theorem mem_allLabels (l : Label) : l ∈ allLabels := by
  cases l <;> simp [allLabels]

theorem allLabels_nodup : allLabels.Nodup := by decide

instance : Fintype Label := ⟨⟨allLabels, allLabels_nodup⟩, mem_allLabels⟩

/-- Lowest conformal weights of the twelve simple modules (line 4178). -/
def lowestWeight : Label → ℚ
  | .o => 0 | .b => 1 | .a => 1 | .c0 => 1 | .c1 => 1 / 3 | .c2 => 2 / 3
  | .d1 => 6 / 13 | .d2 => 11 / 13 | .d3 => 15 / 13 | .d4 => 5 / 13
  | .d5 => 7 / 13 | .d6 => 8 / 13

/-- Top dimensions of the twelve simple modules (line 4178). -/
def topDim : Label → ℕ
  | .o => 1 | .b => 80 | .a => 81 | .c0 => 81 | .c1 => 3 | .c2 => 27
  | .d1 => 7 | .d2 => 42 | .d3 => 119 | .d4 => 5 | .d5 => 13 | .d6 => 14

/-- The categorical twist exponent `t ∈ [0,1)` with `θ = exp(2πi t)`: the fractional
part of the lowest weight. -/
def twistExp : Label → ℚ
  | .o => 0 | .b => 0 | .a => 0 | .c0 => 0 | .c1 => 1 / 3 | .c2 => 2 / 3
  | .d1 => 6 / 13 | .d2 => 11 / 13 | .d3 => 2 / 13 | .d4 => 5 / 13
  | .d5 => 7 / 13 | .d6 => 8 / 13

theorem twistExp_eq_fract (l : Label) : twistExp l = Int.fract (lowestWeight l) := by
  rw [eq_comm, Int.fract_eq_iff]
  cases l <;> simp only [twistExp, lowestWeight] <;>
    first
    | (refine ⟨?_, ?_, 0, ?_⟩ <;> norm_num <;> done)
    | (refine ⟨?_, ?_, 1, ?_⟩ <;> norm_num <;> done)

/-- The twist exponents are the center twist list of line 4060:
`0,0,0,0,1/3,2/3` and the six nonresidues `{2,5,6,7,8,11}/13`. -/
theorem twist_list :
    allLabels.map twistExp =
      [0, 0, 0, 0, 1 / 3, 2 / 3, 6 / 13, 11 / 13, 2 / 13, 5 / 13, 7 / 13, 8 / 13] := rfl

/-- **The only allowed nonvacuum pole.**  Let a simple module have twist exponent
`twistExp l` and lowest weight `h > 0` with `h - twistExp l ∈ ℤ` (twists are
`exp(2πi h)`).  Then its character exponent `h - c/24 = h - 1/3` is negative iff the
twist exponent is `2/13` and `h = 2/13`. -/
theorem pole_iff (l : Label) (h : ℚ) (hpos : 0 < h) (hcong : ∃ n : ℤ, h = twistExp l + n) :
    h - 1 / 3 < 0 ↔ (twistExp l = 2 / 13 ∧ h = 2 / 13) := by
  obtain ⟨n, rfl⟩ := hcong
  constructor
  · intro hneg
    have ht0 : 0 ≤ twistExp l := by cases l <;> norm_num [twistExp]
    have ht1 : twistExp l < 1 := by cases l <;> norm_num [twistExp]
    have hn1 : (n : ℚ) < 1 := by linarith
    have hn0 : ((-1 : ℤ) : ℚ) < n := by push_cast; linarith
    have h1 : n < 1 := by exact_mod_cast hn1
    have h0 : -1 < n := by exact_mod_cast hn0
    have hn : n = 0 := by omega
    subst hn
    simp only [Int.cast_zero, add_zero] at hpos hneg ⊢
    cases l <;>
      first
      | (norm_num [twistExp] at hpos; done)
      | (norm_num [twistExp] at hneg; done)
      | (norm_num [twistExp]; done)
  · rintro ⟨_, hh⟩
    rw [hh]
    norm_num

/-- The pole exponent of the twist-`2/13` coordinate. -/
theorem pole_exponent : (2 / 13 : ℚ) - 1 / 3 = -7 / 39 := by norm_num

/-- **Character `T` fixed coordinates.**  The character `T` eigenvalue is
`exp(2πi (t - 1/3))`; it is trivial iff `t - 1/3 ∈ ℤ`, which happens for exactly one
label, `c₁` (categorical twist `exp(2πi/3)`). -/
theorem character_T_fixed_iff (l : Label) :
    (∃ n : ℤ, twistExp l - 1 / 3 = n) ↔ l = .c1 := by
  have key : ∀ (q : ℚ) (K : ℤ), 39 * (q - 1 / 3) = K → ¬ (39 : ℤ) ∣ K →
      ∀ n : ℤ, q - 1 / 3 = n → False := by
    intro q K hq hK n hn
    have h1 : (K : ℚ) = ((39 * n : ℤ) : ℚ) := by rw [← hq, hn]; push_cast; ring
    have h2 : K = 39 * n := by exact_mod_cast h1
    exact hK ⟨n, h2⟩
  constructor
  · rintro ⟨n, hn⟩
    cases l
    · exact (key _ (-13) (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ (-13) (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ (-13) (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ (-13) (by norm_num [twistExp]) (by decide) n hn).elim
    · rfl
    · exact (key _ 13 (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ 5 (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ 20 (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ (-7) (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ 2 (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ 8 (by norm_num [twistExp]) (by decide) n hn).elim
    · exact (key _ 11 (by norm_num [twistExp]) (by decide) n hn).elim
  · rintro rfl
    exact ⟨0, by norm_num [twistExp]⟩

/-- `γ = 0`: the actual six-current result in `dim U₁ = 6 + 13γ`. -/
theorem gamma_eq_zero (γ dimU1 : ℕ) (hEG : dimU1 = 6 + 13 * γ) (hsix : dimU1 = 6) :
    γ = 0 := by
  omega

/-- The largest lowest weight is `15/13`, which improves the preliminary `17/10`. -/
theorem lowestWeight_le (l : Label) : lowestWeight l ≤ 15 / 13 := by
  cases l <;> simp only [lowestWeight] <;> norm_num

theorem max_lowestWeight_lt : (15 / 13 : ℚ) < 17 / 10 ∧ (15 / 13 : ℚ) < 2 := by
  norm_num

/-- Corollary `cor:unmixed-lattice-restrictions`: the next possible top weights `4/3`
and `5/3` of the two unmixed lattice sectors exceed every lowest weight, so each such
sector is a single simple module. -/
theorem unmixed_next_tops (l : Label) :
    lowestWeight l < 1 / 3 + 1 ∧ lowestWeight l < 2 / 3 + 1 := by
  constructor <;> linarith [lowestWeight_le l]

/-- The only label of lowest weight `1/3` is `c₁`, with top dimension `3`; the only
label of lowest weight `2/3` is `c₂`, with top dimension `27`. -/
theorem unique_one_third (l : Label) : lowestWeight l = 1 / 3 ↔ l = .c1 := by
  cases l <;> simp [lowestWeight] <;> norm_num

theorem unique_two_thirds (l : Label) : lowestWeight l = 2 / 3 ↔ l = .c2 := by
  cases l <;> simp [lowestWeight] <;> norm_num

theorem topDim_c1 : topDim .c1 = 3 := rfl
theorem topDim_c2 : topDim .c2 = 27 := rfl

/-- Strict positivity of nonvacuum lowest weights (used for the CFT-type extension). -/
theorem lowestWeight_pos (l : Label) (hl : l ≠ .o) : 0 < lowestWeight l := by
  cases l <;> simp [lowestWeight] at hl ⊢ <;> norm_num


/-- **Corollary `cor:unmixed-lattice-restrictions`, counting step.**  Let a semisimple module
have finitely many simple summands, `n l` copies of the simple `l`, lowest weight `1/3` and top
dimension `3`, with all its weights in `1/3 + ℤ_{≥0}`.  Every summand's lowest weight is then a
weight `1/3 + j` of the module, and `j = 0` since all lowest weights are at most `15/13 < 4/3`;
so every summand is `c₁`, and the top dimension `3 = 3·n c₁` forces exactly one copy. -/
theorem unmixed_restriction (n : Label → ℕ)
    (hweights : ∀ l, 0 < n l → ∃ j : ℕ, lowestWeight l = 1 / 3 + j)
    (htop : (((allLabels.filter fun l => lowestWeight l = 1 / 3).map
      (fun l => n l * topDim l)).sum = 3)) :
    n .c1 = 1 ∧ ∀ l, l ≠ .c1 → n l = 0 := by
  have hsupp : ∀ l, 0 < n l → l = .c1 := by
    intro l hl
    obtain ⟨j, hj⟩ := hweights l hl
    have hle := lowestWeight_le l
    have hj0 : j = 0 := by
      by_contra h
      have : (1 : ℚ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      linarith
    subst hj0
    exact (unique_one_third l).1 (by simpa using hj)
  have hc1 : n .c1 = 1 := by
    have h := htop
    simp only [allLabels, List.filter, lowestWeight] at h
    norm_num at h
    simpa [topDim] using h
  refine ⟨hc1, fun l hl => ?_⟩
  by_contra h
  exact hl (hsupp l (Nat.pos_of_ne_zero h))

/-- The same for the pair labelled `(±1, 0)`: lowest weight `2/3`, top dimension `27`. -/
theorem unmixed_restriction_two (n : Label → ℕ)
    (hweights : ∀ l, 0 < n l → ∃ j : ℕ, lowestWeight l = 2 / 3 + j)
    (htop : (((allLabels.filter fun l => lowestWeight l = 2 / 3).map
      (fun l => n l * topDim l)).sum = 27)) :
    n .c2 = 1 ∧ ∀ l, l ≠ .c2 → n l = 0 := by
  have hsupp : ∀ l, 0 < n l → l = .c2 := by
    intro l hl
    obtain ⟨j, hj⟩ := hweights l hl
    have hle := lowestWeight_le l
    have hj0 : j = 0 := by
      by_contra h
      have : (1 : ℚ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      linarith
    subst hj0
    exact (unique_two_thirds l).1 (by simpa using hj)
  have hc2 : n .c2 = 1 := by
    have h := htop
    simp only [allLabels, List.filter, lowestWeight] at h
    norm_num at h
    simpa [topDim] using h
  refine ⟨hc2, fun l hl => ?_⟩
  by_contra h
  exact hl (hsupp l (Nat.pos_of_ne_zero h))

#print axioms pole_iff
#print axioms character_T_fixed_iff
#print axioms twist_list

end HaagerupIzumi.C8.Characters
