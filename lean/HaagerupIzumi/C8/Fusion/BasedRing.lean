module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite based rings (fusion rings)

This file sets up the based-ring (fusion-ring) language used in Appendix G of
`c8_expanded_20260929/haagerup_c8_expanded.tex` (lines 3241–4134): the
Grothendieck ring of a fusion category, recorded through its nonnegative integer
structure constants.

A `BasedRing ι` consists of a finite index set `ι` of simple objects, a unit
`𝟙`, an involutive duality `i ↦ i*`, and multiplicities `N i j l` (the
multiplicity of `l` in `i ⊗ j`) satisfying the unit laws, associativity and the
two Frobenius reciprocity identities `N_{ij}^l = N_{i* l}^j = N_{l j*}^i`.
These are theorems about every rigid semisimple tensor category (e.g. EGNO,
*Tensor categories*, §§3.1, 4.9); no categorical statement is proved here.

We derive rigidity `N_{ij}^𝟙 = δ_{j,i*}` (`N_unit_right`), `𝟙* = 𝟙`,
`N_{ij}^l = N_{j* i*}^{l*}` (`N_dual`), the fact that every product is nonzero
(`exists_N_ne_zero`), and a small calculus of invertible simples: if
`g ⊗ g* = 𝟙` then also `g* ⊗ g = 𝟙` (`IsInvertible.N_dual_left`), and
`g ⊗ x`, `x ⊗ g` are simple for every simple `x`.  Left and right
multiplication by an invertible simple are recorded as permutations `lmul g`,
`rmul · g` of `ι`, with transport rules such as
`N_{(g x) y}^l = N_{x y}^{g* l}`.

Characters (`IsCharacter`) are unital multiplicative functions on the basis;
they are exactly the algebra homomorphisms from the scalar-extended fusion
algebra to the coefficient ring.  The fusion product on coefficient vectors is
`BasedRing.mul`.
-/

namespace HaagerupIzumi.C8.Fusion

open Finset

/-- A finite based ring with nonnegative integer structure constants: the
Grothendieck ring of a fusion category.  `N i j l` is the multiplicity of the
simple `l` in `i ⊗ j`. -/
structure BasedRing (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The unit object `𝟙`. -/
  unit : ι
  /-- The duality `i ↦ i*`. -/
  dual : ι → ι
  /-- Fusion multiplicities: `N i j l` is the multiplicity of `l` in `i ⊗ j`. -/
  N : ι → ι → ι → ℕ
  dual_dual : ∀ i, dual (dual i) = i
  unit_mul : ∀ j l, N unit j l = if l = j then 1 else 0
  mul_unit : ∀ i l, N i unit l = if l = i then 1 else 0
  /-- Associativity: `(i ⊗ j) ⊗ k ≅ i ⊗ (j ⊗ k)`. -/
  assoc : ∀ i j k l, ∑ m, N i j m * N m k l = ∑ m, N j k m * N i m l
  /-- Frobenius reciprocity: `N_{ij}^l = N_{i* l}^j`. -/
  frob_left : ∀ i j l, N i j l = N (dual i) l j
  /-- Frobenius reciprocity: `N_{ij}^l = N_{l j*}^i`. -/
  frob_right : ∀ i j l, N i j l = N l (dual j) i

namespace BasedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (R : BasedRing ι)

/-! ### Elementary consequences of the axioms -/

/-- Rigidity: `𝟙` occurs in `i ⊗ j` exactly once if `j = i*`, and otherwise not. -/
theorem N_unit_right (i j : ι) : R.N i j R.unit = if j = R.dual i then 1 else 0 := by
  rw [R.frob_left, R.mul_unit]

theorem dual_unit : R.dual R.unit = R.unit := by
  have h := R.N_unit_right R.unit R.unit
  rw [R.unit_mul, if_pos rfl] at h
  by_contra hne
  rw [if_neg (fun h' => hne h'.symm)] at h
  exact one_ne_zero h

theorem dual_injective : Function.Injective R.dual := fun i j h => by
  rw [← R.dual_dual i, h, R.dual_dual]

/-- Duality reverses products: `N_{ij}^l = N_{j* i*}^{l*}`. -/
theorem N_dual (i j l : ι) : R.N i j l = R.N (R.dual j) (R.dual i) (R.dual l) := by
  rw [R.frob_right i j l, R.frob_left l (R.dual j) i, R.frob_right (R.dual l) i (R.dual j)]

theorem sum_ite_mul (y : ι) (f : ι → ℕ) : ∑ m, (if m = y then 1 else 0) * f m = f y := by
  simp

theorem sum_mul_ite (y : ι) (f : ι → ℕ) : ∑ m, f m * (if m = y then 1 else 0) = f y := by
  simp

/-- Every fusion product of two simples is nonzero. -/
theorem exists_N_ne_zero (i j : ι) : ∃ l, R.N i j l ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := R.assoc (R.dual i) i j j
  have hR : ∑ m, R.N i j m * R.N (R.dual i) m j = 0 := by simp [hcon]
  have hterm : R.N (R.dual i) i R.unit * R.N R.unit j j = 1 := by
    rw [R.N_unit_right, R.dual_dual, R.unit_mul]
    simp
  have hL : 1 ≤ ∑ m, R.N (R.dual i) i m * R.N m j j :=
    calc 1 = R.N (R.dual i) i R.unit * R.N R.unit j j := hterm.symm
      _ ≤ ∑ m, R.N (R.dual i) i m * R.N m j j :=
        Finset.single_le_sum (f := fun m => R.N (R.dual i) i m * R.N m j j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  rw [h, hR] at hL
  exact absurd hL (by norm_num)

/-! ### Characters and the fusion product -/

/-- A character of the based ring with values in `K`: a unital multiplicative
function on the basis.  These are exactly the `K`-algebra homomorphisms from
`K ⊗ ℤ[ι]` to `K`. -/
structure IsCharacter {K : Type*} [CommSemiring K] (χ : ι → K) : Prop where
  map_unit : χ R.unit = 1
  map_mul : ∀ i j, χ i * χ j = ∑ l, (R.N i j l : K) * χ l

theorem IsCharacter.map {K L : Type*} [CommSemiring K] [CommSemiring L] {χ : ι → K}
    {R : BasedRing ι} (h : R.IsCharacter χ) (f : K →+* L) :
    R.IsCharacter (fun i => f (χ i)) := by
  refine ⟨by simp [h.map_unit], fun i j => ?_⟩
  have := congrArg f (h.map_mul i j)
  simpa [map_mul, map_sum, map_natCast] using this

/-- The fusion product of coefficient vectors: `(x y)_l = ∑ x_i y_j N_{ij}^l`. -/
def mul {K : Type*} [CommSemiring K] (x y : ι → K) : ι → K :=
  fun l => ∑ i, ∑ j, x i * y j * (R.N i j l : K)

theorem mul_single_single {K : Type*} [CommSemiring K] (i j l : ι) :
    R.mul (Pi.single i (1 : K)) (Pi.single j 1) l = (R.N i j l : K) := by
  simp [mul, Pi.single_apply]

/-! ### Invertible simples -/

/-- The simple `g` is invertible: `g ⊗ g* ≅ 𝟙`. -/
def IsInvertible (g : ι) : Prop := ∀ l, R.N g (R.dual g) l = if l = R.unit then 1 else 0

/-- A function `ι → ℕ` with `∑ f² = 1` is a Kronecker delta. -/
theorem exists_single_of_sum_mul_self {f : ι → ℕ} (h : ∑ l, f l * f l = 1) :
    ∃ y, ∀ l, f l = if l = y then 1 else 0 := by
  have hne : ∑ l, f l * f l ≠ 0 := by rw [h]; exact one_ne_zero
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hle : ∀ l, f l * f l ≤ 1 := fun l => by
    rw [← h]
    exact Finset.single_le_sum (f := fun l => f l * f l) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ l)
  refine ⟨y, fun l => ?_⟩
  by_cases hl : l = y
  · rw [if_pos hl, hl]
    have h0 : f y ≠ 0 := fun h0 => hy (by simp [h0])
    have h1 : f y ≤ 1 := by nlinarith [hle y, Nat.pos_of_ne_zero h0]
    omega
  · rw [if_neg hl]
    have hpair : ∑ x ∈ ({l, y} : Finset ι), f x * f x ≤ ∑ x, f x * f x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hl, h] at hpair
    have hy1 : 1 ≤ f y * f y := Nat.one_le_iff_ne_zero.mpr hy
    have h2 : f l * f l = 0 := by omega
    exact mul_self_eq_zero.mp h2

/-- If `g* ⊗ g = 𝟙`, then `g ⊗ x` is simple for every simple `x`. -/
theorem exists_single_left {g : ι}
    (hg : ∀ l, R.N (R.dual g) g l = if l = R.unit then 1 else 0) (x : ι) :
    ∃ y, ∀ l, R.N g x l = if l = y then 1 else 0 := by
  refine exists_single_of_sum_mul_self (f := R.N g x) ?_
  have h := R.assoc (R.dual g) g x x
  have h1 : ∑ m, R.N (R.dual g) g m * R.N m x x = 1 := by
    simp only [hg]
    rw [sum_ite_mul, R.unit_mul, if_pos rfl]
  rw [h1] at h
  refine (Finset.sum_congr rfl (fun m _ => ?_)).trans h.symm
  rw [← R.frob_left]

/-- If `g ⊗ g* = 𝟙`, then `x ⊗ g` is simple for every simple `x`. -/
theorem exists_single_right {g : ι}
    (hg : ∀ l, R.N g (R.dual g) l = if l = R.unit then 1 else 0) (x : ι) :
    ∃ y, ∀ l, R.N x g l = if l = y then 1 else 0 := by
  refine exists_single_of_sum_mul_self (f := R.N x g) ?_
  have h := R.assoc x g (R.dual g) x
  have h1 : ∑ m, R.N g (R.dual g) m * R.N x m x = 1 := by
    simp only [hg]
    rw [sum_ite_mul, R.mul_unit, if_pos rfl]
  rw [h1] at h
  refine (Finset.sum_congr rfl (fun m _ => ?_)).trans h
  rw [← R.frob_right]

/-- The simple constituent of `g ⊗ x` (meaningful when `g` is invertible). -/
noncomputable def lmul (g x : ι) : ι :=
  @Classical.epsilon ι ⟨x⟩ fun y => ∀ l, R.N g x l = if l = y then 1 else 0

/-- The simple constituent of `x ⊗ g` (meaningful when `g` is invertible). -/
noncomputable def rmul (x g : ι) : ι :=
  @Classical.epsilon ι ⟨x⟩ fun y => ∀ l, R.N x g l = if l = y then 1 else 0

theorem N_lmul_of {g x : ι} (h : ∃ y, ∀ l, R.N g x l = if l = y then 1 else 0) (l : ι) :
    R.N g x l = if l = R.lmul g x then 1 else 0 :=
  Classical.epsilon_spec h l

theorem N_rmul_of {g x : ι} (h : ∃ y, ∀ l, R.N x g l = if l = y then 1 else 0) (l : ι) :
    R.N x g l = if l = R.rmul x g then 1 else 0 :=
  Classical.epsilon_spec h l

theorem isInvertible_unit : R.IsInvertible R.unit := by
  intro l
  rw [R.dual_unit, R.unit_mul]

section Invertible

variable {R}

/-- If `g ⊗ g* = 𝟙` then `g* ⊗ g = 𝟙`. -/
theorem IsInvertible.N_dual_left {g : ι} (hg : R.IsInvertible g) (l : ι) :
    R.N (R.dual g) g l = if l = R.unit then 1 else 0 := by
  have hg' : ∀ l, R.N g (R.dual g) l = if l = R.unit then 1 else 0 := hg
  have hsum : ∑ m, R.N (R.dual g) g m * R.N (R.dual g) g m = 1 := by
    have h := R.assoc g (R.dual g) g g
    have hL : ∑ m, R.N g (R.dual g) m * R.N m g g = 1 := by
      simp only [hg']
      rw [sum_ite_mul, R.unit_mul, if_pos rfl]
    rw [hL] at h
    exact (Finset.sum_congr rfl
      (fun m _ => by rw [R.frob_left (R.dual g) g m, R.dual_dual])).trans h.symm
  obtain ⟨y, hy⟩ := exists_single_of_sum_mul_self hsum
  have h1 : R.N (R.dual g) g R.unit = 1 := by
    rw [R.N_unit_right, R.dual_dual, if_pos rfl]
  have hyu : y = R.unit := by
    by_contra hne
    rw [hy, if_neg (Ne.symm hne)] at h1
    exact zero_ne_one h1
  rw [hy l, hyu]

theorem IsInvertible.dual {g : ι} (hg : R.IsInvertible g) : R.IsInvertible (R.dual g) := by
  intro l
  rw [R.dual_dual]
  exact hg.N_dual_left l

theorem IsInvertible.N_lmul {g : ι} (hg : R.IsInvertible g) (x l : ι) :
    R.N g x l = if l = R.lmul g x then 1 else 0 :=
  R.N_lmul_of (R.exists_single_left hg.N_dual_left x) l

theorem IsInvertible.N_rmul {g : ι} (hg : R.IsInvertible g) (x l : ι) :
    R.N x g l = if l = R.rmul x g then 1 else 0 :=
  R.N_rmul_of (R.exists_single_right hg x) l

theorem IsInvertible.lmul_eq {g x y : ι} (hg : R.IsInvertible g) (h : R.N g x y ≠ 0) :
    R.lmul g x = y := by
  rw [hg.N_lmul] at h
  by_contra hne
  exact h (if_neg (Ne.symm hne))

theorem IsInvertible.rmul_eq {g x y : ι} (hg : R.IsInvertible g) (h : R.N x g y ≠ 0) :
    R.rmul x g = y := by
  rw [hg.N_rmul] at h
  by_contra hne
  exact h (if_neg (Ne.symm hne))

theorem IsInvertible.lmul_unit {g : ι} (hg : R.IsInvertible g) : R.lmul g R.unit = g :=
  hg.lmul_eq (by rw [R.mul_unit, if_pos rfl]; exact one_ne_zero)

theorem IsInvertible.rmul_unit_left {g : ι} (hg : R.IsInvertible g) : R.rmul R.unit g = g :=
  hg.rmul_eq (by rw [R.unit_mul, if_pos rfl]; exact one_ne_zero)

/-- `N_{ij}^g = δ_{j, i* g}` for invertible `g`. -/
theorem IsInvertible.N_right_obj {g : ι} (hg : R.IsInvertible g) (x y : ι) :
    R.N x y g = if y = R.rmul (R.dual x) g then 1 else 0 := by
  rw [R.frob_left, hg.N_rmul]

theorem IsInvertible.lmul_dual_lmul {g : ι} (hg : R.IsInvertible g) (x : ι) :
    R.lmul (R.dual g) (R.lmul g x) = x :=
  hg.dual.lmul_eq (by rw [← R.frob_left, hg.N_lmul, if_pos rfl]; exact one_ne_zero)

theorem IsInvertible.lmul_lmul_dual {g : ι} (hg : R.IsInvertible g) (x : ι) :
    R.lmul g (R.lmul (R.dual g) x) = x := by
  have h := hg.dual.lmul_dual_lmul x
  rwa [R.dual_dual] at h

theorem IsInvertible.rmul_rmul_dual {g : ι} (hg : R.IsInvertible g) (x : ι) :
    R.rmul (R.rmul x g) (R.dual g) = x :=
  hg.dual.rmul_eq (by rw [← R.frob_right, hg.N_rmul, if_pos rfl]; exact one_ne_zero)

theorem IsInvertible.rmul_dual_rmul {g : ι} (hg : R.IsInvertible g) (x : ι) :
    R.rmul (R.rmul x (R.dual g)) g = x := by
  have h := hg.dual.rmul_rmul_dual x
  rwa [R.dual_dual] at h

theorem IsInvertible.eq_lmul_iff {g l m : ι} (hg : R.IsInvertible g) :
    l = R.lmul g m ↔ m = R.lmul (R.dual g) l := by
  constructor
  · rintro rfl; exact (hg.lmul_dual_lmul m).symm
  · rintro rfl; exact (hg.lmul_lmul_dual l).symm

theorem IsInvertible.eq_rmul_iff {g l m : ι} (hg : R.IsInvertible g) :
    l = R.rmul m g ↔ m = R.rmul l (R.dual g) := by
  constructor
  · rintro rfl; exact (hg.rmul_rmul_dual m).symm
  · rintro rfl; exact (hg.rmul_dual_rmul l).symm

/-- Transport: `N_{(g x) y}^l = N_{x y}^{g* l}`. -/
theorem IsInvertible.N_lmul_left {g : ι} (hg : R.IsInvertible g) (x y l : ι) :
    R.N (R.lmul g x) y l = R.N x y (R.lmul (R.dual g) l) := by
  have h := R.assoc g x y l
  have hL : ∑ m, R.N g x m * R.N m y l = R.N (R.lmul g x) y l := by
    simp only [hg.N_lmul x]
    exact sum_ite_mul _ _
  have hR : ∑ m, R.N x y m * R.N g m l = R.N x y (R.lmul (R.dual g) l) := by
    have e : ∀ m, R.N g m l = if m = R.lmul (R.dual g) l then 1 else 0 := fun m => by
      rw [hg.N_lmul]
      exact if_congr hg.eq_lmul_iff rfl rfl
    simp only [e]
    exact sum_mul_ite _ _
  rw [← hL, h, hR]

/-- Transport: `N_{x (y g)}^l = N_{x y}^{l g*}`. -/
theorem IsInvertible.N_rmul_right {g : ι} (hg : R.IsInvertible g) (x y l : ι) :
    R.N x (R.rmul y g) l = R.N x y (R.rmul l (R.dual g)) := by
  have h := R.assoc x y g l
  have hR : ∑ m, R.N y g m * R.N x m l = R.N x (R.rmul y g) l := by
    simp only [hg.N_rmul y]
    exact sum_ite_mul _ _
  have hL : ∑ m, R.N x y m * R.N m g l = R.N x y (R.rmul l (R.dual g)) := by
    have e : ∀ m, R.N m g l = if m = R.rmul l (R.dual g) then 1 else 0 := fun m => by
      rw [hg.N_rmul]
      exact if_congr hg.eq_rmul_iff rfl rfl
    simp only [e]
    exact sum_mul_ite _ _
  rw [← hR, ← h, hL]

/-- Transport: `N_{x (g y)}^l = N_{(x g) y}^l`. -/
theorem IsInvertible.N_lmul_right {g : ι} (hg : R.IsInvertible g) (x y l : ι) :
    R.N x (R.lmul g y) l = R.N (R.rmul x g) y l := by
  have h := R.assoc x g y l
  have hL : ∑ m, R.N x g m * R.N m y l = R.N (R.rmul x g) y l := by
    simp only [hg.N_rmul x]
    exact sum_ite_mul _ _
  have hR : ∑ m, R.N g y m * R.N x m l = R.N x (R.lmul g y) l := by
    simp only [hg.N_lmul y]
    exact sum_ite_mul _ _
  rw [← hR, ← h, hL]

/-- Left and right multiplications by invertibles commute: `(g x) h = g (x h)`. -/
theorem IsInvertible.rmul_lmul {g h : ι} (hg : R.IsInvertible g) (hh : R.IsInvertible h)
    (x : ι) : R.rmul (R.lmul g x) h = R.lmul g (R.rmul x h) :=
  hh.rmul_eq (by
    rw [hg.N_lmul_left, hg.lmul_dual_lmul, hh.N_rmul, if_pos rfl]
    exact one_ne_zero)

/-- `(g x)* = x* g*`. -/
theorem IsInvertible.dual_lmul {g : ι} (hg : R.IsInvertible g) (x : ι) :
    R.dual (R.lmul g x) = R.rmul (R.dual x) (R.dual g) := by
  symm
  apply hg.dual.rmul_eq
  rw [← R.N_dual, hg.N_lmul, if_pos rfl]
  exact one_ne_zero

/-- `(x g)* = g* x*`. -/
theorem IsInvertible.dual_rmul {g : ι} (hg : R.IsInvertible g) (x : ι) :
    R.dual (R.rmul x g) = R.lmul (R.dual g) (R.dual x) := by
  symm
  apply hg.dual.lmul_eq
  rw [← R.N_dual, hg.N_rmul, if_pos rfl]
  exact one_ne_zero

/-- `g (h x) = (g h) x` for invertible `g, h` with `g ⊗ h = k`. -/
theorem IsInvertible.lmul_lmul {g h k : ι} (hg : R.IsInvertible g) (hh : R.IsInvertible h)
    (hk : R.IsInvertible k) (hgh : R.lmul g h = k) (x : ι) :
    R.lmul g (R.lmul h x) = R.lmul k x := by
  symm
  apply hk.lmul_eq
  rw [← hgh, hg.N_lmul_left, hg.lmul_dual_lmul, hh.N_lmul, if_pos rfl]
  exact one_ne_zero

/-- `(x g) h = x (g h)` for invertible `g, h` with `g ⊗ h = k`. -/
theorem IsInvertible.rmul_rmul {g h k : ι} (hg : R.IsInvertible g) (hh : R.IsInvertible h)
    (hk : R.IsInvertible k) (hgh : R.lmul g h = k) (x : ι) :
    R.rmul (R.rmul x g) h = R.rmul x k := by
  symm
  apply hk.rmul_eq
  rw [← hgh, hg.N_lmul_right, hh.N_rmul, if_pos rfl]
  exact one_ne_zero

/-- For a character and an invertible `g`: `χ(g) χ(x) = χ(g x)`. -/
theorem IsCharacter.map_lmul {K : Type*} [CommSemiring K] {χ : ι → K}
    (hχ : R.IsCharacter χ) {g : ι} (hg : R.IsInvertible g) (x : ι) :
    χ g * χ x = χ (R.lmul g x) := by
  rw [hχ.map_mul, Fintype.sum_eq_single (R.lmul g x)]
  · rw [hg.N_lmul, if_pos rfl, Nat.cast_one, one_mul]
  · intro l hl
    rw [hg.N_lmul, if_neg hl, Nat.cast_zero, zero_mul]

end Invertible

end BasedRing

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.BasedRing.N_dual
#print axioms HaagerupIzumi.C8.Fusion.BasedRing.exists_N_ne_zero
#print axioms HaagerupIzumi.C8.Fusion.BasedRing.IsInvertible.N_dual_left
#print axioms HaagerupIzumi.C8.Fusion.BasedRing.IsInvertible.N_lmul_left
#print axioms HaagerupIzumi.C8.Fusion.BasedRing.IsInvertible.rmul_rmul
