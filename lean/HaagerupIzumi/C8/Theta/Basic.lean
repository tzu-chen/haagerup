module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Theta coefficients of positive rank-four lattices by exact enumeration

Infrastructure for the theta-coefficient tables in the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3777 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`); the tables themselves are in
`HaagerupIzumi.C8.Theta.NearGroup`.

## Conventions (fixed here, documented because the manuscript leaves them implicit)

* A lattice `L` is `ℤ⁴` with an integral Gram matrix `G`; rational coordinate
  vectors `x : Fin 4 → ℚ` (coordinates in the lattice basis) represent `L ⊗ ℚ`,
  with `(x, y) = ∑ᵢⱼ xᵢ Gᵢⱼ yⱼ` (`gramBil`) and norm `(x, x)` (`gramNorm`).
* The `q`-exponent of `x` in a theta series is its *energy* `(x, x)/2`
  (`energy`); e.g. a root has energy `1`.
* A coset `g + L` is given by a rational shift `g`; its points are
  `cosetPt g n = g + n`, `n ∈ ℤ⁴`.  The *shell* of energy `e` is
  `{n | (g + n, g + n)/2 = e}` (`shell`).
* `thetaCoeff G g H e = ∑_{x ∈ g + L, (x,x)/2 = e} H(x)` is the coefficient of
  `q^e` in `Θ_{H, g+L} = ∑_{x ∈ g+L} H(x) q^{(x,x)/2}` (a `finsum`; all shells
  used are proved finite and listed explicitly).  `thetaCount` is the case
  `H = 1`.
* `minusSixD2Coeff θ e` is the coefficient of `q^e` in `-6 D₂ Θ`, with the
  modular derivative `D₂ = q d/dq - E₂/6` and `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`
  (`e2Coeff`); i.e. `-6 e θ(e) + ∑_{0 ≤ j ≤ e} E₂[j] θ(e - j)`.  The
  truncation `j ≤ ⌊e⌋` is exact because theta coefficients of a positive
  lattice vanish at negative exponents.

## Method

`shell_eq_of_box`: if every coordinate satisfies `xᵢ² ≤ Cᵢ (x, x)` (proved
for each lattice from positivity, `Cᵢ = (G⁻¹)ᵢᵢ`, see `coord_*`), then a point
of energy `e` has `(gᵢ + nᵢ)² ≤ 2 Cᵢ e`, which confines `n` to an explicit
integer box (`int_bound`); inside the box the shell is identified with an
explicit list by kernel evaluation (`decide +kernel`, no extra axioms).

Nothing here is an external hypothesis: all statements are proved.
-/

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Lattice cosets, shells, theta coefficients -/

/-- The bilinear form `(x, y) = ∑ᵢ ∑ⱼ xᵢ Gᵢⱼ yⱼ` of an integral Gram matrix. -/
def gramBil (G : Matrix (Fin 4) (Fin 4) ℤ) (x y : Fin 4 → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * (G i j : ℚ) * y j

/-- The norm `(x, x)`. -/
def gramNorm (G : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℚ) : ℚ := gramBil G x x

/-- The energy `(x, x)/2`, i.e. the `q`-exponent of `x` in a theta series. -/
def energy (G : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℚ) : ℚ := gramNorm G x / 2

/-- The standard basis vector `eᵢ` (a lattice basis vector). -/
def basisVec (i : Fin 4) : Fin 4 → ℚ := fun j => if j = i then 1 else 0

/-- The point `g + n` of the coset `g + L`. -/
def cosetPt (g : Fin 4 → ℚ) (n : Fin 4 → ℤ) : Fin 4 → ℚ := fun i => g i + (n i : ℚ)

/-- The shell of energy `e` in the coset `g + L`, parametrized by `n ∈ ℤ⁴`
(`n ↦ g + n` is a bijection onto the coset). -/
def shell (G : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (e : ℚ) : Set (Fin 4 → ℤ) :=
  {n | energy G (cosetPt g n) = e}

/-- `[q^e] Θ_{H, g+L} = ∑_{x ∈ g + L, (x,x)/2 = e} H(x)`. -/
noncomputable def thetaCoeff (G : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ)
    (H : (Fin 4 → ℚ) → ℚ) (e : ℚ) : ℚ :=
  ∑ᶠ n ∈ shell G g e, H (cosetPt g n)

/-- `[q^e] Θ_{g+L}`: the number of vectors of energy `e` in `g + L`. -/
noncomputable def thetaCount (G : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (e : ℚ) : ℚ :=
  thetaCoeff G g (fun _ => 1) e

/-- A shell identified with an explicit duplicate-free list gives the theta
coefficient as a list sum. -/
theorem thetaCoeff_eq_list_sum {G : Matrix (Fin 4) (Fin 4) ℤ} {g : Fin 4 → ℚ}
    {H : (Fin 4 → ℚ) → ℚ} {e : ℚ} {L : List (Fin 4 → ℤ)}
    (hs : shell G g e = {n | n ∈ L}) (hL : L.Nodup) :
    thetaCoeff G g H e = (L.map fun n => H (cosetPt g n)).sum := by
  unfold thetaCoeff
  rw [hs, ← List.coe_toFinset, finsum_mem_coe_finset, List.sum_toFinset _ hL]

/-! ## Confining a shell to an integer box -/

/-- If `(g + n)² ≤ K` and the integers just outside `[lo, hi]` violate the
bound, then `n ∈ [lo, hi]`. -/
theorem int_bound {g K : ℚ} {lo hi n : ℤ}
    (h1 : 0 < g + ((hi + 1 : ℤ) : ℚ)) (h2 : K < (g + ((hi + 1 : ℤ) : ℚ)) ^ 2)
    (h3 : g + ((lo - 1 : ℤ) : ℚ) < 0) (h4 : K < (g + ((lo - 1 : ℤ) : ℚ)) ^ 2)
    (hn : (g + (n : ℚ)) ^ 2 ≤ K) : lo ≤ n ∧ n ≤ hi := by
  constructor
  · by_contra hlt
    have hle : n ≤ lo - 1 := by omega
    have hq : (n : ℚ) ≤ ((lo - 1 : ℤ) : ℚ) := by exact_mod_cast hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (neg_nonneg.mpr h3.le),
      sq_nonneg (((lo - 1 : ℤ) : ℚ) - (n : ℚ))]
  · by_contra hlt
    have hle : hi + 1 ≤ n := by omega
    have hq : ((hi + 1 : ℤ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) h1.le,
      sq_nonneg ((n : ℚ) - ((hi + 1 : ℤ) : ℚ))]

/-- The integers `lo, lo + 1, …, hi` (empty if `hi < lo`). -/
def zRange (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun k : ℕ => lo + (k : ℤ)

theorem mem_zRange {lo hi n : ℤ} (h1 : lo ≤ n) (h2 : n ≤ hi) : n ∈ zRange lo hi := by
  unfold zRange
  rw [List.mem_map]
  exact ⟨(n - lo).toNat, List.mem_range.mpr (by omega), by omega⟩

/-- The integer box `∏ᵢ [loᵢ, hiᵢ]` as an explicit list. -/
def boxList (lo hi : Fin 4 → ℤ) : List (Fin 4 → ℤ) :=
  (zRange (lo 0) (hi 0)).flatMap fun a =>
    (zRange (lo 1) (hi 1)).flatMap fun b =>
      (zRange (lo 2) (hi 2)).flatMap fun c =>
        (zRange (lo 3) (hi 3)).map fun d => ![a, b, c, d]

theorem mem_boxList {lo hi n : Fin 4 → ℤ} (h : ∀ i, lo i ≤ n i ∧ n i ≤ hi i) :
    n ∈ boxList lo hi := by
  have hn : n = ![n 0, n 1, n 2, n 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hn]
  simp only [boxList, List.mem_flatMap, List.mem_map]
  exact ⟨n 0, mem_zRange (h 0).1 (h 0).2, n 1, mem_zRange (h 1).1 (h 1).2,
    n 2, mem_zRange (h 2).1 (h 2).2, n 3, mem_zRange (h 3).1 (h 3).2, rfl⟩

/-- **Shell identification.**  Given coordinate bounds `xᵢ² ≤ Cᵢ (x, x)`, an
integer box whose outside neighbours violate `(gᵢ + nᵢ)² ≤ 2 Cᵢ e`, and an
explicit list `L` that agrees with the shell inside the box (both checked by
kernel evaluation at the use sites), the shell is exactly `L`. -/
theorem shell_eq_of_box {G : Matrix (Fin 4) (Fin 4) ℤ} {g : Fin 4 → ℚ} {e : ℚ}
    {C : Fin 4 → ℚ} (hC : ∀ (x : Fin 4 → ℚ) (i : Fin 4), x i ^ 2 ≤ C i * gramNorm G x)
    (lo hi : Fin 4 → ℤ)
    (hbox : ∀ i : Fin 4, 0 < g i + ((hi i + 1 : ℤ) : ℚ) ∧
      C i * (2 * e) < (g i + ((hi i + 1 : ℤ) : ℚ)) ^ 2 ∧
      g i + ((lo i - 1 : ℤ) : ℚ) < 0 ∧
      C i * (2 * e) < (g i + ((lo i - 1 : ℤ) : ℚ)) ^ 2)
    (L : List (Fin 4 → ℤ))
    (hcheck : ∀ n ∈ boxList lo hi, energy G (cosetPt g n) = e → n ∈ L)
    (hmem : ∀ n ∈ L, energy G (cosetPt g n) = e) :
    shell G g e = {n | n ∈ L} := by
  ext n
  simp only [shell, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine hcheck n (mem_boxList fun i => ?_) h
    have hN : gramNorm G (cosetPt g n) = 2 * e := by
      unfold energy at h
      linarith
    have hx : (g i + (n i : ℚ)) ^ 2 ≤ C i * (2 * e) := by
      have := hC (cosetPt g n) i
      rw [hN] at this
      exact this
    obtain ⟨h1, h2, h3, h4⟩ := hbox i
    exact int_bound h1 h2 h3 h4 hx
  · exact hmem n

/-! ## The modular derivative `-6 D₂` on coefficients -/

/-- Coefficients of `E₂ = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ`. -/
def e2Coeff (n : ℕ) : ℚ := if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℚ)

/-- `[q^e] (-6 D₂ Θ)` for `D₂ = q d/dq - E₂/6`, from the coefficients `θ` of `Θ`:
`-6 e θ(e) + ∑_{0 ≤ j ≤ e} E₂[j] θ(e - j)` (`θ` vanishes at negative exponents). -/
noncomputable def minusSixD2Coeff (θ : ℚ → ℚ) (e : ℚ) : ℚ :=
  -6 * e * θ e + ∑ j ∈ Finset.range (⌊e⌋₊ + 1), e2Coeff j * θ (e - j)

theorem e2Coeff_zero : e2Coeff 0 = 1 := by
  simp [e2Coeff]

theorem e2Coeff_one : e2Coeff 1 = -24 := by
  simp [e2Coeff]

theorem minusSixD2Coeff_of_lt_one (θ : ℚ → ℚ) {e : ℚ} (h1 : e < 1) :
    minusSixD2Coeff θ e = (1 - 6 * e) * θ e := by
  rw [minusSixD2Coeff, Nat.floor_eq_zero.mpr h1, zero_add, Finset.sum_range_one, e2Coeff_zero]
  simp only [Nat.cast_zero, sub_zero]
  ring

theorem minusSixD2Coeff_one (θ : ℚ → ℚ) :
    minusSixD2Coeff θ 1 = -5 * θ 1 - 24 * θ 0 := by
  rw [minusSixD2Coeff, Nat.floor_one, Finset.sum_range_succ, Finset.sum_range_one,
    e2Coeff_zero, e2Coeff_one]
  simp only [Nat.cast_zero, Nat.cast_one, sub_zero, sub_self]
  ring

/-! ## Projections used by the tables -/

/-- Orthogonal projection of `x` onto the line `ℚ z`. -/
def projLine (G : Matrix (Fin 4) (Fin 4) ℤ) (z x : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun i => gramBil G x z / gramNorm G z * z i

/-- `‖x - x_z‖² - 3 ‖x_z‖²`, with `x_z` the projection to `ℚ z`.  When `z ⊥ A₃`
and `A₃ ⊗ ℚ = z^⊥`, this is `‖x_{A₃}‖² - 3 ‖x_{A₃^⊥}‖²`. -/
def harmA3 (G : Matrix (Fin 4) (Fin 4) ℤ) (z x : Fin 4 → ℚ) : ℚ :=
  gramNorm G (fun i => x i - projLine G z x i) - 3 * gramNorm G (projLine G z x)

/-- Projection to functions even separately in `r` and `s`: the average over
the four sign changes `(±r, ±s)`. -/
def sepEven (f : ℤ → ℤ → ℚ) (r s : ℤ) : ℚ := (f r s + f (-r) s + f r (-s) + f (-r) (-s)) / 4

theorem sepEven_zero (f : ℤ → ℤ → ℚ) : sepEven f 0 0 = f 0 0 := by
  simp only [sepEven, neg_zero]
  ring

/-- Projection to even functions on `L*/L`: the average over `x ↦ -x`. -/
def avgNeg (f : (Fin 4 → ℚ) → ℚ) (g : Fin 4 → ℚ) : ℚ := (f g + f (-g)) / 2

/-! ## The four Gram matrices of the proof -/

/-- `L₇ ⊕ A₂` (line 3646): basis `u, v` of `L₇` with Gram `[[2,1],[1,4]]`,
then the simple roots `α₁, α₂` of `A₂`. -/
def gramL7A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 1, 0, 0; 1, 4, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2]

/-- `G₇⁻` (line 3686). -/
def gramG7m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 6]

/-- `A₁ ⊕ A₁ ⊕ A₂` (line 3720): simple roots of the two `A₁`, then of `A₂`. -/
def gramA1A1A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2]

/-- `G₆⁻` (line 3749), basis `a, b, c, e`. -/
def gramG6m : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, -1, -1; -1, 2, 0, 0; -1, 0, 2, 0; -1, 0, 0, 4]

theorem gramNorm_L7A2 (x : Fin 4 → ℚ) : gramNorm gramL7A2 x =
    2 * x 0 ^ 2 + 2 * x 0 * x 1 + 4 * x 1 ^ 2 + 2 * x 2 ^ 2 - 2 * x 2 * x 3 + 2 * x 3 ^ 2 := by
  simp only [gramNorm, gramBil, Fin.sum_univ_four]
  simp [gramL7A2]
  ring1

theorem gramNorm_G7m (x : Fin 4 → ℚ) : gramNorm gramG7m x =
    2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 - 2 * x 1 * x 2 + 2 * x 2 ^ 2
      - 2 * x 2 * x 3 + 6 * x 3 ^ 2 := by
  simp only [gramNorm, gramBil, Fin.sum_univ_four]
  simp [gramG7m]
  ring1

theorem gramNorm_A1A1A2 (x : Fin 4 → ℚ) : gramNorm gramA1A1A2 x =
    2 * x 0 ^ 2 + 2 * x 1 ^ 2 + 2 * x 2 ^ 2 - 2 * x 2 * x 3 + 2 * x 3 ^ 2 := by
  simp only [gramNorm, gramBil, Fin.sum_univ_four]
  simp [gramA1A1A2]
  ring1

theorem gramNorm_G6m (x : Fin 4 → ℚ) : gramNorm gramG6m x =
    2 * x 0 ^ 2 + 2 * x 1 ^ 2 + 2 * x 2 ^ 2 + 4 * x 3 ^ 2
      - 2 * x 0 * x 1 - 2 * x 0 * x 2 - 2 * x 0 * x 3 := by
  simp only [gramNorm, gramBil, Fin.sum_univ_four]
  simp [gramG6m]
  ring1

/-! ### Positivity (explicit sums of squares) -/

theorem psd_L7A2 (a b c d : ℚ) :
    0 ≤ 2 * a ^ 2 + 2 * a * b + 4 * b ^ 2 + 2 * c ^ 2 - 2 * c * d + 2 * d ^ 2 := by
  nlinarith [sq_nonneg (2 * a + b), sq_nonneg b, sq_nonneg (2 * c - d), sq_nonneg d]

theorem psd_G7m (a b c d : ℚ) :
    0 ≤ 2 * a ^ 2 - 2 * a * b + 2 * b ^ 2 - 2 * b * c + 2 * c ^ 2 - 2 * c * d + 6 * d ^ 2 := by
  nlinarith [sq_nonneg a, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg d]

theorem psd_A1A1A2 (a b c d : ℚ) :
    0 ≤ 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 - 2 * c * d + 2 * d ^ 2 := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (2 * c - d), sq_nonneg d]

theorem psd_G6m (a b c d : ℚ) :
    0 ≤ 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 4 * d ^ 2 - 2 * a * b - 2 * a * c - 2 * a * d := by
  nlinarith [sq_nonneg (2 * a - b - c - d), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (c - d), sq_nonneg b, sq_nonneg c, sq_nonneg d]

/-! ### Coordinate bounds `xᵢ² ≤ (G⁻¹)ᵢᵢ (x, x)`

For `ℓ = G⁻¹ eᵢ` and `C = (G⁻¹)ᵢᵢ = (ℓ, ℓ)` one has
`(C x - xᵢ ℓ, C x - xᵢ ℓ) = C (C (x, x) - xᵢ²)`, so positivity gives the bound.
The columns `ℓ` used are those of the inverse Gram matrices
`G⁻¹(L₇ ⊕ A₂) = [[4,-1],[-1,2]]/7 ⊕ [[2,1],[1,2]]/3`,
`G⁻¹(G₇⁻) = [[16,11,6,1],[11,22,12,2],[6,12,18,3],[1,2,3,4]]/21`,
`G⁻¹(A₁² ⊕ A₂) = diag(1/2,1/2) ⊕ [[2,1],[1,2]]/3`,
`G⁻¹(G₆⁻) = [[8,4,4,2],[4,5,2,1],[4,2,5,1],[2,1,1,2]]/6`. -/

/-- `x0² ≤ (G⁻¹)₍00₎ · (x, x)`: the form evaluated at `C x - x0 ℓ`, with `ℓ = G⁻¹ e0`, is
`C (C (x, x) - x0²)`. -/
theorem sq0_L7A2 (x : Fin 4 → ℚ) : x 0 ^ 2 ≤ 4/7 * gramNorm gramL7A2 x := by
  rw [gramNorm_L7A2]
  nlinarith [psd_L7A2 (4/7 * x 0 - x 0 * (4/7)) (4/7 * x 1 - x 0 * (-1/7)) (4/7 * x 2 - x 0 * (0)) (4/7 * x 3 - x 0 * (0))]

/-- `x1² ≤ (G⁻¹)₍11₎ · (x, x)`: the form evaluated at `C x - x1 ℓ`, with `ℓ = G⁻¹ e1`, is
`C (C (x, x) - x1²)`. -/
theorem sq1_L7A2 (x : Fin 4 → ℚ) : x 1 ^ 2 ≤ 2/7 * gramNorm gramL7A2 x := by
  rw [gramNorm_L7A2]
  nlinarith [psd_L7A2 (2/7 * x 0 - x 1 * (-1/7)) (2/7 * x 1 - x 1 * (2/7)) (2/7 * x 2 - x 1 * (0)) (2/7 * x 3 - x 1 * (0))]

/-- `x2² ≤ (G⁻¹)₍22₎ · (x, x)`: the form evaluated at `C x - x2 ℓ`, with `ℓ = G⁻¹ e2`, is
`C (C (x, x) - x2²)`. -/
theorem sq2_L7A2 (x : Fin 4 → ℚ) : x 2 ^ 2 ≤ 2/3 * gramNorm gramL7A2 x := by
  rw [gramNorm_L7A2]
  nlinarith [psd_L7A2 (2/3 * x 0 - x 2 * (0)) (2/3 * x 1 - x 2 * (0)) (2/3 * x 2 - x 2 * (2/3)) (2/3 * x 3 - x 2 * (1/3))]

/-- `x3² ≤ (G⁻¹)₍33₎ · (x, x)`: the form evaluated at `C x - x3 ℓ`, with `ℓ = G⁻¹ e3`, is
`C (C (x, x) - x3²)`. -/
theorem sq3_L7A2 (x : Fin 4 → ℚ) : x 3 ^ 2 ≤ 2/3 * gramNorm gramL7A2 x := by
  rw [gramNorm_L7A2]
  nlinarith [psd_L7A2 (2/3 * x 0 - x 3 * (0)) (2/3 * x 1 - x 3 * (0)) (2/3 * x 2 - x 3 * (1/3)) (2/3 * x 3 - x 3 * (2/3))]

/-- Coordinate bounds `xᵢ² ≤ (G⁻¹)ᵢᵢ (x, x)` for `L7A2`. -/
def boundL7A2 : Fin 4 → ℚ := ![4/7, 2/7, 2/3, 2/3]

theorem coord_L7A2 (x : Fin 4 → ℚ) (i : Fin 4) :
    x i ^ 2 ≤ boundL7A2 i * gramNorm gramL7A2 x := by
  fin_cases i <;>
    first
    | exact sq0_L7A2 x
    | exact sq1_L7A2 x
    | exact sq2_L7A2 x
    | exact sq3_L7A2 x

/-- `x0² ≤ (G⁻¹)₍00₎ · (x, x)`: the form evaluated at `C x - x0 ℓ`, with `ℓ = G⁻¹ e0`, is
`C (C (x, x) - x0²)`. -/
theorem sq0_G7m (x : Fin 4 → ℚ) : x 0 ^ 2 ≤ 16/21 * gramNorm gramG7m x := by
  rw [gramNorm_G7m]
  nlinarith [psd_G7m (16/21 * x 0 - x 0 * (16/21)) (16/21 * x 1 - x 0 * (11/21)) (16/21 * x 2 - x 0 * (6/21)) (16/21 * x 3 - x 0 * (1/21))]

/-- `x1² ≤ (G⁻¹)₍11₎ · (x, x)`: the form evaluated at `C x - x1 ℓ`, with `ℓ = G⁻¹ e1`, is
`C (C (x, x) - x1²)`. -/
theorem sq1_G7m (x : Fin 4 → ℚ) : x 1 ^ 2 ≤ 22/21 * gramNorm gramG7m x := by
  rw [gramNorm_G7m]
  nlinarith [psd_G7m (22/21 * x 0 - x 1 * (11/21)) (22/21 * x 1 - x 1 * (22/21)) (22/21 * x 2 - x 1 * (12/21)) (22/21 * x 3 - x 1 * (2/21))]

/-- `x2² ≤ (G⁻¹)₍22₎ · (x, x)`: the form evaluated at `C x - x2 ℓ`, with `ℓ = G⁻¹ e2`, is
`C (C (x, x) - x2²)`. -/
theorem sq2_G7m (x : Fin 4 → ℚ) : x 2 ^ 2 ≤ 18/21 * gramNorm gramG7m x := by
  rw [gramNorm_G7m]
  nlinarith [psd_G7m (18/21 * x 0 - x 2 * (6/21)) (18/21 * x 1 - x 2 * (12/21)) (18/21 * x 2 - x 2 * (18/21)) (18/21 * x 3 - x 2 * (3/21))]

/-- `x3² ≤ (G⁻¹)₍33₎ · (x, x)`: the form evaluated at `C x - x3 ℓ`, with `ℓ = G⁻¹ e3`, is
`C (C (x, x) - x3²)`. -/
theorem sq3_G7m (x : Fin 4 → ℚ) : x 3 ^ 2 ≤ 4/21 * gramNorm gramG7m x := by
  rw [gramNorm_G7m]
  nlinarith [psd_G7m (4/21 * x 0 - x 3 * (1/21)) (4/21 * x 1 - x 3 * (2/21)) (4/21 * x 2 - x 3 * (3/21)) (4/21 * x 3 - x 3 * (4/21))]

/-- Coordinate bounds `xᵢ² ≤ (G⁻¹)ᵢᵢ (x, x)` for `G7m`. -/
def boundG7m : Fin 4 → ℚ := ![16/21, 22/21, 18/21, 4/21]

theorem coord_G7m (x : Fin 4 → ℚ) (i : Fin 4) :
    x i ^ 2 ≤ boundG7m i * gramNorm gramG7m x := by
  fin_cases i <;>
    first
    | exact sq0_G7m x
    | exact sq1_G7m x
    | exact sq2_G7m x
    | exact sq3_G7m x

/-- `x0² ≤ (G⁻¹)₍00₎ · (x, x)`: the form evaluated at `C x - x0 ℓ`, with `ℓ = G⁻¹ e0`, is
`C (C (x, x) - x0²)`. -/
theorem sq0_A1A1A2 (x : Fin 4 → ℚ) : x 0 ^ 2 ≤ 1/2 * gramNorm gramA1A1A2 x := by
  rw [gramNorm_A1A1A2]
  nlinarith [psd_A1A1A2 (1/2 * x 0 - x 0 * (1/2)) (1/2 * x 1 - x 0 * (0)) (1/2 * x 2 - x 0 * (0)) (1/2 * x 3 - x 0 * (0))]

/-- `x1² ≤ (G⁻¹)₍11₎ · (x, x)`: the form evaluated at `C x - x1 ℓ`, with `ℓ = G⁻¹ e1`, is
`C (C (x, x) - x1²)`. -/
theorem sq1_A1A1A2 (x : Fin 4 → ℚ) : x 1 ^ 2 ≤ 1/2 * gramNorm gramA1A1A2 x := by
  rw [gramNorm_A1A1A2]
  nlinarith [psd_A1A1A2 (1/2 * x 0 - x 1 * (0)) (1/2 * x 1 - x 1 * (1/2)) (1/2 * x 2 - x 1 * (0)) (1/2 * x 3 - x 1 * (0))]

/-- `x2² ≤ (G⁻¹)₍22₎ · (x, x)`: the form evaluated at `C x - x2 ℓ`, with `ℓ = G⁻¹ e2`, is
`C (C (x, x) - x2²)`. -/
theorem sq2_A1A1A2 (x : Fin 4 → ℚ) : x 2 ^ 2 ≤ 2/3 * gramNorm gramA1A1A2 x := by
  rw [gramNorm_A1A1A2]
  nlinarith [psd_A1A1A2 (2/3 * x 0 - x 2 * (0)) (2/3 * x 1 - x 2 * (0)) (2/3 * x 2 - x 2 * (2/3)) (2/3 * x 3 - x 2 * (1/3))]

/-- `x3² ≤ (G⁻¹)₍33₎ · (x, x)`: the form evaluated at `C x - x3 ℓ`, with `ℓ = G⁻¹ e3`, is
`C (C (x, x) - x3²)`. -/
theorem sq3_A1A1A2 (x : Fin 4 → ℚ) : x 3 ^ 2 ≤ 2/3 * gramNorm gramA1A1A2 x := by
  rw [gramNorm_A1A1A2]
  nlinarith [psd_A1A1A2 (2/3 * x 0 - x 3 * (0)) (2/3 * x 1 - x 3 * (0)) (2/3 * x 2 - x 3 * (1/3)) (2/3 * x 3 - x 3 * (2/3))]

/-- Coordinate bounds `xᵢ² ≤ (G⁻¹)ᵢᵢ (x, x)` for `A1A1A2`. -/
def boundA1A1A2 : Fin 4 → ℚ := ![1/2, 1/2, 2/3, 2/3]

theorem coord_A1A1A2 (x : Fin 4 → ℚ) (i : Fin 4) :
    x i ^ 2 ≤ boundA1A1A2 i * gramNorm gramA1A1A2 x := by
  fin_cases i <;>
    first
    | exact sq0_A1A1A2 x
    | exact sq1_A1A1A2 x
    | exact sq2_A1A1A2 x
    | exact sq3_A1A1A2 x

/-- `x0² ≤ (G⁻¹)₍00₎ · (x, x)`: the form evaluated at `C x - x0 ℓ`, with `ℓ = G⁻¹ e0`, is
`C (C (x, x) - x0²)`. -/
theorem sq0_G6m (x : Fin 4 → ℚ) : x 0 ^ 2 ≤ 8/6 * gramNorm gramG6m x := by
  rw [gramNorm_G6m]
  nlinarith [psd_G6m (8/6 * x 0 - x 0 * (8/6)) (8/6 * x 1 - x 0 * (4/6)) (8/6 * x 2 - x 0 * (4/6)) (8/6 * x 3 - x 0 * (2/6))]

/-- `x1² ≤ (G⁻¹)₍11₎ · (x, x)`: the form evaluated at `C x - x1 ℓ`, with `ℓ = G⁻¹ e1`, is
`C (C (x, x) - x1²)`. -/
theorem sq1_G6m (x : Fin 4 → ℚ) : x 1 ^ 2 ≤ 5/6 * gramNorm gramG6m x := by
  rw [gramNorm_G6m]
  nlinarith [psd_G6m (5/6 * x 0 - x 1 * (4/6)) (5/6 * x 1 - x 1 * (5/6)) (5/6 * x 2 - x 1 * (2/6)) (5/6 * x 3 - x 1 * (1/6))]

/-- `x2² ≤ (G⁻¹)₍22₎ · (x, x)`: the form evaluated at `C x - x2 ℓ`, with `ℓ = G⁻¹ e2`, is
`C (C (x, x) - x2²)`. -/
theorem sq2_G6m (x : Fin 4 → ℚ) : x 2 ^ 2 ≤ 5/6 * gramNorm gramG6m x := by
  rw [gramNorm_G6m]
  nlinarith [psd_G6m (5/6 * x 0 - x 2 * (4/6)) (5/6 * x 1 - x 2 * (2/6)) (5/6 * x 2 - x 2 * (5/6)) (5/6 * x 3 - x 2 * (1/6))]

/-- `x3² ≤ (G⁻¹)₍33₎ · (x, x)`: the form evaluated at `C x - x3 ℓ`, with `ℓ = G⁻¹ e3`, is
`C (C (x, x) - x3²)`. -/
theorem sq3_G6m (x : Fin 4 → ℚ) : x 3 ^ 2 ≤ 2/6 * gramNorm gramG6m x := by
  rw [gramNorm_G6m]
  nlinarith [psd_G6m (2/6 * x 0 - x 3 * (2/6)) (2/6 * x 1 - x 3 * (1/6)) (2/6 * x 2 - x 3 * (1/6)) (2/6 * x 3 - x 3 * (2/6))]

/-- Coordinate bounds `xᵢ² ≤ (G⁻¹)ᵢᵢ (x, x)` for `G6m`. -/
def boundG6m : Fin 4 → ℚ := ![8/6, 5/6, 5/6, 2/6]

theorem coord_G6m (x : Fin 4 → ℚ) (i : Fin 4) :
    x i ^ 2 ≤ boundG6m i * gramNorm gramG6m x := by
  fin_cases i <;>
    first
    | exact sq0_G6m x
    | exact sq1_G6m x
    | exact sq2_G6m x
    | exact sq3_G6m x

/-! ### Theta coefficients at negative exponents vanish -/

theorem shell_eq_empty_of_neg {G : Matrix (Fin 4) (Fin 4) ℤ} {g : Fin 4 → ℚ} {e : ℚ}
    (hpsd : ∀ x, 0 ≤ gramNorm G x) (he : e < 0) : shell G g e = ∅ := by
  ext n
  simp only [shell, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have := hpsd (cosetPt g n)
  unfold energy at h
  linarith

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.shell_eq_of_box
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_eq_list_sum
#print axioms HaagerupIzumi.C8.Theta.coord_G7m
#print axioms HaagerupIzumi.C8.Theta.minusSixD2Coeff_one
