module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Tactic.Ring
public import HaagerupIzumi.C8.Data.Spectra

@[expose] public section

/-!
# The Gate 5 weight table and the isotropy facts

Finite data of `c8_expanded_20260929/haagerup_c8_expanded.tex`:

* Gate 5, subsection "The charged families" (lines 2494–2531): the joint
  current highest weights of the eight charged fields (`chargedWeight`,
  consistent with the current dimensions of `Spectra`,
  `chargedWeight_eq_dims`), the weights of the bottom inputs `p₃`, `p₆`,
  the bottom witnesses `β(a₃,p₃) ∝ q₋`, `β(a₆,p₆) ∝ q₋`
  (`bottom_witness_weights`), and the table of pairs (`gate5Rows`): every
  listed output weight is the sum of the input weights
  (`gate5Rows_output`) and lies outside the weights of the triplet `Q`
  (`gate5Rows_not_in_Q`).  Hence `β(a_i,p_j) = 0` for these rows by weight.
* The order-thirteen core (lines 3051, 3075–3079): for
  `q(j,k) = -(j²+k²)` on `(ℤ/13)²`, `5² = -1`, the isotropic vectors are
  exactly the two lines `k = ±5j` (`q13_eq_zero_iff`), a sum of nonzero
  vectors from the two lines is never isotropic (`q13_lines_sum`), and every
  isotropic subgroup lies in one of the two lines
  (`isotropic_subgroup_le_line`).
* The metric group of the local `B`-modules (lines 3326–3334):
  `q(a,b) = 2a² + b²` on `(ℤ/3)²` has isotropic lines `L₊ = {(a,a)}`,
  `L₋ = {(a,-a)}`, these are the only isotropic vectors (`q3_eq_zero_iff`),
  `L₊ ∩ L₋ = 0` and `(ℤ/3)² = L₊ ⊕ L₋` (`q3_decomposition`,
  `q3_lines_independent`); `q` and its polar form vanish on `L₋` (symmetric, trivial twists:
  `Lminus_symmetric_trivial_twists`); every coset of `L₊` meets `L₋` once
  (`coset_Lplus_meets_Lminus_once`); and the Hom count of free `H/B`-module induction on `L₋`
  is `δ_{x,y}` (`free_induction_hom_count`, lines 3340–3345).

Here the quadratic forms are written with values in `ZMod 13` and `ZMod 3`;
the manuscript's `q/13 mod 1` and `q/3 mod 1` vanish exactly when these do.
Everything is decided by kernel computation; there are no hypotheses.
-/

namespace HaagerupIzumi.C8
namespace Weights

/-! ## Gate 5 weights -/

/-- Joint current highest weights `(m_L, m_R)` of the charged fields
`a₀,…,a₇` (line 2498). -/
def chargedWeight : Fin 8 → ℤ × ℤ :=
  ![(0, 4), (0, 8), (0, 8), (0, 12), (1, 1), (1, 5), (1, 7), (1, 13)]

/-- Highest weights are current dimensions minus one. -/
theorem chargedWeight_eq_dims :
    ∀ i : Fin 8, chargedWeight i =
      ((Spectra.leftDim i : ℤ) - 1, (Spectra.rightDim i : ℤ) - 1) := by
  decide

/-- Weight of `p₃ = r3_000910`. -/
def p3Weight : ℤ × ℤ := (0, -14)

/-- Weight of `p₆ = r3_000899`. -/
def p6Weight : ℤ × ℤ := (-1, -9)

/-- Weights of the current triplet `Q` of highest weight `(0,2)`:
`q₊, q₀, q₋`. -/
def qWeights : List (ℤ × ℤ) := [(0, 2), (0, 0), (0, -2)]

/-- The bottom witnesses `β(a₃,p₃) = c₃ q₋` and `β(a₆,p₆) = c₆ q₋` are
weight-consistent: both land on the weight of `q₋`. -/
theorem bottom_witness_weights :
    chargedWeight 3 + p3Weight = (0, -2) ∧ chargedWeight 6 + p6Weight = (0, -2) ∧
      ((0, -2) : ℤ × ℤ) ∈ qWeights := by
  decide

/-- The input of a row: `p₃` for `j = 3` and `p₆` for `j = 6`. -/
def inputWeight (j : Fin 8) : ℤ × ℤ := if j = 3 then p3Weight else p6Weight

/-- The table of line 2513: rows `(i, j, weight of (a_i)₀ p_j)`. -/
def gate5Rows : List (Fin 8 × Fin 8 × (ℤ × ℤ)) :=
  [(0, 3, (0, -10)), (1, 3, (0, -6)), (2, 3, (0, -6)), (3, 6, (-1, 3)), (4, 6, (0, -8)),
   (5, 3, (1, -9)), (6, 3, (1, -7)), (7, 3, (1, -1))]

/-- Every charged field occurs exactly once in the table, with input
`p₃` or `p₆`. -/
theorem gate5Rows_fields :
    gate5Rows.map Prod.fst = [0, 1, 2, 3, 4, 5, 6, 7] ∧
      ∀ r ∈ gate5Rows, r.2.1 = 3 ∨ r.2.1 = 6 := by
  decide

/-- Each listed output weight is the sum of the two input weights. -/
theorem gate5Rows_output :
    ∀ r ∈ gate5Rows, chargedWeight r.1 + inputWeight r.2.1 = r.2.2 := by
  decide

/-- Every listed output weight lies outside `Q`. -/
theorem gate5Rows_not_in_Q : ∀ r ∈ gate5Rows, r.2.2 ∉ qWeights := by
  decide

/-! ## The order-thirteen core charges -/

/-- `13 · q(j,k) = -(j² + k²)` on `(ℤ/13)²` (line 3051). -/
def q13 (v : ZMod 13 × ZMod 13) : ZMod 13 := -(v.1 ^ 2 + v.2 ^ 2)

theorem five_sq_eq_neg_one : (5 : ZMod 13) ^ 2 = -1 := by decide

/-- The isotropic vectors are exactly the two lines `k = 5j` and `k = -5j`. -/
theorem q13_eq_zero_iff' :
    ∀ j k : ZMod 13, q13 (j, k) = 0 ↔ (k = 5 * j ∨ k = -5 * j) := by
  decide +kernel

theorem q13_eq_zero_iff (v : ZMod 13 × ZMod 13) :
    q13 v = 0 ↔ (v.2 = 5 * v.1 ∨ v.2 = -5 * v.1) :=
  q13_eq_zero_iff' v.1 v.2

/-- A sum of a vector of `k = -5j` and a vector of `k = 5j` is isotropic only
if one of them is zero: the two lines together generate nonintegral spins. -/
theorem q13_lines_sum :
    ∀ a b : ZMod 13, q13 ((a, -5 * a) + (b, 5 * b)) = 0 ↔ (a = 0 ∨ b = 0) := by
  decide +kernel

/-- Every isotropic subgroup of `(ℤ/13)²` lies in one of the two lines. -/
theorem isotropic_subgroup_le_line (S : AddSubgroup (ZMod 13 × ZMod 13))
    (hS : ∀ v ∈ S, q13 v = 0) :
    (∀ v ∈ S, v.2 = 5 * v.1) ∨ (∀ v ∈ S, v.2 = -5 * v.1) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h₁, h₂⟩ := h
  simp only [not_forall] at h₁ h₂
  obtain ⟨v, hv, hv1⟩ := h₁
  obtain ⟨w, hw, hw1⟩ := h₂
  have hv2 : v.2 = -5 * v.1 := ((q13_eq_zero_iff v).mp (hS v hv)).resolve_left hv1
  have hw2 : w.2 = 5 * w.1 := ((q13_eq_zero_iff w).mp (hS w hw)).resolve_right hw1
  have hv0 : v.1 ≠ 0 := by
    intro h0; apply hv1; rw [hv2, h0]; ring
  have hw0 : w.1 ≠ 0 := by
    intro h0; apply hw1; rw [hw2, h0]; ring
  have hvw := hS (v + w) (S.add_mem hv hw)
  have hv' : v = (v.1, -5 * v.1) := Prod.ext rfl hv2
  have hw' : w = (w.1, 5 * w.1) := Prod.ext rfl hw2
  rw [hv', hw'] at hvw
  rcases (q13_lines_sum v.1 w.1).mp hvw with h | h
  · exact hv0 h
  · exact hw0 h

/-! ## The metric group `(ℤ/3)²` -/

/-- `3 · q(a,b) = 2a² + b²` on `(ℤ/3)²` (line 3329). -/
def q3 (v : ZMod 3 × ZMod 3) : ZMod 3 := 2 * v.1 ^ 2 + v.2 ^ 2

/-- Both `L₊ = {(a,a)}` and `L₋ = {(a,-a)}` are isotropic. -/
theorem q3_lines_isotropic :
    ∀ a : ZMod 3, q3 (a, a) = 0 ∧ q3 (a, -a) = 0 := by
  decide

/-- The only isotropic vectors are those of `L₊ ∪ L₋`. -/
theorem q3_eq_zero_iff :
    ∀ v : ZMod 3 × ZMod 3, q3 v = 0 ↔ (v.2 = v.1 ∨ v.2 = -v.1) := by
  decide

/-- `L₊ ∩ L₋ = 0`, i.e. the sum map `L₊ × L₋ → (ℤ/3)²` is injective. -/
theorem q3_lines_independent :
    ∀ p : ZMod 3 × ZMod 3, (p.1, p.1) + (p.2, -p.2) = 0 → p = 0 := by
  decide

/-- `(ℤ/3)² = L₊ + L₋`, with explicit components. -/
theorem q3_decomposition :
    ∀ v : ZMod 3 × ZMod 3,
      v = (2 * (v.1 + v.2), 2 * (v.1 + v.2)) + (2 * (v.1 - v.2), -(2 * (v.1 - v.2))) := by
  decide

/-- The polar form `b(v,w) = q(v+w) - q(v) - q(w)` (`3 · b`, with values in `ZMod 3`); the double
braiding of the invertibles `v, w` is `exp(2πi b(v,w)/3)`. -/
def b3 (v w : ZMod 3 × ZMod 3) : ZMod 3 := q3 (v + w) - q3 v - q3 w

/-- The pointed subcategory on `L₋` is symmetric with trivial twists (line 3335): `q` and the
double braiding `b` vanish on `L₋`. -/
theorem Lminus_symmetric_trivial_twists :
    ∀ a c : ZMod 3, q3 (a, -a) = 0 ∧ b3 (a, -a) (c, -c) = 0 := by
  decide

/-- Every coset of `L₊` meets `L₋` exactly once (line 3345: distinct elements of `L₋` represent
distinct cosets of `L₊`); so each free module `z ⊗ (H/B)` is isomorphic to `x ⊗ (H/B)` for exactly
one `x ∈ L₋`. -/
theorem coset_Lplus_meets_Lminus_once : ∀ v : ZMod 3 × ZMod 3,
    (Finset.univ.filter (fun a : ZMod 3 => ∃ c : ZMod 3, v = (a, -a) + (c, c))).card = 1 := by
  decide

/-- **The fully-faithfulness count** of free `H/B`-module induction on `L₋` (lines 3340–3345).
With `H/B = ⊕_{ℓ ∈ L₊} ℓ` in the pointed category, `Hom_{H/B}(x ⊗ (H/B), y ⊗ (H/B)) ≅
Hom(x, y ⊗ (H/B))` (free-module adjunction, external) has dimension the number of `ℓ ∈ L₊` with
`x = y + ℓ`; for `x = (a,-a)`, `y = (b,-b)` in `L₋` this is `δ_{x,y}`. -/
theorem free_induction_hom_count : ∀ a b : ZMod 3,
    (Finset.univ.filter (fun c : ZMod 3 =>
      ((a, -a) : ZMod 3 × ZMod 3) = (b, -b) + (c, c))).card = if a = b then 1 else 0 := by
  decide

#print axioms chargedWeight_eq_dims
#print axioms bottom_witness_weights
#print axioms gate5Rows_fields
#print axioms gate5Rows_output
#print axioms gate5Rows_not_in_Q
#print axioms q13_eq_zero_iff
#print axioms q13_lines_sum
#print axioms isotropic_subgroup_le_line
#print axioms q3_lines_isotropic
#print axioms q3_eq_zero_iff
#print axioms q3_lines_independent
#print axioms q3_decomposition
#print axioms Lminus_symmetric_trivial_twists
#print axioms coset_Lplus_meets_Lminus_once
#print axioms free_induction_hom_count

end Weights
end HaagerupIzumi.C8
