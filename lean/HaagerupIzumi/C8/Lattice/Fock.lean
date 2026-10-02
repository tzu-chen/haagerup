module

public import HaagerupIzumi.C8.Data.Lattice
public import Mathlib.Algebra.Ring.Int.Parity

@[expose] public section

/-!
# The Fock model of `V_L`, `L = E₆ ⊕ A₂`: computable states and sparse vectors

Work item W1 of `C8/ROADMAP.md` (lattice construction of Appendix A, lines 1872–1910 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  This file is the *computable layer*: data
types that the kernel can evaluate with `decide +kernel`.  The modes are in
`Lattice/Modes.lean`, the semantic layer (`State →₀ ℚ`) in `Lattice/Semantic.lean`.

## Conventions (identical to `hi_cft_20260923_c8_exact.py`)

* `Mom`: a lattice vector `x = ∑ xᵢ αᵢ` in simple-root coordinates, Gram matrix
  `Lattice.gram` (`E₆` nodes `0,…,5`, node `2` joined to `5`; `A₂` nodes `6,7`).  `Mom.form`
  is the explicit polynomial of `Lattice.form_apply` (`Mom.form_eq`), `Mom.cocycleExp` that
  of `Lattice.cocycleExp_apply` (`Mom.cocycleExp_eq`), and `Mom.eps a b = (-1)^{cocycleExp a b}`
  is the cocycle `ε(a,b)` of `eq:cocycle` (line 1880) as a rational sign.
* `State = Mom × List ℕ`: the *unnormalized* Fock monomial
  `∏_{k ∈ osc} h_{k % 8}(-(k / 8 + 1)) e^β`, where `hᵢ = αᵢ` (simple coroot, identified with
  the simple root via the form).  The oscillator list is the Python code list; it is a
  canonical representative of the monomial when it is nondecreasing (`Valid`).
* `grade (β, osc) = (β,β)/2 + ∑_{k ∈ osc} (k / 8 + 1)` (the `L(0)`-weight).
* `Vec = List (State × ℚ)`: a sparse vector.  Vectors are kept *strictly sorted* for
  `stateCmp` (lexicographic on the eight coordinates, then on the code list, shorter prefix
  first: the order of Python's `sorted`) with nonzero coefficients, so equal vectors are equal
  lists.  `addVec` is a linear-time merge of sorted vectors, `normalize` an insertion sort
  for short unsorted lists, `bindVec` the linear extension of a map on states (its summands are
  merged pairwise in a balanced tree, `mergeAll`, to avoid quadratic accumulation).

All functions are structurally recursive (no well-founded recursion, no `mergeSort`), so
that `decide +kernel` evaluates them.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## Comparisons -/

/-- Three-way comparison of integers (equality is tested first: it is the cheap and common
case in kernel evaluation). -/
def cmpZ (a b : ℤ) : Ordering := if a = b then .eq else if a < b then .lt else .gt

theorem cmpZ_eq {a b : ℤ} (h : cmpZ a b = .eq) : a = b := by
  unfold cmpZ at h
  by_cases h1 : a = b
  · exact h1
  · rw [if_neg h1] at h
    by_cases h2 : a < b
    · rw [if_pos h2] at h
      exact absurd h (by decide)
    · rw [if_neg h2] at h
      exact absurd h (by decide)

/-- Three-way comparison of natural numbers. -/
def cmpN (a b : ℕ) : Ordering := if a = b then .eq else if a < b then .lt else .gt

theorem cmpN_eq {a b : ℕ} (h : cmpN a b = .eq) : a = b := by
  unfold cmpN at h
  by_cases h1 : a = b
  · exact h1
  · rw [if_neg h1] at h
    by_cases h2 : a < b
    · rw [if_pos h2] at h
      exact absurd h (by decide)
    · rw [if_neg h2] at h
      exact absurd h (by decide)

/-! ## Lattice vectors -/

/-- A vector of `L` in simple-root coordinates `x = ∑ xᵢ αᵢ`. -/
structure Mom where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x5 : ℤ
  x6 : ℤ
  x7 : ℤ
  deriving DecidableEq

namespace Mom

/-- The zero vector. -/
def zero : Mom := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Addition. -/
def add (a b : Mom) : Mom :=
  ⟨a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4, a.x5 + b.x5,
    a.x6 + b.x6, a.x7 + b.x7⟩

/-- Negation. -/
def neg (a : Mom) : Mom := ⟨-a.x0, -a.x1, -a.x2, -a.x3, -a.x4, -a.x5, -a.x6, -a.x7⟩

/-- The `i`-th coordinate (`0` for `i ≥ 8`). -/
def coord (a : Mom) : ℕ → ℤ
  | 0 => a.x0
  | 1 => a.x1
  | 2 => a.x2
  | 3 => a.x3
  | 4 => a.x4
  | 5 => a.x5
  | 6 => a.x6
  | 7 => a.x7
  | _ => 0

/-- The simple root `αᵢ` (`0` for `i ≥ 8`). -/
def simple : ℕ → Mom
  | 0 => ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
  | 4 => ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
  | 5 => ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
  | 6 => ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
  | 7 => ⟨0, 0, 0, 0, 0, 0, 0, 1⟩
  | _ => zero

/-- `(αᵢ, a) = (G a)ᵢ`, the eigenvalue of `hᵢ(0)` on `e^a` (`0` for `i ≥ 8`). -/
def pairSimple (i : ℕ) (a : Mom) : ℤ :=
  match i with
  | 0 => 2 * a.x0 - a.x1
  | 1 => -a.x0 + 2 * a.x1 - a.x2
  | 2 => -a.x1 + 2 * a.x2 - a.x3 - a.x5
  | 3 => -a.x2 + 2 * a.x3 - a.x4
  | 4 => -a.x3 + 2 * a.x4
  | 5 => -a.x2 + 2 * a.x5
  | 6 => 2 * a.x6 - a.x7
  | 7 => -a.x6 + 2 * a.x7
  | _ => 0

/-- The lattice form `(a, b) = aᵀ G b`, as the explicit polynomial of `Lattice.form_apply`. -/
def form (a b : Mom) : ℤ :=
  2 * (a.x0 * b.x0 + a.x1 * b.x1 + a.x2 * b.x2 + a.x3 * b.x3 + a.x4 * b.x4 + a.x5 * b.x5
      + a.x6 * b.x6 + a.x7 * b.x7)
    - (a.x0 * b.x1 + a.x1 * b.x0) - (a.x1 * b.x2 + a.x2 * b.x1) - (a.x2 * b.x3 + a.x3 * b.x2)
    - (a.x3 * b.x4 + a.x4 * b.x3) - (a.x2 * b.x5 + a.x5 * b.x2) - (a.x6 * b.x7 + a.x7 * b.x6)

/-- The norm `(a, a)`. -/
def norm (a : Mom) : ℤ := form a a

/-- The exponent of the cocycle `ε(a,b) = (-1)^{∑ᵢ aᵢbᵢ + ∑_{i>j} aᵢ bⱼ Gᵢⱼ}`
(`Lattice.cocycleExp_apply`). -/
def cocycleExp (a b : Mom) : ℤ :=
  (a.x0 * b.x0 + a.x1 * b.x1 + a.x2 * b.x2 + a.x3 * b.x3 + a.x4 * b.x4 + a.x5 * b.x5
      + a.x6 * b.x6 + a.x7 * b.x7)
    - (a.x1 * b.x0 + a.x2 * b.x1 + a.x3 * b.x2 + a.x4 * b.x3 + a.x5 * b.x2 + a.x7 * b.x6)

/-- The cocycle sign `ε(a, b)` as a rational number. -/
def eps (a b : Mom) : ℚ := if cocycleExp a b % 2 = 0 then 1 else -1

/-- Lexicographic comparison of the coordinates. -/
def cmp (a b : Mom) : Ordering :=
  (cmpZ a.x0 b.x0).then <| (cmpZ a.x1 b.x1).then <| (cmpZ a.x2 b.x2).then <|
    (cmpZ a.x3 b.x3).then <| (cmpZ a.x4 b.x4).then <| (cmpZ a.x5 b.x5).then <|
      (cmpZ a.x6 b.x6).then (cmpZ a.x7 b.x7)

theorem cmp_eq {a b : Mom} (h : cmp a b = .eq) : a = b := by
  cases a
  cases b
  simp only [cmp, Ordering.then_eq_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [cmpZ_eq h0, cmpZ_eq h1, cmpZ_eq h2, cmpZ_eq h3, cmpZ_eq h4, cmpZ_eq h5, cmpZ_eq h6,
    cmpZ_eq h7]

/-- The coordinate vector in `Fin 8 → ℤ` (the type of `Data/Lattice`). -/
def toVec (a : Mom) : Fin 8 → ℤ := ![a.x0, a.x1, a.x2, a.x3, a.x4, a.x5, a.x6, a.x7]

/-- From a coordinate vector. -/
def ofVec (v : Fin 8 → ℤ) : Mom := ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩

theorem ofVec_toVec (a : Mom) : ofVec (toVec a) = a := rfl

theorem toVec_ofVec (v : Fin 8 → ℤ) : toVec (ofVec v) = v := by
  funext i
  fin_cases i <;> rfl

/-- `Mom.form` is the lattice form of `Data/Lattice`. -/
theorem form_eq (a b : Mom) : form a b = Lattice.form a.toVec b.toVec := by
  rw [Lattice.form_apply]
  rfl

/-- `Mom.cocycleExp` is the cocycle exponent of `Data/Lattice`. -/
theorem cocycleExp_eq (a b : Mom) : cocycleExp a b = Lattice.cocycleExp a.toVec b.toVec := by
  rw [Lattice.cocycleExp_apply]
  rfl

theorem form_ofVec (v w : Fin 8 → ℤ) : form (ofVec v) (ofVec w) = Lattice.form v w := by
  rw [form_eq, toVec_ofVec, toVec_ofVec]

/-- `Mom.eps` is the sign `Lattice.epsilon`. -/
theorem eps_eq (a b : Mom) :
    eps a b = ((Lattice.epsilon a.toVec b.toVec : ℤˣ) : ℤ) := by
  rw [eps, Lattice.epsilon, ← cocycleExp_eq]
  rcases Int.emod_two_eq_zero_or_one (cocycleExp a b) with h | h
  · rw [if_pos h, Int.negOnePow_even _ (Int.even_iff.mpr h)]
    simp
  · have h' : cocycleExp a b % 2 ≠ 0 := by omega
    rw [if_neg h', Int.negOnePow_odd _ (Int.odd_iff.mpr h)]
    simp

end Mom

/-! ## Fock states -/

/-- A Fock monomial `(β, osc)` = `∏_{k ∈ osc} h_{k % 8}(-(k / 8 + 1)) e^β`. -/
abbrev State := Mom × List ℕ

/-- The oscillator grade `∑_{k ∈ osc} (k / 8 + 1)`. -/
def oscGrade : List ℕ → ℕ
  | [] => 0
  | k :: ks => (k / 8 + 1) + oscGrade ks

/-- The `L(0)`-grade `(β,β)/2 + oscGrade osc`. -/
def grade (s : State) : ℕ := (s.1.norm / 2).toNat + oscGrade s.2

/-- A state is a canonical basis monomial when its code list is nondecreasing. -/
def Valid (s : State) : Prop := s.2.Pairwise (· ≤ ·)

instance (s : State) : Decidable (Valid s) :=
  inferInstanceAs (Decidable (s.2.Pairwise (· ≤ ·)))

/-- Comparison of code lists (lexicographic, shorter prefix first). -/
def oscCmp : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmpN a b).then (oscCmp as bs)

theorem oscCmp_eq : ∀ {l m : List ℕ}, oscCmp l m = .eq → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [oscCmp] at h
  | _ :: _, [], h => by simp [oscCmp] at h
  | a :: as, b :: bs, h => by
    simp only [oscCmp, Ordering.then_eq_eq] at h
    rw [cmpN_eq h.1, oscCmp_eq h.2]

/-- The total order on states used to keep vectors sorted. -/
def stateCmp (s t : State) : Ordering := (Mom.cmp s.1 t.1).then (oscCmp s.2 t.2)

theorem stateCmp_eq {s t : State} (h : stateCmp s t = .eq) : s = t := by
  simp only [stateCmp, Ordering.then_eq_eq] at h
  exact Prod.ext (Mom.cmp_eq h.1) (oscCmp_eq h.2)

/-- The vacuum state `e^0`. -/
def vacState : State := (Mom.zero, [])

/-! ## Sparse vectors -/

/-- A sparse vector: a list of states with rational coefficients. -/
abbrev Vec := List (State × ℚ)

/-- Insert `c · s` (`c ≠ 0` intended) into a sorted vector, combining equal states and
dropping a resulting zero coefficient. -/
def addTermAux (s : State) (c : ℚ) : Vec → Vec
  | [] => [(s, c)]
  | (t, d) :: rest =>
    match stateCmp s t with
    | .lt => (s, c) :: (t, d) :: rest
    | .eq => if c + d = 0 then rest else (t, c + d) :: rest
    | .gt => (t, d) :: addTermAux s c rest

/-- Add `c · s` to a vector (insertion). -/
def addTerm (s : State) (c : ℚ) (v : Vec) : Vec := if c = 0 then v else addTermAux s c v

/-- The sorted form of an arbitrary vector (insertion sort; for short lists). -/
def normalize (v : Vec) : Vec := v.foldr (fun p acc => addTerm p.1 p.2 acc) []

/-- Merge the term `p` followed by `as` (whose merge with any vector is `mergeAs`) into a
sorted vector. -/
def mergeInto (p : State × ℚ) (as : Vec) (mergeAs : Vec → Vec) : Vec → Vec
  | [] => p :: as
  | q :: bs =>
    match stateCmp p.1 q.1 with
    | .lt => p :: mergeAs (q :: bs)
    | .eq => if p.2 + q.2 = 0 then mergeAs bs else (p.1, p.2 + q.2) :: mergeAs bs
    | .gt => q :: mergeInto p as mergeAs bs

/-- Sum of two vectors by merging (linear time; the result is sorted when both are). -/
def addVec : Vec → Vec → Vec
  | [], b => b
  | p :: as, b => mergeInto p as (addVec as) b

/-- Scalar multiple. -/
def smul (c : ℚ) (v : Vec) : Vec :=
  if c = 0 then [] else if c = 1 then v else v.map fun p => (p.1, c * p.2)

/-- Merge adjacent pairs of a list of vectors. -/
def mergePairs : List Vec → List Vec
  | a :: b :: rest => addVec a b :: mergePairs rest
  | l => l

/-- The sum of a list of vectors by balanced pairwise merging (`⌈log₂ n⌉` rounds suffice for
`n` vectors; with no fuel left the rest is merged linearly). -/
def mergeAll : ℕ → List Vec → Vec
  | 0, l => l.foldr addVec []
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: l => mergeAll fuel (mergePairs (a :: b :: l))

/-- Linear extension: `∑_{(s,c) ∈ v} c · f s` (balanced merging of the `|v|` summands). -/
def bindVec (v : Vec) (f : State → Vec) : Vec :=
  mergeAll v.length (v.map fun p => smul p.2 (f p.1))

/-- The vacuum vector `𝟏`. -/
def vac : Vec := [(vacState, 1)]

/-- Convenience constructor for generated data: the state `(⟨a,…,h⟩, o)`. -/
def S (a b c d e f g h : ℤ) (o : List ℕ) : State := (⟨a, b, c, d, e, f, g, h⟩, o)

/-! ## Natural-number encoding of generated data

Generated data files write states and vectors as lists of natural-number literals only
(elaborating many `ℤ` literals is slow: about 2 ms each in a measured probe, against well under
0.1 ms for `ℕ`).  Signed integers are zigzag encoded (`unzig`: `2z ↦ z`, `2z-1 ↦ -z`).
A state row is `[zz m₀, …, zz m₇, codes…]`, a term row `[zz num, den, zz m₀, …, zz m₇,
codes…]` (coefficient `num/den`), and a mode sample `[[zz n], u, v, term rows…]`. -/

/-- Zigzag decoding `0, 1, 2, 3, 4, … ↦ 0, -1, 1, -2, 2, …`. -/
def unzig (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n + 1) / 2 : ℕ) : ℤ)

/-- Decode the momentum `[zz m₀, …, zz m₇, …]`. -/
def decMom : List ℕ → Mom
  | a :: b :: c :: d :: e :: f :: g :: h :: _ =>
    ⟨unzig a, unzig b, unzig c, unzig d, unzig e, unzig f, unzig g, unzig h⟩
  | _ => Mom.zero

/-- Decode a state row `[zz m₀, …, zz m₇, codes…]`. -/
def decState (l : List ℕ) : State := (decMom l, l.drop 8)

/-- Decode a term row `[zz num, den, zz m₀, …, zz m₇, codes…]`. -/
def decTerm : List ℕ → State × ℚ
  | p :: q :: rest => (decState rest, if q = 1 then (unzig p : ℚ) else (unzig p : ℚ) / (q : ℚ))
  | _ => (vacState, 0)

/-- Decode a vector (list of term rows). -/
def decVec (l : List (List ℕ)) : Vec := l.map decTerm

/-- The mode index `n` of a sample `[[zz n], u, v, out…]`. -/
def sampleN (t : List (List ℕ)) : ℤ := unzig ((t.headD []).headD 0)

/-- The state `u` of a sample. -/
def sampleU (t : List (List ℕ)) : State := decState (t.getD 1 [])

/-- The state `v` of a sample. -/
def sampleV (t : List (List ℕ)) : State := decState (t.getD 2 [])

/-- The expected output vector `u_(n) v` of a sample. -/
def sampleOut (t : List (List ℕ)) : Vec := decVec (t.drop 3)

/-! ## Sanity checks of the representation -/

example : normalize [(S 0 0 0 0 0 0 0 1 [], 1), (S 0 0 0 0 0 0 0 0 [3], 2),
    (S 0 0 0 0 0 0 0 1 [], -1), (S 0 0 0 0 0 0 0 0 [1, 2], 1 / 2)] =
    [(S 0 0 0 0 0 0 0 0 [1, 2], 1 / 2), (S 0 0 0 0 0 0 0 0 [3], 2)] := by
  decide +kernel

example : unzig 0 = 0 ∧ unzig 1 = -1 ∧ unzig 4 = 2 ∧ unzig 7 = -4 ∧
    decTerm [3, 2, 2, 0, 0, 0, 0, 0, 0, 1, 9] = (S 1 0 0 0 0 0 0 (-1) [9], -2 / 2) := by
  decide +kernel

example : Mom.norm ⟨-1, -2, -3, -2, -1, -2, 0, 0⟩ = 2 ∧
    Mom.eps ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ ⟨-1, 0, 0, 0, 0, 0, 0, 0⟩ = -1 := by
  decide +kernel

#print axioms Mom.cmp_eq
#print axioms stateCmp_eq
#print axioms Mom.form_eq
#print axioms Mom.cocycleExp_eq
#print axioms Mom.eps_eq

end LatticeVOA
end HaagerupIzumi.C8
