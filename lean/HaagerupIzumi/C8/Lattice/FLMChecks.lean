module

public import HaagerupIzumi.C8.Lattice.Model

@[expose] public section

/-!
# Kernel checks of `L(0)` and `L(-1)` on the 24 generating fields

Benchmark item 4 (`Lattice/Benchmark.md` §5).  For each of the 24 fields
`b ∈ {hᵢ(-1)𝟏, e^{αᵢ}, e^{-αᵢ}}` (`genList`, as rational sparse vectors) the kernel checks

* `b` consists of canonical monomials of grade one,
* `ω_(0) b = b_(-2) 𝟏` (the `L(-1)` property on `b`),
* `ω_(1) b = b` (the `L(0)` property on `b`),

each identity after bringing both sides to a canonical form (`canonVec`: sort the oscillator
codes of every state, then sort and merge the terms; `toV_canonVec`: this does not change the
vector of `V`).  Used in `FLMReduce.lean`.

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- The canonical form of a sparse vector: canonical states, sorted, merged, no zero terms. -/
def canonVec (v : Vec) : Vec := normalize (v.map fun p => ((p.1.1, sortCodes p.1.2), p.2))

theorem canon_sortCodes (s : State) : canon (s.1, sortCodes s.2) = canon s := by
  apply Subtype.ext
  show (s.1, sortCodes (sortCodes s.2)) = (s.1, sortCodes s.2)
  rw [sortCodes_of_pairwise (sortCodes_pairwise s.2)]

theorem push_toFock_map_sort (v : Vec) :
    push (toFock (v.map fun p => ((p.1.1, sortCodes p.1.2), p.2))) = push (toFock v) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    simp only [List.map_cons, toFock_cons, map_add, ih, push_single, canon_sortCodes]

theorem toV_canonVec (v : Vec) : toV (canonVec v) = toV v := by
  unfold toV canonVec
  rw [toFock_normalize, push_toFock_map_sort]

/-- `hᵢ(-1)𝟏` as a rational sparse vector. -/
def hgen (i : ℕ) : Vec := [((Mom.zero, [i]), 1)]

/-- `e^α` as a rational sparse vector. -/
def egen (α : Mom) : Vec := [((α, []), 1)]

/-- The 24 generating fields. -/
def genList : List Vec :=
  (List.range 8).flatMap fun i => [hgen i, egen (Mom.simple i), egen (Mom.neg (Mom.simple i))]

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

/-- **The finite certificate of item 4**: canonical grade-one states, `ω_(0) b = b_(-2)𝟏` and
`ω_(1) b = b` for the 24 generating fields. -/
theorem genList_checks : ∀ b ∈ genList, (∀ p ∈ b, Valid p.1 ∧ grade p.1 = 1) ∧
    canonVec (mode omega 0 b) = canonVec (mode b (-2) vac) ∧
    canonVec (mode omega 1 b) = canonVec b := by
  decide +kernel

theorem toV_vac_eq : toV vac = vacV := by
  simp [vac, toV_cons_mk, canon_of_valid (show Valid vacState from List.Pairwise.nil), vacV,
    vacValid]

#print axioms toV_canonVec
#print axioms genList_checks

end LatticeVOA
end HaagerupIzumi.C8
