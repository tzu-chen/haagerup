module

public import HaagerupIzumi.C8.Lattice.Modes
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Fintype.Sets

@[expose] public section

/-!
# The semantic layer of the Fock model

Work item W1 of `C8/ROADMAP.md`.  The computable layer (`Lattice/Fock.lean`,
`Lattice/Modes.lean`) works with sorted lists; this file maps it into linear algebra so that
kernel computations give statements about vector spaces.

* `Fock = State →₀ ℚ`, and `toFock : Vec → Fock` sends a sparse list to the sum of its terms.
  `toFock` is additive under every list operation (`toFock_addTerm`, `toFock_normalize`,
  `toFock_addVec`, `toFock_smul`, `toFock_bindVec`), whatever the order of the lists, so
  sortedness only matters for the *shape* of results, never for their meaning.
* `modeOp u m : Fock →ₗ[ℚ] Fock` is the linear extension of `v ↦ basisMode u m v`, and
  `Y a m = ∑ₐ a(u) • modeOp u m` the bilinear mode `a_(m)`.  `toFock_mode`: the list
  computation `mode a m b` represents `Y (toFock a) m (toFock b)`.  Hence every identity
  `mode a m b = c` proved by `decide +kernel` is an identity `a_(m) b = c` in `Fock`.
* `basisStates d`: the canonical monomials (nondecreasing code lists) of grade `d`;
  `gradeSpace d = Finsupp.supported ℚ ℚ (basisStates d)` is the grade-`d` subspace `V_d` of the
  Fock model `S(ĥ⁻) ⊗ ℚ[L]` (unnormalized monomials form a basis), and
  `finrank_gradeSpace_eq` computes its dimension from an explicit list of its basis states.

Here `Fock` is the free vector space on all code lists; the Fock space proper is the span of
the `Valid` (sorted) states, which contains `gradeSpace d`.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open Finsupp

/-- The Fock model as a vector space: finitely supported functions on states. -/
abbrev Fock := State →₀ ℚ

/-- The vector represented by a sparse list. -/
noncomputable def toFock (v : Vec) : Fock := (v.map fun p => Finsupp.single p.1 p.2).sum

@[simp] theorem toFock_nil : toFock [] = 0 := by
  simp [toFock]

theorem toFock_cons (p : State × ℚ) (v : Vec) :
    toFock (p :: v) = Finsupp.single p.1 p.2 + toFock v := by
  simp [toFock]

@[simp] theorem toFock_cons_mk (s : State) (c : ℚ) (v : Vec) :
    toFock ((s, c) :: v) = Finsupp.single s c + toFock v :=
  toFock_cons (s, c) v

/-- The coefficient of a state in a sparse list (computable). -/
def coeffOf (v : Vec) (s : State) : ℚ := (v.map fun p => if p.1 = s then p.2 else 0).sum

theorem toFock_apply (v : Vec) (s : State) : toFock v s = coeffOf v s := by
  induction v with
  | nil => simp [coeffOf]
  | cons p v ih =>
    rw [toFock_cons, Finsupp.add_apply, ih, Finsupp.single_apply]
    simp [coeffOf]

theorem toFock_addTermAux (s : State) (c : ℚ) :
    ∀ v : Vec, toFock (addTermAux s c v) = Finsupp.single s c + toFock v
  | [] => by simp [addTermAux]
  | (t, d) :: rest => by
    rw [addTermAux]
    split
    · simp
    · rename_i h
      obtain rfl := stateCmp_eq h
      split_ifs with h'
      · rw [toFock_cons_mk, ← add_assoc, ← Finsupp.single_add, h', Finsupp.single_zero,
          zero_add]
      · rw [toFock_cons_mk, toFock_cons_mk, Finsupp.single_add, add_assoc]
    · rw [toFock_cons_mk, toFock_cons_mk, toFock_addTermAux s c rest]
      abel

theorem toFock_addTerm (s : State) (c : ℚ) (v : Vec) :
    toFock (addTerm s c v) = Finsupp.single s c + toFock v := by
  unfold addTerm
  split_ifs with h
  · simp [h]
  · exact toFock_addTermAux s c v

theorem toFock_normalize : ∀ v : Vec, toFock (normalize v) = toFock v
  | [] => rfl
  | p :: v => by
    rw [show normalize (p :: v) = addTerm p.1 p.2 (normalize v) from rfl, toFock_addTerm,
      toFock_normalize v, toFock_cons]

theorem toFock_mergeInto (as : Vec) (mergeAs : Vec → Vec)
    (h : ∀ b, toFock (mergeAs b) = toFock as + toFock b) :
    ∀ (ps : State) (pc : ℚ) (b : Vec),
      toFock (mergeInto (ps, pc) as mergeAs b) = toFock ((ps, pc) :: as) + toFock b
  | ps, pc, [] => by simp [mergeInto]
  | ps, pc, (qs, qc) :: bs => by
    rw [mergeInto]
    split
    · simp only [toFock_cons, h]
      abel
    · rename_i hc
      obtain rfl : ps = qs := stateCmp_eq hc
      split_ifs with h'
      · have h'' : pc + qc = 0 := h'
        have hz : Finsupp.single ps pc + Finsupp.single ps qc = 0 := by
          rw [← Finsupp.single_add, h'', Finsupp.single_zero]
        simp only [toFock_cons_mk, h]
        calc toFock as + toFock bs
            = (Finsupp.single ps pc + Finsupp.single ps qc) + (toFock as + toFock bs) := by
              rw [hz, zero_add]
          _ = Finsupp.single ps pc + toFock as + (Finsupp.single ps qc + toFock bs) := by abel
      · simp only [toFock_cons, h, Finsupp.single_add]
        abel
    · simp only [toFock_cons]
      rw [toFock_mergeInto as mergeAs h ps pc bs]
      simp only [toFock_cons_mk]
      abel

theorem toFock_addVec : ∀ a b : Vec, toFock (addVec a b) = toFock a + toFock b
  | [], b => by simp [addVec]
  | (ps, pc) :: as, b => by
    rw [addVec]
    exact toFock_mergeInto as (addVec as) (fun b => toFock_addVec as b) ps pc b

theorem toFock_smul (c : ℚ) (v : Vec) : toFock (smul c v) = c • toFock v := by
  unfold smul
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · induction v with
    | nil => simp
    | cons p v ih =>
      simp only [List.map_cons, toFock_cons, ih, smul_add, Finsupp.smul_single, smul_eq_mul]

theorem toFock_mergePairs : ∀ l : List Vec, ((mergePairs l).map toFock).sum = (l.map toFock).sum
  | a :: b :: rest => by
    simp only [mergePairs, List.map_cons, List.sum_cons, toFock_addVec, toFock_mergePairs rest,
      add_assoc]
  | [] => rfl
  | [_] => rfl

theorem toFock_foldr_addVec_nil : ∀ l : List Vec, toFock (l.foldr addVec []) = (l.map toFock).sum
  | [] => by simp
  | a :: l => by
    rw [List.foldr_cons, toFock_addVec, toFock_foldr_addVec_nil l, List.map_cons, List.sum_cons]

theorem toFock_mergeAll : ∀ (fuel : ℕ) (l : List Vec), toFock (mergeAll fuel l) = (l.map toFock).sum
  | 0, l => by rw [mergeAll, toFock_foldr_addVec_nil]
  | _ + 1, [] => by simp [mergeAll]
  | _ + 1, [a] => by simp [mergeAll]
  | fuel + 1, a :: b :: l => by rw [mergeAll, toFock_mergeAll fuel, toFock_mergePairs]

theorem toFock_bindVec (v : Vec) (f : State → Vec) :
    toFock (bindVec v f) = Finsupp.linearCombination ℚ (fun s => toFock (f s)) (toFock v) := by
  rw [bindVec, toFock_mergeAll, List.map_map]
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [List.map_cons, List.sum_cons, ih, toFock_cons, map_add,
      Finsupp.linearCombination_single, Function.comp_apply, toFock_smul]

theorem toFock_bindVec_cons (t : State) (c : ℚ) (v : Vec) (f : State → Vec) :
    toFock (bindVec ((t, c) :: v) f) = c • toFock (f t) + toFock (bindVec v f) := by
  rw [toFock_bindVec, toFock_bindVec, toFock_cons_mk, map_add, Finsupp.linearCombination_single]

/-! ## Modes as linear maps -/

/-- `u_(m)` as a linear map on the Fock model (linear extension of `basisMode u m`). -/
noncomputable def modeOp (u : State) (m : ℤ) : Fock →ₗ[ℚ] Fock :=
  Finsupp.linearCombination ℚ fun v => toFock (basisMode u m v)

/-- The mode `a_(m)` of `a ∈ Fock`, linear in `a`. -/
noncomputable def Y (a : Fock) (m : ℤ) : Fock →ₗ[ℚ] Fock :=
  Finsupp.linearCombination ℚ (fun u => modeOp u m) a

/-- **The list computation represents the mode.** -/
theorem toFock_mode (a : Vec) (m : ℤ) (b : Vec) :
    toFock (mode a m b) = Y (toFock a) m (toFock b) := by
  have h1 : ∀ u, toFock (bindVec b fun v => basisMode u m v) = modeOp u m (toFock b) :=
    fun u => toFock_bindVec b _
  rw [mode, toFock_bindVec]
  simp only [h1, Y, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, modeOp]

/-- A kernel-checked list identity `mode a m b = c` is the identity `a_(m) b = c` in `Fock`. -/
theorem Y_eq_of_mode_eq {a b c : Vec} {m : ℤ} (h : mode a m b = c) :
    Y (toFock a) m (toFock b) = toFock c := by
  rw [← toFock_mode, h]

/-! ## Grades -/

/-- The canonical basis monomials of grade `d`. -/
def basisStates (d : ℕ) : Set State := {s | Valid s ∧ grade s = d}

/-- The grade-`d` subspace `V_d` of the Fock model. -/
noncomputable def gradeSpace (d : ℕ) : Submodule ℚ Fock :=
  Finsupp.supported ℚ ℚ (basisStates d)

/-- The dimension of `V_d` from an explicit finite list of its basis states. -/
theorem finrank_gradeSpace_eq (d : ℕ) (F : Finset State) (h : basisStates d = ↑F) :
    Module.finrank ℚ (gradeSpace d) = F.card := by
  rw [gradeSpace, h, (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) (↑F : Set State)).finrank_eq,
    Module.finrank_finsupp_self]
  exact Fintype.card_coe F

/-- A list all of whose states are basis states of grade `d` lies in `V_d`. -/
theorem toFock_mem_gradeSpace {d : ℕ} {v : Vec} (h : ∀ p ∈ v, p.1 ∈ basisStates d) :
    toFock v ∈ gradeSpace d := by
  induction v with
  | nil => simp
  | cons p v ih =>
    rw [toFock_cons]
    exact Submodule.add_mem _ (Finsupp.single_mem_supported ℚ _ (h p List.mem_cons_self))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

#print axioms toFock_mode
#print axioms toFock_addVec
#print axioms finrank_gradeSpace_eq
#print axioms toFock_mem_gradeSpace

end LatticeVOA
end HaagerupIzumi.C8
