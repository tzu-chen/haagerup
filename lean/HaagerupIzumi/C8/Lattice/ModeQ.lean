module

public import HaagerupIzumi.C8.Lattice.PCTCore

@[expose] public section

/-!
# Modes on vectors with one `ℚ(√13, √-3)` coefficient per state

A second evaluation of the modes, for the heavy controls of the triplet (`Lattice/Benchmark.md`
§5): `Vec4.mode` (`QA.lean`) treats the four rational components separately, so it calls
`basisMode` once per (component, state) and merges sixteen partial products; `modeQ` calls
`basisMode` once per pair of *states* (one coefficient `QA` per state, `QVec`) and does not merge
(the output is a list of scaled pieces; `toVec4Q` and `sort4` normalize at the end).

* `toVQ : QVec → V`, `liftQ c v` (`c · v` for a rational vector `v`), `modeQ`.
* **Link**: `toVQ_modeQ`: `toVQ (modeQ a m b) = modeC m (toVQ a) (toVQ b)` for vectors of
  canonical states; `toV4_toVec4Q`: `toV4 (toVec4Q x) = toVQ x`.  So kernel checks stated with
  `modeQ` are statements about `modeC`, and everything built on `modeC` stays valid.

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- A sparse vector with one coefficient in `ℚ(√13, √-3)` per state. -/
abbrev QVec := List (State × QA)

/-- The vector of `V` represented by a `QVec`. -/
noncomputable def toVQ (x : QVec) : V := (x.map fun p => p.2.toC • toV [(p.1, 1)]).sum

/-- `c · v` for a rational vector `v`. -/
def liftQ (c : QA) (v : Vec) : QVec := v.map fun p => (p.1, QA.mul c (QA.ofRat p.2))

/-- `a_(m) b`: one `basisMode` per pair of states, no merging. -/
def modeQ (a : QVec) (m : ℤ) (b : QVec) : QVec :=
  a.flatMap fun p => b.flatMap fun q => liftQ (QA.mul p.2 q.2) (basisMode p.1 m q.1)

/-- The four rational components (unsorted). -/
def toVec4Q (x : QVec) : Vec4 :=
  ⟨x.map fun p => (p.1, p.2.a), x.map fun p => (p.1, p.2.b), x.map fun p => (p.1, p.2.c),
    x.map fun p => (p.1, p.2.d)⟩

theorem toVQ_nil : toVQ [] = 0 := by simp [toVQ]

theorem toVQ_cons (p : State × QA) (x : QVec) :
    toVQ (p :: x) = p.2.toC • toV [(p.1, 1)] + toVQ x := by
  simp [toVQ]

theorem toVQ_append (x y : QVec) : toVQ (x ++ y) = toVQ x + toVQ y := by
  simp [toVQ, List.map_append, List.sum_append]

theorem toVQ_flatMap {α : Type*} (f : α → QVec) :
    ∀ l : List α, toVQ (l.flatMap f) = (l.map fun p => toVQ (f p)).sum
  | [] => by simp [toVQ_nil]
  | p :: l => by rw [List.flatMap_cons, toVQ_append, toVQ_flatMap f l, List.map_cons, List.sum_cons]

theorem toV_single_state (s : State) (c : ℚ) : toV [(s, c)] = (c : ℂ) • toV [(s, 1)] := by
  rw [toV_cons_mk, toV_cons_mk, toV_nil, add_zero, add_zero, Finsupp.smul_single, smul_eq_mul,
    Rat.cast_one, mul_one]

theorem toVQ_liftQ (c : QA) : ∀ v : Vec, toVQ (liftQ c v) = c.toC • toV v
  | [] => by simp [liftQ, toVQ_nil]
  | (s, r) :: v => by
    have ih := toVQ_liftQ c v
    have e1 : toV [(s, 1)] = Finsupp.single (canon s) 1 := by
      rw [toV_cons_mk, toV_nil, add_zero, Rat.cast_one]
    show toVQ ((s, QA.mul c (QA.ofRat r)) :: liftQ c v) = c.toC • toV ((s, r) :: v)
    rw [toVQ_cons, ih]
    show (QA.mul c (QA.ofRat r)).toC • toV [(s, 1)] + c.toC • toV v = c.toC • toV ((s, r) :: v)
    rw [QA.toC_mul, QA.toC_ofRat, toV_cons_mk s r v, e1, smul_add, Finsupp.smul_single,
      Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]

theorem toV_single_valid {s : State} (hs : Valid s) : toV [(s, 1)] = Finsupp.single ⟨s, hs⟩ 1 := by
  rw [toV_cons_mk, toV_nil, add_zero, canon_of_valid hs, Rat.cast_one]

theorem modeC_single_states {s t : State} (hs : Valid s) (ht : Valid t) (m : ℤ) :
    modeC m (toV [(s, 1)]) (toV [(t, 1)]) = toV (basisMode s m t) := by
  rw [toV_single_valid hs, toV_single_valid ht, modeC_single, one_mul, one_smul]

theorem toVQ_modeQ_single {s : State} (hs : Valid s) (c : QA) (m : ℤ) :
    ∀ b : QVec, (∀ q ∈ b, Valid q.1) →
      toVQ (b.flatMap fun q => liftQ (QA.mul c q.2) (basisMode s m q.1)) =
        c.toC • modeC m (toV [(s, 1)]) (toVQ b)
  | [], _ => by simp [toVQ_nil]
  | q :: b, hb => by
    have ih := toVQ_modeQ_single hs c m b fun r hr => hb r (List.mem_cons_of_mem _ hr)
    rw [List.flatMap_cons, toVQ_append, ih, toVQ_liftQ, toVQ_cons, map_add, map_smul,
      modeC_single_states hs (hb q List.mem_cons_self), QA.toC_mul, smul_add, smul_smul]

/-- **Link**: `modeQ` computes `modeC` on vectors of canonical states. -/
theorem toVQ_modeQ (m : ℤ) : ∀ a b : QVec, (∀ p ∈ a, Valid p.1) → (∀ q ∈ b, Valid q.1) →
    toVQ (modeQ a m b) = modeC m (toVQ a) (toVQ b)
  | [], b, _, _ => by simp [modeQ, toVQ_nil]
  | p :: a, b, ha, hb => by
    have ih := toVQ_modeQ m a b (fun r hr => ha r (List.mem_cons_of_mem _ hr)) hb
    have h1 := toVQ_modeQ_single (ha p List.mem_cons_self) p.2 m b hb
    simp only [modeQ] at ih ⊢
    rw [List.flatMap_cons, toVQ_append, h1, ih, toVQ_cons, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]

/-- **Link**: the four rational components of a `QVec` represent the same vector. -/
theorem toV4_toVec4Q : ∀ x : QVec, toV4 (toVec4Q x) = toVQ x
  | [] => by simp [toV4, toVec4Q, toVQ_nil]
  | p :: x => by
    have ih := toV4_toVec4Q x
    simp only [toV4, toVec4Q, List.map_cons] at ih ⊢
    have e1 : toV [(p.1, 1)] = Finsupp.single (canon p.1) 1 := by
      rw [toV_cons_mk, toV_nil, add_zero, Rat.cast_one]
    have hs : ∀ r : ℚ, Finsupp.single (canon p.1) (r : ℂ) = (r : ℂ) • Finsupp.single (canon p.1) 1 :=
      fun r => by rw [Finsupp.smul_single_one]
    rw [toV_cons_mk, toV_cons_mk, toV_cons_mk, toV_cons_mk, toVQ_cons, ← ih, e1, hs p.2.a, hs p.2.b,
      hs p.2.c, hs p.2.d]
    simp only [QA.toC]
    module

#print axioms toVQ_modeQ
#print axioms toV4_toVec4Q

end LatticeVOA
end HaagerupIzumi.C8
