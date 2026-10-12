module

public import HaagerupIzumi.C8.Lattice.P4Cartan

@[expose] public section

/-!
# Integer Cartan eigenvalues

The eigenvalues of the Cartan currents `H_L`, `H_R` (`Lattice/Data.lean`) on a monomial of
momentum `β` are the integer linear forms `eigZ hLZ β`, `eigZ hRZ β`
(`cartanEig_hL`, `cartanEig_hR`), so the state checks of the triplet data (`P4St*.lean`) need no
rational arithmetic.  `P4Good μ s`: `s` canonical of grade four with eigenvalues `(0, μ)`.
No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- `∑ cᵢ (αᵢ, β)` for integer coefficients. -/
def eigZ (cs : List (ℕ × ℤ)) (β : Mom) : ℤ := (cs.map fun p => p.2 * Mom.pairSimple p.1 β).sum

/-- The coefficients of `H_L`. -/
def hLZ : List (ℕ × ℤ) := [(0, -1), (1, -2), (2, -3), (3, -2), (4, -1), (5, -2)]

/-- The coefficients of `H_R`. -/
def hRZ : List (ℕ × ℤ) := [(0, 5), (1, 8), (2, 9), (3, 8), (4, 5), (6, 2), (7, 2)]

theorem cartanEig_hL (β : Mom) : cartanEig hL β = eigZ hLZ β := by
  simp only [cartanEig, eigZ, hL, hLZ, S, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.headD_cons]
  push_cast
  ring

theorem cartanEig_hR (β : Mom) : cartanEig hR β = eigZ hRZ β := by
  simp only [cartanEig, eigZ, hR, hRZ, S, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.headD_cons]
  push_cast
  ring

/-- A canonical grade-four monomial with Cartan eigenvalues `(0, μ)`. -/
def P4Good (μ : ℤ) (s : State) : Prop :=
  Valid s ∧ grade s = 4 ∧ eigZ hLZ s.1 = 0 ∧ eigZ hRZ s.1 = μ

instance (μ : ℤ) (s : State) : Decidable (P4Good μ s) :=
  inferInstanceAs (Decidable (Valid s ∧ grade s = 4 ∧ eigZ hLZ s.1 = 0 ∧ eigZ hRZ s.1 = μ))

theorem P4Good.cartan {x : Vec4} {μ : ℤ} (h : x.AllStates (P4Good μ)) :
    (x.AllStates fun s => Valid s ∧ cartanEig hL s.1 = ((0 : ℤ) : ℚ)) ∧
      (x.AllStates fun s => Valid s ∧ cartanEig hR s.1 = (μ : ℚ)) ∧
      x.AllStates fun s => Valid s ∧ grade s = 4 := by
  have key : ∀ v : Vec, (∀ p ∈ v, P4Good μ p.1) →
      (∀ p ∈ v, Valid p.1 ∧ cartanEig hL p.1.1 = ((0 : ℤ) : ℚ)) ∧
      (∀ p ∈ v, Valid p.1 ∧ cartanEig hR p.1.1 = (μ : ℚ)) ∧
      ∀ p ∈ v, Valid p.1 ∧ grade p.1 = 4 := fun v hv =>
    ⟨fun p hp => ⟨(hv p hp).1, by rw [cartanEig_hL, (hv p hp).2.2.1]⟩,
      fun p hp => ⟨(hv p hp).1, by rw [cartanEig_hR, (hv p hp).2.2.2]⟩,
      fun p hp => ⟨(hv p hp).1, (hv p hp).2.1⟩⟩
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨a0, b0, c0⟩ := key _ h0
  obtain ⟨a1, b1, c1⟩ := key _ h1
  obtain ⟨a2, b2, c2⟩ := key _ h2
  obtain ⟨a3, b3, c3⟩ := key _ h3
  exact ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩⟩

/-! ## Checking each state once -/

/-- `l₁ ⊆ l₂` for lists sorted by `stateCmp` (merge walk, structural in `l₂`). -/
def subsetSorted : List State → List State → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    match stateCmp a b with
    | .eq => subsetSorted as bs
    | .gt => subsetSorted (a :: as) bs
    | .lt => false

theorem subsetSorted_sound :
    ∀ (l₂ l₁ : List State), subsetSorted l₁ l₂ = true → ∀ s ∈ l₁, s ∈ l₂
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [subsetSorted] at h
  | _ :: _, [], _ => by simp
  | b :: bs, a :: as, h => by
    intro s hs
    cases hc : stateCmp a b with
    | lt => simp [subsetSorted, hc] at h
    | eq =>
      simp only [subsetSorted, hc] at h
      have hab := stateCmp_eq hc
      rcases List.mem_cons.1 hs with rfl | hs'
      · rw [hab]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (subsetSorted_sound bs as h s hs')
    | gt =>
      simp only [subsetSorted, hc] at h
      exact List.mem_cons_of_mem _ (subsetSorted_sound bs (a :: as) h s hs)

/-- A property of all states of `x`, from the states of the component `c1` (which carries every
state of the triplet data) and sorted inclusions of the other components. -/
theorem allStates_of_c1 {P : State → Prop} {x : Vec4} (h1 : ∀ p ∈ x.c1, P p.1)
    (h0 : subsetSorted (x.c0.map Prod.fst) (x.c1.map Prod.fst) = true)
    (h2 : subsetSorted (x.c2.map Prod.fst) (x.c1.map Prod.fst) = true)
    (h3 : subsetSorted (x.c3.map Prod.fst) (x.c1.map Prod.fst) = true) : x.AllStates P := by
  have key : ∀ v : Vec, subsetSorted (v.map Prod.fst) (x.c1.map Prod.fst) = true →
      ∀ p ∈ v, P p.1 := by
    intro v hv p hp
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1
      (subsetSorted_sound _ _ hv p.1 (List.mem_map.2 ⟨p, hp, rfl⟩))
    rw [← hqe]
    exact h1 q hq
  exact ⟨key _ h0, h1, key _ h2, key _ h3⟩

end LatticeVOA
end HaagerupIzumi.C8
