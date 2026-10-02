module

public import HaagerupIzumi.C8.Lattice.Semantic
public import HaagerupIzumi.C8.Lattice.Roots
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `dim B₁ = 86` and `dim K = 6` in the Fock model, by kernel computation

Work item W1 of `C8/ROADMAP.md`: the two dimension facts of the `certDimensions` node of the
proof map (`ProofMapProperness.concreteNodes`: `Module.finrank k D.K = 6`,
`Module.finrank k (A.grade 1) = 86`; the node also contains `IsSl2SumSpan A D.K`), proved for the
rational Fock model of `B = V_{E₆ ⊕ A₂}` of `Lattice/Semantic.lean` (manuscript
`c8_expanded_20260929/haagerup_c8_expanded.tex`: `dim B₁ = 86` at line 222, the weight formula
at line 1890, the currents `eq:leftcurrents`, `eq:rightcurrents` at lines 1910–1930).

* `norm_eq_two_iff` (`Lattice/Roots.lean`): the norm-two vectors of `L = E₆ ⊕ A₂` are exactly
  the 78 vectors of the list `roots`.
* `finrank_gradeSpace_one`: the grade-one space `V₁` of the Fock model (canonical monomials
  `hᵢ(-1)e⁰` and `e^α`, `(α,α) = 2`) has dimension `8 + 78 = 86` (`basisStates_one`).
* `finrank_K`: the six currents `H_L, E_L, F_L, H_R, E_R, F_R` (`Lattice/Data.lean`, exported
  from the Python engine) are linearly independent, so their span `K` has dimension `6`;
  `K_le_gradeSpace_one`: `K ⊆ V₁`.
* `certDimensions_model`: both dimension facts together for the rational model.  The full
  `certDimensions` node (with `IsSl2SumSpan`) for the lattice vertex operator algebra over `ℂ`
  is `certDimensions_lattice` in `Lattice/VOA.lean`.

Relation to the proof map: `concreteNodes` states `certDimensions` for an abstract
`A : VertexOperatorAlgebra k V` with `A.grade 1` and `D.K = span {hL, …, fR}`.  Here `V` is
`Fock = State →₀ ℚ`, `A.grade 1` is `gradeSpace 1` and `D.K` is `K` (`K_eq_span` gives the same
set-literal form as `ClosureData.K`).  The model is not yet a `VertexOperatorAlgebra` (the
Borcherds identity is W3); `Lattice/VOA.lean` builds the `VertexOperatorAlgebra` on the
canonical-monomial model `V` over `ℂ` from the single hypothesis `FLMInput` and proves the node
there.  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

-- Sequential elaboration keeps the kernel evaluations from running concurrently (memory).
set_option Elab.async false

/-! ## The grade-one space -/

/-- The 86 canonical monomials of grade one: `hᵢ(-1) e⁰` and `e^α` for the roots `α`. -/
def gradeOneStates : List State :=
  (List.range 8).map (fun i => (Mom.zero, [i])) ++ roots.map (fun r => (r, []))

theorem gradeOneStates_spec : ∀ s ∈ gradeOneStates, Valid s ∧ grade s = 1 := by
  decide +kernel

theorem gradeOneStates_nodup : gradeOneStates.Nodup := by
  rw [gradeOneStates, List.nodup_append]
  refine ⟨by decide +kernel, roots_nodup.map fun a b h => congrArg Prod.fst h, ?_⟩
  intro x hx y hy hxy
  rw [List.mem_map] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨r, -, rfl⟩ := hy
  exact absurd (congrArg Prod.snd hxy) (by simp)

theorem gradeOneStates_length : gradeOneStates.length = 86 := by
  simp [gradeOneStates, roots_length]

theorem mem_gradeOneStates {s : State} (hg : grade s = 1) : s ∈ gradeOneStates := by
  obtain ⟨β, osc⟩ := s
  obtain ⟨q, hq⟩ := Mom.norm_even β
  have hq0 : 0 ≤ q := by
    have := Mom.norm_nonneg β
    omega
  simp only [grade] at hg
  rw [hq] at hg
  simp only [gradeOneStates, List.mem_append, List.mem_map, List.mem_range]
  rcases osc with _ | ⟨k, ks⟩
  · simp only [oscGrade] at hg
    have h2 : β.norm = 2 := by omega
    exact Or.inr ⟨β, (norm_eq_two_iff β).1 h2, rfl⟩
  · simp only [oscGrade] at hg
    have hks : oscGrade ks = 0 := by omega
    have hk : k < 8 := by omega
    have hβ : β = Mom.zero := Mom.eq_zero_of_norm_eq_zero (by omega)
    have hks' : ks = [] := by
      cases ks with
      | nil => rfl
      | cons j js =>
        simp only [oscGrade] at hks
        omega
    subst hβ hks'
    exact Or.inl ⟨k, hk, rfl⟩

/-- The grade-one basis states are exactly the 86 listed ones. -/
theorem basisStates_one : basisStates 1 = ↑gradeOneStates.toFinset := by
  ext s
  simp only [basisStates, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
  exact ⟨fun h => mem_gradeOneStates h.2, fun h => gradeOneStates_spec s h⟩

/-- **`dim V₁ = 86`** for the Fock model of `V_{E₆ ⊕ A₂}`. -/
theorem finrank_gradeSpace_one : Module.finrank ℚ (gradeSpace 1) = 86 := by
  rw [finrank_gradeSpace_eq 1 _ basisStates_one, List.toFinset_card_of_nodup gradeOneStates_nodup,
    gradeOneStates_length]

/-! ## The current space `K` -/

/-- The six currents `(H_L, E_L, F_L, H_R, E_R, F_R)` as sparse vectors. -/
def currentVec : Fin 6 → Vec
  | 0 => hL
  | 1 => eL
  | 2 => fL
  | 3 => hR
  | 4 => eR
  | 5 => fR

/-- The six currents in the Fock model. -/
noncomputable def currentFock (i : Fin 6) : Fock := toFock (currentVec i)

/-- The current space `K = span {H_L, E_L, F_L, H_R, E_R, F_R}`. -/
noncomputable def K : Submodule ℚ Fock := Submodule.span ℚ (Set.range currentFock)

theorem range_currentFock : Set.range currentFock =
    {toFock hL, toFock eL, toFock fL, toFock hR, toFock eR, toFock fR} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

/-- `K` in the set-literal form of `ClosureData.K`. -/
theorem K_eq_span : K = Submodule.span ℚ
    ({toFock hL, toFock eL, toFock fL, toFock hR, toFock eR, toFock fR} : Set Fock) := by
  rw [K, range_currentFock]

/-- Coefficients of the currents at six test states (kernel evaluation). -/
theorem current_coeffs :
    (coeffOf hL (S 0 0 0 0 0 0 0 0 [0]) = -1 ∧ coeffOf eL (S 0 0 0 0 0 0 0 0 [0]) = 0 ∧
      coeffOf fL (S 0 0 0 0 0 0 0 0 [0]) = 0 ∧ coeffOf hR (S 0 0 0 0 0 0 0 0 [0]) = 5 ∧
      coeffOf eR (S 0 0 0 0 0 0 0 0 [0]) = 0 ∧ coeffOf fR (S 0 0 0 0 0 0 0 0 [0]) = 0) ∧
    (coeffOf hL (S 0 0 0 0 0 0 0 0 [1]) = -2 ∧ coeffOf eL (S 0 0 0 0 0 0 0 0 [1]) = 0 ∧
      coeffOf fL (S 0 0 0 0 0 0 0 0 [1]) = 0 ∧ coeffOf hR (S 0 0 0 0 0 0 0 0 [1]) = 8 ∧
      coeffOf eR (S 0 0 0 0 0 0 0 0 [1]) = 0 ∧ coeffOf fR (S 0 0 0 0 0 0 0 0 [1]) = 0) ∧
    (coeffOf hL (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) = 0 ∧
      coeffOf eL (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) = 1 ∧
      coeffOf fL (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) = 0 ∧
      coeffOf hR (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) = 0 ∧
      coeffOf eR (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) = 0 ∧
      coeffOf fR (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) = 0) ∧
    (coeffOf hL (S 1 2 3 2 1 2 0 0 []) = 0 ∧ coeffOf eL (S 1 2 3 2 1 2 0 0 []) = 0 ∧
      coeffOf fL (S 1 2 3 2 1 2 0 0 []) = -1 ∧ coeffOf hR (S 1 2 3 2 1 2 0 0 []) = 0 ∧
      coeffOf eR (S 1 2 3 2 1 2 0 0 []) = 0 ∧ coeffOf fR (S 1 2 3 2 1 2 0 0 []) = 0) ∧
    (coeffOf hL (S 1 0 0 0 0 0 0 0 []) = 0 ∧ coeffOf eL (S 1 0 0 0 0 0 0 0 []) = 0 ∧
      coeffOf fL (S 1 0 0 0 0 0 0 0 []) = 0 ∧ coeffOf hR (S 1 0 0 0 0 0 0 0 []) = 0 ∧
      coeffOf eR (S 1 0 0 0 0 0 0 0 []) = 1 ∧ coeffOf fR (S 1 0 0 0 0 0 0 0 []) = 0) ∧
    (coeffOf hL (S (-1) 0 0 0 0 0 0 0 []) = 0 ∧ coeffOf eL (S (-1) 0 0 0 0 0 0 0 []) = 0 ∧
      coeffOf fL (S (-1) 0 0 0 0 0 0 0 []) = 0 ∧ coeffOf hR (S (-1) 0 0 0 0 0 0 0 []) = 0 ∧
      coeffOf eR (S (-1) 0 0 0 0 0 0 0 []) = 0 ∧ coeffOf fR (S (-1) 0 0 0 0 0 0 0 []) = -5) := by
  decide +kernel

/-- The six currents are linearly independent. -/
theorem currentFock_linearIndependent : LinearIndependent ℚ currentFock := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have ev : ∀ s : State, g 0 * coeffOf hL s + g 1 * coeffOf eL s + g 2 * coeffOf fL s +
      g 3 * coeffOf hR s + g 4 * coeffOf eR s + g 5 * coeffOf fR s = 0 := by
    intro s
    have h := congrArg (fun F : Fock => F s) hg
    simpa [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, currentFock,
      toFock_apply, Fin.sum_univ_six, currentVec] using h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5, d6⟩, ⟨e1, e2, e3, e4, e5, e6⟩, ⟨f1, f2, f3, f4, f5, f6⟩⟩ :=
    current_coeffs
  have q0 := ev (S 0 0 0 0 0 0 0 0 [0])
  have q1 := ev (S 0 0 0 0 0 0 0 0 [1])
  have q2 := ev (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 [])
  have q3 := ev (S 1 2 3 2 1 2 0 0 [])
  have q4 := ev (S 1 0 0 0 0 0 0 0 [])
  have q5 := ev (S (-1) 0 0 0 0 0 0 0 [])
  rw [a1, a2, a3, a4, a5, a6] at q0
  rw [b1, b2, b3, b4, b5, b6] at q1
  rw [c1, c2, c3, c4, c5, c6] at q2
  rw [d1, d2, d3, d4, d5, d6] at q3
  rw [e1, e2, e3, e4, e5, e6] at q4
  rw [f1, f2, f3, f4, f5, f6] at q5
  have g0 : g 0 = 0 := by linarith
  have g1 : g 1 = 0 := by linarith
  have g2 : g 2 = 0 := by linarith
  have g3 : g 3 = 0 := by linarith
  have g4 : g 4 = 0 := by linarith
  have g5 : g 5 = 0 := by linarith
  intro i
  fin_cases i <;> assumption

/-- **`dim K = 6`.** -/
theorem finrank_K : Module.finrank ℚ K = 6 := by
  rw [K, finrank_span_eq_card currentFock_linearIndependent, Fintype.card_fin]

theorem currents_basisStates : ∀ i : Fin 6, ∀ p ∈ currentVec i, Valid p.1 ∧ grade p.1 = 1 := by
  decide +kernel

/-- The currents have weight one: `K ⊆ V₁`. -/
theorem K_le_gradeSpace_one : K ≤ gradeSpace 1 := by
  rw [K, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact toFock_mem_gradeSpace fun p hp => currents_basisStates i p hp

/-- **The dimension facts of `certDimensions` for the rational Fock model**: `dim K = 6` and
`dim V₁ = 86` (the full node, with `IsSl2SumSpan`, is `certDimensions_lattice`). -/
theorem certDimensions_model :
    Module.finrank ℚ K = 6 ∧ Module.finrank ℚ (gradeSpace 1) = 86 :=
  ⟨finrank_K, finrank_gradeSpace_one⟩

#print axioms finrank_gradeSpace_one
#print axioms finrank_K
#print axioms K_le_gradeSpace_one
#print axioms certDimensions_model

end LatticeVOA
end HaagerupIzumi.C8
