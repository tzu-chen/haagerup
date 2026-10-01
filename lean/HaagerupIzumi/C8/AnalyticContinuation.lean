module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-!
# Continuation of the insertion form (Lemma `lem:analytic-insertion-continuation`)

Lemma `lem:analytic-insertion-continuation` (lines 4697–4735 of the expanded draft) puts
`Ω = int(cl O_in ∪ cl O_out)` and argues: "Every component of `Ω` meets `O_in ∪ O_out`.
Indeed, its complement inside `Ω` is contained in the union of the two boundaries; boundaries
of open sets are closed with empty interior, and a finite union of such sets contains no
nonempty open component.  The identity theorem therefore extends the equality across every
component."

This file proves that argument for scalar holomorphic functions (each matrix coefficient of
the insertion operators is one):

* `interior_union_eq_empty` — a union of two closed sets with empty interior has empty
  interior;
* `open_subset_meets` — every nonempty open subset of `Ω` meets `O_in ∪ O_out`;
* `continuation` — two functions analytic on `Ω` that agree on `(O_in ∪ O_out) ∩ Ω` agree on
  all of `Ω`.

The facts that the formal Laurent pairing and the geometric matrix coefficient are holomorphic
on `Ω` and agree on the two interiors (Henriques–Tener sewing and point insertion) are the
inputs.
-/

namespace HaagerupIzumi.C8.AnalyticContinuation

open Set Topology Filter

/-- A union of two closed sets with empty interior has empty interior. -/
theorem interior_union_eq_empty {X : Type*} [TopologicalSpace X] {F₁ F₂ : Set X}
    (h₁ : IsClosed F₁) (e₁ : interior F₁ = ∅) (e₂ : interior F₂ = ∅) :
    interior (F₁ ∪ F₂) = ∅ := by
  set W := interior (F₁ ∪ F₂)
  have hW : IsOpen W := isOpen_interior
  have h1 : W \ F₁ ⊆ interior F₂ := by
    apply interior_maximal _ (hW.sdiff h₁)
    intro x hx
    rcases interior_subset hx.1 with h | h
    · exact absurd h hx.2
    · exact h
  rw [e₂] at h1
  have h2 : W ⊆ interior F₁ := by
    apply interior_maximal _ hW
    intro x hx
    by_contra h
    exact h1 ⟨hx, h⟩
  rw [e₁] at h2
  exact subset_eq_empty h2 rfl

/-- The boundary of an open set has empty interior. -/
theorem interior_frontier_of_isOpen {X : Type*} [TopologicalSpace X] {O : Set X}
    (hO : IsOpen O) : interior (frontier O) = ∅ := by
  rw [← frontier_compl]
  exact interior_frontier hO.isClosed_compl

/-- **Every nonempty open subset of `Ω = int(cl O₁ ∪ cl O₂)` meets `O₁ ∪ O₂`.** -/
theorem open_subset_meets {X : Type*} [TopologicalSpace X] {O₁ O₂ W : Set X}
    (ho₁ : IsOpen O₁) (ho₂ : IsOpen O₂) (hW : IsOpen W)
    (hWΩ : W ⊆ interior (closure O₁ ∪ closure O₂)) (hne : W.Nonempty) :
    (W ∩ (O₁ ∪ O₂)).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hsub : W ⊆ frontier O₁ ∪ frontier O₂ := by
    intro x hx
    have hnot : x ∉ O₁ ∪ O₂ := by
      intro h
      have hx' : x ∈ W ∩ (O₁ ∪ O₂) := ⟨hx, h⟩
      rw [hempty] at hx'
      exact hx'
    rcases interior_subset (hWΩ hx) with h | h
    · left
      rw [ho₁.frontier_eq]
      exact ⟨h, fun h' => hnot (Or.inl h')⟩
    · right
      rw [ho₂.frontier_eq]
      exact ⟨h, fun h' => hnot (Or.inr h')⟩
  have hint : interior (frontier O₁ ∪ frontier O₂) = ∅ :=
    interior_union_eq_empty isClosed_frontier (interior_frontier_of_isOpen ho₁)
      (interior_frontier_of_isOpen ho₂)
  have hWint : W ⊆ interior (frontier O₁ ∪ frontier O₂) := interior_maximal hsub hW
  rw [hint] at hWint
  obtain ⟨x, hx⟩ := hne
  exact hWint hx

/-- **Lemma `lem:analytic-insertion-continuation`, identity-theorem step.**  Two functions
analytic on `Ω = int(cl O₁ ∪ cl O₂)` that agree on `(O₁ ∪ O₂) ∩ Ω` agree on all of `Ω`. -/
theorem continuation {f g : ℂ → ℂ} {O₁ O₂ : Set ℂ} (ho₁ : IsOpen O₁) (ho₂ : IsOpen O₂)
    (hf : AnalyticOnNhd ℂ f (interior (closure O₁ ∪ closure O₂)))
    (hg : AnalyticOnNhd ℂ g (interior (closure O₁ ∪ closure O₂)))
    (hfg : EqOn f g ((O₁ ∪ O₂) ∩ interior (closure O₁ ∪ closure O₂))) :
    EqOn f g (interior (closure O₁ ∪ closure O₂)) := by
  set Ω := interior (closure O₁ ∪ closure O₂)
  intro z hz
  set C := connectedComponentIn Ω z
  have hCopen : IsOpen C := isOpen_interior.connectedComponentIn
  have hCsub : C ⊆ Ω := connectedComponentIn_subset Ω z
  have hzC : z ∈ C := mem_connectedComponentIn hz
  obtain ⟨w, hwC, hwO⟩ := open_subset_meets ho₁ ho₂ hCopen hCsub ⟨z, hzC⟩
  have hev : f =ᶠ[𝓝 w] g := by
    have hopen : IsOpen (C ∩ (O₁ ∪ O₂)) := hCopen.inter (ho₁.union ho₂)
    filter_upwards [hopen.mem_nhds ⟨hwC, hwO⟩] with y hy
    exact hfg ⟨hy.2, hCsub hy.1⟩
  exact (hf.mono hCsub).eqOn_of_preconnected_of_eventuallyEq (hg.mono hCsub)
    isPreconnected_connectedComponentIn hwC hev hzC

#print axioms continuation

end HaagerupIzumi.C8.AnalyticContinuation
