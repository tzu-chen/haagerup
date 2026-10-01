module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# The finite positive conformal-vector identity (eq:finite-positive-stress)

Appendix F (lines 2688–2721 of the expanded draft) replaces the Haar averages
`p̄, z̄` in the positive stress identity

  `ω_U = ω_{A₁,₁} + (3403/4563) ω_{A₁,₃₉} + (25/6) p̄ + (25/26) z̄`   (eq:positive-stress)

by finite convex combinations of conjugate conformal vectors:
"The compact orbit of a conformal vector has compact convex hull in the real space of
PCT-fixed weight-two vectors.  Its Haar average belongs to that hull.  Carathéodory's
theorem therefore replaces each average by a finite convex combination of orbit points."

This file proves those three sentences in a finite-dimensional real normed space `E`:

* `isCompact_convexHull` — the convex hull of a compact set is compact
  (via Carathéodory; this is not in Mathlib);
* `integral_mem_convexHull` — the average of a map into a compact set `K` against a
  probability measure lies in `convexHull K` (applied to the Haar probability measure of the
  compact current group and the orbit map of a conformal vector);
* `finite_positive_combination` — `ω = ∑_k a_k avg_k` with `a_k > 0` and
  `avg_k ∈ convexHull K_k` gives `ω = ∑_i c_i z_i` with `c_i > 0`, `z_i ∈ K_{k(i)}`;
* `positive_stress_coefficients` — the four coefficients of eq:positive-stress are positive.

The identity eq:positive-stress itself (its exact coefficients inside `S₂`) is the
certificate input `pf13_membership_replay` of Certificate `cert:structural-inputs`; the
continuity of the orbit map and the existence of the Haar probability measure are standard.
-/

namespace HaagerupIzumi.C8.PositiveStress

open MeasureTheory Set

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private lemma sum_extend_eq {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (e : ι ↪ κ) (f : κ → M) (hf : ∀ j, j ∉ Set.range e → f j = 0) :
    ∑ j, f j = ∑ i, f (e i) := by
  classical
  rw [← Finset.sum_map Finset.univ e f]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hf
  rintro ⟨i, rfl⟩
  exact hj (Finset.mem_map_of_mem e (Finset.mem_univ i))

/-- Carathéodory with a fixed number of points: every point of `convexHull K` is a convex
combination of `finrank E + 1` points of `K` (padding with a fixed point `k₀ ∈ K`). -/
theorem exists_fin_combination {K : Set E} {k₀ : E} (hk₀ : k₀ ∈ K) {x : E}
    (hx : x ∈ convexHull ℝ K) :
    ∃ p : Fin (Module.finrank ℝ E + 1) → E,
      ∃ w ∈ stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)), (∀ i, p i ∈ K) ∧ ∑ i, w i • p i = x := by
  classical
  obtain ⟨ι, _, z, w, hzK, hai, hwpos, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
      Submodule.finrank_le _
    omega
  let e : ι ↪ Fin (Module.finrank ℝ E + 1) :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  let p : Fin (Module.finrank ℝ E + 1) → E := Function.extend e z fun _ => k₀
  let w' : Fin (Module.finrank ℝ E + 1) → ℝ := Function.extend e w 0
  have hp_e : ∀ i, p (e i) = z i := fun i => e.injective.extend_apply _ _ _
  have hw_e : ∀ i, w' (e i) = w i := fun i => e.injective.extend_apply _ _ _
  have hp_off : ∀ j, j ∉ Set.range e → p j = k₀ := fun j hj => Function.extend_apply' _ _ _ hj
  have hw_off : ∀ j, j ∉ Set.range e → w' j = 0 := fun j hj => Function.extend_apply' _ _ _ hj
  refine ⟨p, w', ⟨fun j => ?_, ?_⟩, fun j => ?_, ?_⟩
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [hw_e]
      exact (hwpos i).le
    · rw [hw_off j hj]
  · rw [sum_extend_eq e w' hw_off]
    simp only [hw_e]
    exact hw1
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [hp_e]
      exact hzK ⟨i, rfl⟩
    · rw [hp_off j hj]
      exact hk₀
  · rw [sum_extend_eq e (fun j => w' j • p j) (fun j hj => by simp [hw_off j hj])]
    simp only [hw_e, hp_e]
    exact hwx

/-- The convex hull of a compact set in a finite-dimensional real normed space is compact. -/
theorem isCompact_convexHull {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp
  let N := Module.finrank ℝ E + 1
  let S : Set ((Fin N → E) × (Fin N → ℝ)) :=
    (Set.univ.pi fun _ => K) ×ˢ stdSimplex ℝ (Fin N)
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => hK).prod (isCompact_stdSimplex ℝ (Fin N))
  let Φ : (Fin N → E) × (Fin N → ℝ) → E := fun pw => ∑ i, pw.2 i • pw.1 i
  have hΦ : Continuous Φ := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((continuous_apply i).comp continuous_snd).smul ((continuous_apply i).comp continuous_fst)
  have hEq : convexHull ℝ K = Φ '' S := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, w, hw, hpK, hpx⟩ := exists_fin_combination hk₀ hx
      exact ⟨(p, w), ⟨fun i _ => hpK i, hw⟩, hpx⟩
    · rintro ⟨⟨p, w⟩, ⟨hp, hw⟩, rfl⟩
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) (by simpa using hw.2)
        (fun i _ => subset_convexHull ℝ K (hp i (mem_univ i)))
  rw [hEq]
  exact hS.image hΦ

/-- The average of a map into a compact set `K` against a probability measure lies in the
convex hull of `K` (the Haar average of an orbit lies in the hull of the orbit). -/
theorem integral_mem_convexHull {G : Type*} [MeasurableSpace G] {μ : Measure G}
    [IsProbabilityMeasure μ] {f : G → E} (hf : Integrable f μ) {K : Set E} (hK : IsCompact K)
    (hfK : ∀ g, f g ∈ K) : (∫ g, f g ∂μ) ∈ convexHull ℝ K :=
  (convex_convexHull ℝ K).integral_mem (isCompact_convexHull hK).isClosed
    (Filter.Eventually.of_forall fun g => subset_convexHull ℝ K (hfK g)) hf

/-- eq:finite-positive-stress.  If `ω = ∑_k a_k avg_k` with every `a_k > 0`, and each
`avg_k` lies in the convex hull of `K_k`, then `ω` is a finite combination, with strictly
positive coefficients, of points of the sets `K_k`. -/
theorem finite_positive_combination {κ : Type u} [Fintype κ] (a : κ → ℝ) (ha : ∀ k, 0 < a k)
    (avg : κ → E) (K : κ → Set E) (havg : ∀ k, avg k ∈ convexHull ℝ (K k)) (ω : E)
    (hω : ω = ∑ k, a k • avg k) :
    ∃ (ι : Type u) (_ : Fintype ι) (z : ι → E) (c : ι → ℝ) (src : ι → κ),
      (∀ i, z i ∈ K (src i)) ∧ (∀ i, 0 < c i) ∧ ω = ∑ i, c i • z i := by
  classical
  choose ι hfin z w hzK _ hwpos _ hwx using fun k => eq_pos_convex_span_of_mem_convexHull (havg k)
  letI : ∀ k, Fintype (ι k) := hfin
  refine ⟨Σ k, ι k, inferInstance, fun i => z i.1 i.2, fun i => a i.1 * w i.1 i.2,
    fun i => i.1, fun i => hzK i.1 ⟨i.2, rfl⟩, fun i => mul_pos (ha i.1) (hwpos i.1 i.2), ?_⟩
  rw [hω, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hwx k, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

/-- The Haar-averaged identity and its finite form, packaged: a finite-dimensional real
space, a family of probability-measure averages of maps into compact sets, and positive
weights give a finite positive combination of points of those compact sets. -/
theorem average_identity_finite {κ : Type u} [Fintype κ] {G : κ → Type*}
    [∀ k, MeasurableSpace (G k)] (μ : ∀ k, Measure (G k)) [∀ k, IsProbabilityMeasure (μ k)]
    (f : ∀ k, G k → E) (hf : ∀ k, Integrable (f k) (μ k)) (K : κ → Set E)
    (hK : ∀ k, IsCompact (K k)) (hfK : ∀ k g, f k g ∈ K k) (a : κ → ℝ) (ha : ∀ k, 0 < a k)
    (ω : E) (hω : ω = ∑ k, a k • ∫ g, f k g ∂(μ k)) :
    ∃ (ι : Type u) (_ : Fintype ι) (z : ι → E) (c : ι → ℝ) (src : ι → κ),
      (∀ i, z i ∈ K (src i)) ∧ (∀ i, 0 < c i) ∧ ω = ∑ i, c i • z i :=
  finite_positive_combination a ha _ K
    (fun k => integral_mem_convexHull (hf k) (hK k) (hfK k)) ω hω

/-- The coefficients `1, 3403/4563, 25/6, 25/26` of eq:positive-stress are positive. -/
theorem positive_stress_coefficients :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 3403 / 4563 ∧ (0 : ℝ) < 25 / 6 ∧ (0 : ℝ) < 25 / 26 := by
  norm_num

#print axioms isCompact_convexHull
#print axioms finite_positive_combination
#print axioms average_identity_finite

end HaagerupIzumi.C8.PositiveStress
