module

public import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Geometry.Manifold.Notation

@[expose] public section

/-! # Pole cancellation for vector-valued modular functions (`lem:pole-cancellation`)

This file proves Lemma `lem:pole-cancellation` (`haagerup_c8_expanded.tex`, lines
3599–3612):

> Let `σ` be a finite-image representation of `SL₂(ℤ)` with no invariant vector.  Two
> weight-zero vector-valued modular functions, holomorphic on the upper half-plane, with
> representation `σ` and equal principal parts at infinity are equal.

Formalization.  The representation is a group homomorphism
`σ : SL(2, ℤ) →* GL ι ℂ` (matrices acting on column vectors `ι → ℂ`), with finite image
`(Set.range σ).Finite` and no nonzero invariant vector.  A vector-valued modular function
of weight `0` with representation `σ` is `F : ℍ → ι → ℂ` with
`F (γ • τ) = σ(γ) *ᵥ F τ` for all `γ ∈ SL(2, ℤ)`; "holomorphic on `ℍ`" means every
component is `MDifferentiable`.  "Equal principal parts at infinity" is formalized as the
property actually used in the proof: the difference `F - G` has no pole at `i∞`, i.e. every
component of `F - G` is bounded as `Im τ → ∞` (`IsBoundedAtImInfty`).  For components with
expansions in powers of `q^{1/N}` this is equivalent to equality of the principal parts.

Proof (as in the manuscript).  `Γ = ker σ` has finite index because `σ` has finite image,
so its image in `GL(2, ℝ)` is arithmetic.  Each component of `F - G` is invariant under `Γ`
(weight `0`), and covariance turns its behaviour at the cusp `γ • ∞` into a linear
combination of the components at `∞`, so it is bounded at every cusp of `Γ`
(`component_isBoundedAt`).  Hence each component is a weight-zero modular form for `Γ`,
which is constant by Mathlib's `ModularForm.eq_const_of_weight_zero`.  The constant vector is
`σ`-invariant, hence zero.

There are no external hypotheses: the theorem is proved outright from Mathlib (whose
weight-zero level-one theorem underlies `ModularForm.eq_const_of_weight_zero`).
-/

namespace HaagerupIzumi.C8

open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold ModularForm Matrix

section PoleCancellation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each component of a weight-zero `σ`-covariant function is invariant under the image of
`ker σ` in `GL(2, ℝ)`. -/
theorem component_slash_ker (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup ι ℂ)
    (F : ℍ → ι → ℂ)
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = (σ γ : Matrix ι ι ℂ) *ᵥ F τ) (i : ι) :
    ∀ γ ∈ Subgroup.map (mapGL ℝ) σ.ker, (fun τ => F τ i) ∣[(0 : ℤ)] γ = fun τ => F τ i := by
  rintro γ ⟨g, hg, rfl⟩
  have hg' : σ g = 1 := MonoidHom.mem_ker.1 hg
  show (fun τ => F τ i) ∣[(0 : ℤ)] g = fun τ => F τ i
  funext τ
  rw [ModularForm.SL_slash_apply]
  show F (g • τ) i * _ = _
  rw [hcov g τ, hg']
  simp

/-- **Holomorphy at every cusp** ("covariance makes every component holomorphic at every
cusp of the finite-index kernel").  If every component of a `σ`-covariant `F` is bounded at
`i∞`, then every component is bounded at every cusp `c` of `SL(2, ℤ)`: for `c = γ • ∞`,
`F_i ∣ γ = ∑_j σ(γ)_{ij} F_j`. -/
theorem component_isBoundedAt (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup ι ℂ)
    (F : ℍ → ι → ℂ)
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = (σ γ : Matrix ι ι ℂ) *ᵥ F τ)
    (hbdd : ∀ j, IsBoundedAtImInfty (fun τ => F τ j)) (i : ι) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (fun τ => F τ i) 0 := by
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  have hslash : (fun τ => F τ i) ∣[(0 : ℤ)] γ =
      ∑ j, (σ γ : Matrix ι ι ℂ) i j • (fun τ => F τ j) := by
    funext τ
    rw [ModularForm.SL_slash_apply]
    show F (γ • τ) i * _ = _
    rw [hcov γ τ]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  have hmem : (∑ j, (σ γ : Matrix ι ι ℂ) i j • (fun τ => F τ j)) ∈
      UpperHalfPlane.boundedAtImInftySubalgebra ℂ :=
    sum_mem fun j _ => (UpperHalfPlane.boundedAtImInftySubalgebra ℂ).smul_mem
      (x := fun τ => F τ j) (hbdd j) _
  rw [hslash]
  exact hmem

/-- **Core of `lem:pole-cancellation`.**  Let `σ : SL(2, ℤ) → GL ι ℂ` have finite image and
no nonzero invariant vector.  If `F : ℍ → ι → ℂ` is holomorphic, satisfies
`F (γ • τ) = σ(γ) *ᵥ F τ`, and every component is bounded at `i∞`, then `F = 0`. -/
theorem eq_zero_of_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup ι ℂ)
    (hfin : (Set.range σ).Finite)
    (hinv : ∀ v : ι → ℂ, (∀ γ, (σ γ : Matrix ι ι ℂ) *ᵥ v = v) → v = 0)
    (F : ℍ → ι → ℂ) (hhol : ∀ i, MDiff (fun τ => F τ i))
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = (σ γ : Matrix ι ι ℂ) *ᵥ F τ)
    (hbdd : ∀ i, IsBoundedAtImInfty (fun τ => F τ i)) :
    F = 0 := by
  have hfin' : ((σ.range : Subgroup (Matrix.GeneralLinearGroup ι ℂ)) :
      Set (Matrix.GeneralLinearGroup ι ℂ)).Finite := by
    rw [MonoidHom.coe_range]
    exact hfin
  have : Finite σ.range := hfin'.to_subtype
  have key : ∀ i, ∃ c : ℂ, ∀ τ, F τ i = c := by
    intro i
    let fi : ModularForm (Subgroup.map (mapGL ℝ) σ.ker) 0 :=
      { toFun := fun τ => F τ i
        slash_action_eq' := component_slash_ker σ F hcov i
        holo' := hhol i
        bdd_at_cusps' := fun hc => component_isBoundedAt σ F hcov hbdd i
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc) }
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero fi
    exact ⟨c, fun τ => congrFun hc τ⟩
  choose c hc using key
  have hFc : ∀ τ, F τ = c := fun τ => funext fun i => hc i τ
  have hc0 : c = 0 := hinv c fun γ => by
    have h := hcov γ UpperHalfPlane.I
    rw [hFc, hFc] at h
    exact h.symm
  funext τ
  simp [hFc τ, hc0]

/-- **Lemma `lem:pole-cancellation`** (lines 3599–3612).  Let `σ : SL(2, ℤ) → GL ι ℂ` be a
representation with finite image and no nonzero invariant vector.  Let `F, G : ℍ → ι → ℂ` be
weight-zero vector-valued modular functions for `σ`, holomorphic on `ℍ`
(`F (γ • τ) = σ(γ) *ᵥ F τ`, likewise for `G`), with equal principal parts at infinity, i.e.
every component of `F - G` bounded at `i∞`.  Then `F = G`. -/
theorem pole_cancellation (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup ι ℂ)
    (hfin : (Set.range σ).Finite)
    (hinv : ∀ v : ι → ℂ, (∀ γ, (σ γ : Matrix ι ι ℂ) *ᵥ v = v) → v = 0)
    (F G : ℍ → ι → ℂ) (hF : ∀ i, MDiff (fun τ => F τ i)) (hG : ∀ i, MDiff (fun τ => G τ i))
    (hFcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = (σ γ : Matrix ι ι ℂ) *ᵥ F τ)
    (hGcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G (γ • τ) = (σ γ : Matrix ι ι ℂ) *ᵥ G τ)
    (hpp : ∀ i, IsBoundedAtImInfty (fun τ => F τ i - G τ i)) :
    F = G := by
  have h := eq_zero_of_covariant σ hfin hinv (F - G) (fun i => (hF i).sub (hG i))
    (fun γ τ => by simp only [Pi.sub_apply, hFcov, hGcov, Matrix.mulVec_sub]) hpp
  exact sub_eq_zero.1 h

end PoleCancellation

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.component_isBoundedAt
#print axioms HaagerupIzumi.C8.eq_zero_of_covariant
#print axioms HaagerupIzumi.C8.pole_cancellation
