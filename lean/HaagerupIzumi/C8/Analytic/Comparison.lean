module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

@[expose] public section

/-! # Exact finite steps of the analytic comparison (Section `sec:analytic-unitarity`)

This file isolates small exact arguments from the analytic comparison
(`haagerup_c8_expanded.tex`, lines 4217–4895).  The analytic and categorical theorems
cited there (Henriques–Tener reconstruction and annulus results, Tener's bounded
insertions, CKLW, Kawahigashi–Longo, Haag duality of conformal nets, ...) are not proved;
the concrete properties they supply are explicit hypotheses.

* `analytic_inverse_domain` (Lemma `lem:analytic-inverse-domain`, lines 4642–4672):
  from `A C = λ R` (`λ ≠ 0`), `A` injective, `C` continuous with dense range, and `R` a
  bijection of the dense subspace `F = M^fin` onto itself: `F ⊆ ran A`,
  `A⁻¹ F = C F`, and this set is dense.  Hypotheses: injectivity and dense range of the
  annulus actions are Henriques–Tener Lemma 4.15; `A C = λ r^{L₀}` is
  `eq:analytic-round-factorization`; `R = r^{L₀}` preserves and exhausts the
  finite-energy space.
* `insertion_continuation` (Lemma `lem:analytic-insertion-continuation`, lines
  4697–4735): matrix coefficients continuous on `Ω = int(cl O_in ∪ cl O_out)` that agree
  on `O_in ∪ O_out` agree on `Ω` (density suffices; the identity theorem is not needed),
  and a bounded operator is determined by its matrix coefficients on two dense test
  domains (`clm_eq_of_inner_eq_on_dense`).  Hypotheses: boundedness and holomorphy of
  the geometric insertion (Henriques–Tener Lemma 6.8, Corollary 6.15), its agreement with
  the algebraic form on the two interiors (sewing, Theorem 9.5(i), Proposition 6.19),
  density of `𝒟_A`, `𝒟_{B*}` (`analytic_inverse_domain`).
* `haag_squeeze`, `net_eq_of_haagDuality`, `vonNeumann_eq_of_haagDuality`
  (lines 4858–4864): `𝒜(I) ⊆ 𝒩(I) ⊆ 𝒜(I')' = 𝒜(I)` forces `𝒩(I) = 𝒜(I)`.  Hypotheses:
  the inclusion `𝒜^bl_U(I) ⊆ 𝒩_U(I)` (proved in the manuscript from the annulus
  identities), locality of `𝒩_U`, and Haag duality of the vacuum net `𝒜^bl_U`.
* `commute_on_iSup_of_periodic`, `deck_commute`, `deck_pow_commute` (lines 4801–4806):
  `Z = e^{2πi L₀}` commutes, on the algebraic direct sum of the energy spaces
  `M_{h+n}`, with every operator shifting the energy by an integer.
* `schur_scalar`, `schur_scalar_of_finiteDimensional` (lines 4561–4575): an operator
  commuting with all module operators of a simple module and having an eigenvector
  (e.g. preserving a nonzero finite-dimensional subspace) is a scalar.
* `projection_commute_of_formalAdjoint` (proof of Prop. `clm:analytic-reconstruction`,
  lines 4524–4537): the projection onto the closure of an ordinary summand commutes
  with every mode that has a formal adjoint preserving the summand.
* `bijective_of_injective_of_card_eq`, `forall_of_injective_card_eq` (Prop.
  `prop:analytic-strong-unitarity`, lines 4581–4593): an injection between two sets of
  twelve isomorphism classes is a bijection.  Hypotheses: the twelve net sectors (Prop.
  `clm:analytic-net-count`), the twelve simple `U`-modules (algebraic count), and
  injectivity of reconstruction on isomorphism classes (full faithfulness, Prop.
  `clm:analytic-reconstruction`).
-/

namespace HaagerupIzumi.C8

open scoped InnerProductSpace

section InverseDomain

variable {𝕜 X Y : Type*} [Field 𝕜] [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y]
  [Module 𝕜 Y]

/-- Range assertion of `lem:analytic-inverse-domain`: `v = A C (λ⁻¹ r^{-L₀} v)`. -/
theorem inverseDomain_subset_range {A : Y →ₗ[𝕜] X} {C : X →ₗ[𝕜] Y} {R : X →ₗ[𝕜] X}
    {lam : 𝕜} (hlam : lam ≠ 0) (hAC : ∀ x, A (C x) = lam • R x) (F : Submodule 𝕜 X)
    (hRF' : ∀ v ∈ F, ∃ w ∈ F, R w = v) :
    ∀ v ∈ F, v ∈ LinearMap.range A := by
  intro v hv
  obtain ⟨w, -, rfl⟩ := hRF' v hv
  refine LinearMap.mem_range.2 ⟨C (lam⁻¹ • w), ?_⟩
  rw [map_smul, map_smul, hAC, smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- Preimage assertion of `lem:analytic-inverse-domain`: `A⁻¹ F = C F`. -/
theorem inverseDomain_preimage {A : Y →ₗ[𝕜] X} {C : X →ₗ[𝕜] Y} {R : X →ₗ[𝕜] X}
    {lam : 𝕜} (hlam : lam ≠ 0) (hAC : ∀ x, A (C x) = lam • R x)
    (hA : Function.Injective A) (F : Submodule 𝕜 X) (hRF : ∀ w ∈ F, R w ∈ F)
    (hRF' : ∀ v ∈ F, ∃ w ∈ F, R w = v) :
    A ⁻¹' (F : Set X) = C '' (F : Set X) := by
  ext ξ
  constructor
  · intro hξ
    obtain ⟨w, hw, hRw⟩ := hRF' (A ξ) hξ
    refine ⟨lam⁻¹ • w, F.smul_mem _ hw, hA ?_⟩
    rw [map_smul, map_smul, hAC, smul_smul, inv_mul_cancel₀ hlam, one_smul, hRw]
  · rintro ⟨w, hw, rfl⟩
    show A (C w) ∈ F
    rw [hAC]
    exact F.smul_mem _ (hRF w hw)

/-- **Lemma `lem:analytic-inverse-domain`** (Dense inverse-energy domains, lines
4642–4672).  Let `A, C` be linear, `A` injective, `C` continuous with dense range, and
`A C = λ R` with `λ ≠ 0`, where `R` maps the dense subspace `F` onto itself.  Then
`F ⊆ ran A`, `A⁻¹ F = C F`, and `A⁻¹ F` is dense. -/
theorem analytic_inverse_domain [TopologicalSpace X] [TopologicalSpace Y]
    {A : Y →ₗ[𝕜] X} {C : X →ₗ[𝕜] Y} {R : X →ₗ[𝕜] X} {lam : 𝕜} (hlam : lam ≠ 0)
    (hAC : ∀ x, A (C x) = lam • R x) (hA : Function.Injective A)
    (hC : Continuous C) (hCd : DenseRange C) (F : Submodule 𝕜 X) (hF : Dense (F : Set X))
    (hRF : ∀ w ∈ F, R w ∈ F) (hRF' : ∀ v ∈ F, ∃ w ∈ F, R w = v) :
    (∀ v ∈ F, v ∈ LinearMap.range A) ∧ A ⁻¹' (F : Set X) = C '' (F : Set X) ∧
      Dense (A ⁻¹' (F : Set X)) := by
  have hpre := inverseDomain_preimage hlam hAC hA F hRF hRF'
  refine ⟨inverseDomain_subset_range hlam hAC F hRF', hpre, ?_⟩
  rw [hpre]
  exact hCd.dense_image hC hF

end InverseDomain

section InsertionContinuation

/-- `O₁ ∪ O₂ ⊆ Ω = int(cl O₁ ∪ cl O₂)` for open `O₁, O₂`. -/
theorem union_subset_interior_closure_union {X : Type*} [TopologicalSpace X] {O₁ O₂ : Set X}
    (h₁ : IsOpen O₁) (h₂ : IsOpen O₂) :
    O₁ ∪ O₂ ⊆ interior (closure O₁ ∪ closure O₂) :=
  interior_maximal (Set.union_subset_union subset_closure subset_closure) (h₁.union h₂)

/-- `Ω = int(cl O₁ ∪ cl O₂)` lies in the closure of `O₁ ∪ O₂`. -/
theorem interior_closure_union_subset_closure {X : Type*} [TopologicalSpace X]
    (O₁ O₂ : Set X) :
    interior (closure O₁ ∪ closure O₂) ⊆ closure (O₁ ∪ O₂) := by
  rw [closure_union]
  exact interior_subset

/-- Two functions continuous on `Ω = int(cl O₁ ∪ cl O₂)` that agree on `O₁ ∪ O₂` agree on
`Ω`. -/
theorem eqOn_interior_closure_union {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {O₁ O₂ : Set X} (h₁ : IsOpen O₁) (h₂ : IsOpen O₂) {f g : X → Y}
    (hf : ContinuousOn f (interior (closure O₁ ∪ closure O₂)))
    (hg : ContinuousOn g (interior (closure O₁ ∪ closure O₂)))
    (hfg : Set.EqOn f g (O₁ ∪ O₂)) :
    Set.EqOn f g (interior (closure O₁ ∪ closure O₂)) :=
  hfg.of_subset_closure hf hg (union_subset_interior_closure_union h₁ h₂)
    (interior_closure_union_subset_closure O₁ O₂)

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A bounded operator is determined by its matrix coefficients on two dense sets. -/
theorem clm_eq_of_inner_eq_on_dense {G G' : E →L[𝕜] F} {D₁ : Set E} {D₂ : Set F}
    (h₁ : Dense D₁) (h₂ : Dense D₂)
    (h : ∀ ξ ∈ D₁, ∀ η ∈ D₂, ⟪G ξ, η⟫_𝕜 = ⟪G' ξ, η⟫_𝕜) : G = G' := by
  have hD : Set.EqOn G G' D₁ := fun ξ hξ => h₂.eq_of_inner_left 𝕜 (h ξ hξ)
  have hfun : (G : E → F) = G' := G.continuous.ext_on h₁ G'.continuous hD
  exact ContinuousLinearMap.ext fun ξ => congrFun hfun ξ

/-- **Lemma `lem:analytic-insertion-continuation`** (Continuation of the insertion form,
lines 4697–4735).  Let `O₁, O₂` be open (the incoming and outgoing insertion interiors) and
`Ω = int(cl O₁ ∪ cl O₂)`.  Let `G z` be bounded operators (the geometric insertion
`G_v(z)`) and `form z ξ η` the algebraic insertion form `⟨Y(v,z) A ξ, B* η⟩`, for test
vectors in the dense domains `D₁ = 𝒟_A`, `D₂ = 𝒟_{B*}`.  If for all test vectors the
functions `z ↦ ⟪G z ξ, η⟫` and `z ↦ form z ξ η` are continuous on `Ω` (e.g. holomorphic)
and agree on `O₁ ∪ O₂`, then they agree on `Ω`, and for every `z ∈ Ω` the operator `G z` is
the unique bounded operator with these matrix coefficients. -/
theorem insertion_continuation {X : Type*} [TopologicalSpace X] {O₁ O₂ : Set X}
    (h₁ : IsOpen O₁) (h₂ : IsOpen O₂) (G : X → E →L[𝕜] F) (form : X → E → F → 𝕜)
    {D₁ : Set E} {D₂ : Set F} (hD₁ : Dense D₁) (hD₂ : Dense D₂)
    (hG : ∀ ξ ∈ D₁, ∀ η ∈ D₂,
      ContinuousOn (fun z => ⟪G z ξ, η⟫_𝕜) (interior (closure O₁ ∪ closure O₂)))
    (hform : ∀ ξ ∈ D₁, ∀ η ∈ D₂,
      ContinuousOn (fun z => form z ξ η) (interior (closure O₁ ∪ closure O₂)))
    (heq : ∀ z ∈ O₁ ∪ O₂, ∀ ξ ∈ D₁, ∀ η ∈ D₂, ⟪G z ξ, η⟫_𝕜 = form z ξ η) :
    ∀ z ∈ interior (closure O₁ ∪ closure O₂),
      (∀ ξ ∈ D₁, ∀ η ∈ D₂, ⟪G z ξ, η⟫_𝕜 = form z ξ η) ∧
      ∀ G' : E →L[𝕜] F, (∀ ξ ∈ D₁, ∀ η ∈ D₂, ⟪G' ξ, η⟫_𝕜 = form z ξ η) → G' = G z := by
  intro z hz
  have hcoef : ∀ ξ ∈ D₁, ∀ η ∈ D₂, ⟪G z ξ, η⟫_𝕜 = form z ξ η := fun ξ hξ η hη =>
    eqOn_interior_closure_union h₁ h₂ (hG ξ hξ η hη) (hform ξ hξ η hη)
      (fun w hw => heq w hw ξ hξ η hη) hz
  refine ⟨hcoef, fun G' hG' => clm_eq_of_inner_eq_on_dense hD₁ hD₂ fun ξ hξ η hη => ?_⟩
  rw [hG' ξ hξ η hη, hcoef ξ hξ η hη]

end InsertionContinuation

section HaagDuality

/-- The squeeze `𝒜 ⊆ 𝒩 ⊆ 𝒜' ′ = 𝒜` (lines 4858–4864), for sets in any multiplicative
structure, with `Set.centralizer` as commutant. -/
theorem haag_squeeze {M : Type*} [Mul M] {A N A' : Set M} (hAN : A ⊆ N)
    (hNA' : N ⊆ Set.centralizer A') (hHaag : Set.centralizer A' = A) : N = A := by
  refine Set.Subset.antisymm ?_ hAN
  rw [← hHaag]
  exact hNA'

/-- **Equality of the concrete nets** (end of the proof of Prop. `clm:analytic-annulus`,
lines 4858–4865).  If `𝒜(J) ⊆ 𝒩(J)` for `J = I, I'`, `𝒩` is local
(`𝒩(I) ⊆ 𝒩(I')′`), and `𝒜` satisfies Haag duality `𝒜(I')′ = 𝒜(I)`, then
`𝒩(I) = 𝒜(I)`. -/
theorem net_eq_of_haagDuality {M ι : Type*} [Mul M] (𝒜 𝒩 : ι → Set M) {I I' : ι}
    (hsub : 𝒜 I ⊆ 𝒩 I) (hsub' : 𝒜 I' ⊆ 𝒩 I')
    (hloc : 𝒩 I ⊆ Set.centralizer (𝒩 I')) (hHaag : Set.centralizer (𝒜 I') = 𝒜 I) :
    𝒩 I = 𝒜 I :=
  haag_squeeze hsub (Set.Subset.trans hloc (Set.centralizer_subset hsub')) hHaag

/-- The same squeeze with Mathlib's von Neumann algebras and `VonNeumannAlgebra.commutant`. -/
theorem vonNeumann_eq_of_haagDuality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {𝒜 𝒜' : VonNeumannAlgebra H}
    {𝒩 𝒩' : Set (H →L[ℂ] H)} (hsub : (𝒜 : Set (H →L[ℂ] H)) ⊆ 𝒩)
    (hsub' : (𝒜' : Set (H →L[ℂ] H)) ⊆ 𝒩') (hloc : 𝒩 ⊆ Set.centralizer 𝒩')
    (hHaag : 𝒜'.commutant = 𝒜) :
    𝒩 = 𝒜 := by
  apply haag_squeeze hsub (Set.Subset.trans hloc (Set.centralizer_subset hsub'))
  rw [← VonNeumannAlgebra.coe_commutant, hHaag]

end HaagDuality

section Deck

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If `Z` acts on `M n` by the scalar `c n`, `c` is `j`-periodic, and `X` maps `M n` into
`M (n + j)`, then `Z X = X Z` on `⨆ n, M n`. -/
theorem commute_on_iSup_of_periodic (M : ℤ → Submodule K V) (c : ℤ → K)
    (Z X : V →ₗ[K] V) (hZ : ∀ n, ∀ v ∈ M n, Z v = c n • v) (j : ℤ)
    (hc : ∀ n, c (n + j) = c n) (hX : ∀ n, ∀ v ∈ M n, X v ∈ M (n + j)) :
    ∀ v ∈ ⨆ n, M n, Z (X v) = X (Z v) := by
  intro v hv
  refine Submodule.iSup_induction M (motive := fun v => Z (X v) = X (Z v)) hv ?_ ?_ ?_
  · intro n v hv
    rw [hZ (n + j) (X v) (hX n v hv), hc n, hZ n v hv, map_smul]
  · simp
  · intro v w hv hw
    simp only [map_add, hv, hw]

/-- **Deck cancellation** (lines 4801–4806).  Let `Z` act on the energy space `M_{h+n}`
(`n ∈ ℤ`; the spaces with `h + n` below the lowest weight are zero) by `e^{2πi(h+n)}`, and
let `X` change the energy by the integer `j`.  Then `Z X = X Z` on the algebraic direct sum
of the energy spaces, even for fractional `h`. -/
theorem deck_commute {W : Type*} [AddCommGroup W] [Module ℂ W] (M : ℤ → Submodule ℂ W) (h : ℂ)
    (Z X : W →ₗ[ℂ] W)
    (hZ : ∀ n : ℤ, ∀ v ∈ M n, Z v = Complex.exp (2 * Real.pi * Complex.I * (h + n)) • v)
    (j : ℤ) (hX : ∀ n, ∀ v ∈ M n, X v ∈ M (n + j)) :
    ∀ v ∈ ⨆ n, M n, Z (X v) = X (Z v) := by
  refine commute_on_iSup_of_periodic M
    (fun n : ℤ => Complex.exp (2 * Real.pi * Complex.I * (h + n))) Z X hZ j ?_ hX
  intro n
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (h + ((n + j : ℤ) : ℂ)) =
      2 * Real.pi * Complex.I * (h + n) + (j : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A power of `Z` acts on `M n` by the corresponding power of the scalar. -/
theorem pow_apply_of_mem (M : ℤ → Submodule K V) (c : ℤ → K) (Z : V →ₗ[K] V)
    (hZ : ∀ n, ∀ v ∈ M n, Z v = c n • v) (m : ℕ) :
    ∀ n, ∀ v ∈ M n, (Z ^ m) v = c n ^ m • v := by
  induction m with
  | zero => intro n v _; simp
  | succ m ih =>
    intro n v hv
    rw [pow_succ', Module.End.mul_apply, ih n v hv, map_smul, hZ n v hv, smul_smul, pow_succ]

/-- Deck transformations `Z^m` also commute with integer energy shifts. -/
theorem deck_pow_commute (M : ℤ → Submodule K V) (c : ℤ → K) (Z X : V →ₗ[K] V)
    (hZ : ∀ n, ∀ v ∈ M n, Z v = c n • v) (j : ℤ) (hc : ∀ n, c (n + j) = c n)
    (hX : ∀ n, ∀ v ∈ M n, X v ∈ M (n + j)) (m : ℕ) :
    ∀ v ∈ ⨆ n, M n, (Z ^ m) (X v) = X ((Z ^ m) v) :=
  commute_on_iSup_of_periodic M (fun n => c n ^ m) (Z ^ m) X (pow_apply_of_mem M c Z hZ m) j
    (fun n => by simp only [hc n]) hX

end Deck

section Schur

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Schur step** (lines 4561–4575).  On a module that is simple for a set `S` of
operators (every `S`-invariant subspace is `⊥` or `⊤`), an operator `Q` commuting with
every element of `S` and having an eigenvector `x ≠ 0`, `Q x = μ x`, is the scalar `μ`. -/
theorem schur_scalar (S : Set (Module.End K V))
    (hsimple : ∀ W : Submodule K V, (∀ a ∈ S, ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = ⊤)
    (Q : Module.End K V) (hQ : ∀ a ∈ S, ∀ x, Q (a x) = a (Q x))
    {μ : K} {x : V} (hx : x ≠ 0) (hQx : Q x = μ • x) :
    ∀ v, Q v = μ • v := by
  have hinv : ∀ a ∈ S, ∀ y ∈ Module.End.eigenspace Q μ, a y ∈ Module.End.eigenspace Q μ := by
    intro a ha y hy
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    rw [hQ a ha, hy, map_smul]
  rcases hsimple _ hinv with h | h
  · have hxmem : x ∈ Module.End.eigenspace Q μ := Module.End.mem_eigenspace_iff.2 hQx
    rw [h, Submodule.mem_bot] at hxmem
    exact absurd hxmem hx
  · intro v
    have hv : v ∈ Module.End.eigenspace Q μ := by
      rw [h]
      exact Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.1 hv

/-- Schur step with the eigenvector produced as in the manuscript: if `Q` preserves a
nonzero finite-dimensional subspace (the lowest energy space) over an algebraically closed
field, then `Q` is a scalar. -/
theorem schur_scalar_of_finiteDimensional [IsAlgClosed K] (S : Set (Module.End K V))
    (hsimple : ∀ W : Submodule K V, (∀ a ∈ S, ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = ⊤)
    (Q : Module.End K V) (hQ : ∀ a ∈ S, ∀ x, Q (a x) = a (Q x))
    (W₀ : Submodule K V) [FiniteDimensional K W₀] (hW₀ : W₀ ≠ ⊥)
    (hQW₀ : ∀ x ∈ W₀, Q x ∈ W₀) :
    ∃ μ : K, ∀ v, Q v = μ • v := by
  have : Nontrivial W₀ := Submodule.nontrivial_iff_ne_bot.2 hW₀
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Q.restrict hQW₀)
  obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
  obtain ⟨hy1, hy2⟩ := Module.End.hasEigenvector_iff.1 hy
  have h1 := Module.End.mem_eigenspace_iff.1 hy1
  have h2 : Q (y : V) = μ • (y : V) := congrArg Subtype.val h1
  refine ⟨μ, schur_scalar S hsimple Q hQ (x := (y : V)) ?_ h2⟩
  intro h0
  exact hy2 (Subtype.ext h0)

end Schur

section ProjectionCommute

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Projection onto an ordinary summand commutes with modes** (proof of Prop.
`clm:analytic-reconstruction`, lines 4524–4537).  Let `S ⊆ M` be subspaces and `P` a
symmetric map that is the identity on `S` and maps `M` into `S` (the projection onto the
closure of the summand `S`, eq. `eq:analytic-projection-core`).  If `X` preserves `M` and
`S` and has a formal adjoint `X†` on `S` that preserves `S`
(`⟪X ξ, s⟫ = ⟪ξ, X† s⟫` for `ξ ∈ M`, `s ∈ S`; the unitary invariance identity), then
`P X ξ = X P ξ` for every `ξ ∈ M`. -/
theorem projection_commute_of_formalAdjoint (S M : Submodule 𝕜 H) (hSM : S ≤ M)
    (P : H → H) (hPsymm : ∀ a b, ⟪P a, b⟫_𝕜 = ⟪a, P b⟫_𝕜) (hPS : ∀ s ∈ S, P s = s)
    (hPM : ∀ ξ ∈ M, P ξ ∈ S) (X Xd : H →ₗ[𝕜] H) (hXM : ∀ ξ ∈ M, X ξ ∈ M)
    (hXS : ∀ s ∈ S, X s ∈ S) (hXdS : ∀ s ∈ S, Xd s ∈ S)
    (hadj : ∀ ξ ∈ M, ∀ s ∈ S, ⟪X ξ, s⟫_𝕜 = ⟪ξ, Xd s⟫_𝕜) {ξ : H} (hξ : ξ ∈ M) :
    P (X ξ) = X (P ξ) := by
  have horth : ∀ s ∈ S, ⟪P (X ξ) - X (P ξ), s⟫_𝕜 = 0 := by
    intro s hs
    rw [inner_sub_left, hPsymm, hPS s hs, hadj ξ hξ s hs, hadj (P ξ) (hSM (hPM ξ hξ)) s hs,
      hPsymm ξ (Xd s), hPS (Xd s) (hXdS s hs), sub_self]
  have hu : P (X ξ) - X (P ξ) ∈ S := S.sub_mem (hPM _ (hXM ξ hξ)) (hXS _ (hPM ξ hξ))
  have h0 := horth _ hu
  rw [inner_self_eq_zero, sub_eq_zero] at h0
  exact h0

end ProjectionCommute

section Counting

/-- **Counting step of Prop. `prop:analytic-strong-unitarity`** (lines 4588–4590).
An injective map between two finite types with twelve elements each is bijective. -/
theorem bijective_of_injective_of_card_eq {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (hf : Function.Injective f) (hα : Fintype.card α = 12) (hβ : Fintype.card β = 12) :
    Function.Bijective f :=
  (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hα.trans hβ.symm⟩

/-- **Strong unitarity from sector exhaustion** (Prop. `prop:analytic-strong-unitarity`).
Let `α` be the twelve irreducible net sectors and `β` the twelve isomorphism classes of
simple `U`-modules, and `f` the reconstruction on isomorphism classes (injective by full
faithfulness).  If every reconstructed module has a property (unitarizability, character of
a net sector), then every simple `U`-module has it. -/
theorem forall_of_injective_card_eq {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (hf : Function.Injective f) (hα : Fintype.card α = 12) (hβ : Fintype.card β = 12)
    (p : β → Prop) (hp : ∀ a, p (f a)) : ∀ b, p b := by
  intro b
  obtain ⟨a, rfl⟩ := (bijective_of_injective_of_card_eq f hf hα hβ).2 b
  exact hp a

end Counting

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.analytic_inverse_domain
#print axioms HaagerupIzumi.C8.insertion_continuation
#print axioms HaagerupIzumi.C8.net_eq_of_haagDuality
#print axioms HaagerupIzumi.C8.vonNeumann_eq_of_haagDuality
#print axioms HaagerupIzumi.C8.deck_commute
#print axioms HaagerupIzumi.C8.deck_pow_commute
#print axioms HaagerupIzumi.C8.schur_scalar
#print axioms HaagerupIzumi.C8.schur_scalar_of_finiteDimensional
#print axioms HaagerupIzumi.C8.projection_commute_of_formalAdjoint
#print axioms HaagerupIzumi.C8.bijective_of_injective_of_card_eq
#print axioms HaagerupIzumi.C8.forall_of_injective_card_eq
