module

public import HaagerupIzumi.C8.Regularity.NoNegativeWeights
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# The vacuum-top step on `N_[0]` (Lemma `lem:vacuum-projective`, lines 2959–2978)

Lines 2959–2978 of `c8_expanded_20260929/haagerup_c8_expanded.tex`: *"The finite generalized
weight-zero space `N_[0]` therefore has no lower-weight target for a lowering mode.  It is again in
every `Ω_{Aᵢ}(N)` and is invariant under degree-zero modes.  On this space `L_V(0)` is nilpotent,
so `0 = Tr L_V(0) = ∑ cᵢ Tr L^{eᵢ}(0)`.  Diagonalizability and nonnegativity of each partial
energy imply it is zero.  The vacuum-top step gives `L_V(-1) N_[0] = 0`.  … one can choose
`v ∈ N_[0]` with `π(v) = 𝟏`.  Then `s(a) = a_(-1) v` is a section."*

This file derives `ω_(0) v = 0` on `N_[0]` (previously an input of
`VacuumProjective.omega_vacuumLike_section`) and the splitting itself from the following inputs,
stated as in `Regularity/CompatibleTop`:

* `omegaSpace A W A'` is `Ω_{A'}(M)`, the vectors killed by every mode `a_(n)`, `n ≥ d`, of the
  states `a ∈ A' ∩ V_d` (`A' ⊆ V` a grading-compatible component algebra);
* `ComponentTops A W A' e K T` (**[external] regularity of the component algebra `A'` with
  conformal vector `e`**): a linear isomorphism `Ω_{A'}(M) ≅ ⨁ₖ T k` onto the direct sum of the
  tops of the simple ordinary summands of `M↓A'`, on each of which `L^{A'}(0) = e_(1)` acts by the
  lowest weight `wt k ≥ 0` (nonnegative lowest weights of the factor), and `L^{A'}(-1) = e_(0)`
  kills the tops of lowest weight `0` (these are vacuum tops: the vacuum is the only weight-zero
  simple of `A'` and `L(-1)𝟏 = 0`).

Results:

* `isNonnegDiagonalizable_of_tops`: an operator acting on `Ω ≅ ⨁ T k` by the scalars `wt k ≥ 0`
  is diagonalizable with nonnegative eigenvalues on every finite-dimensional invariant subspace
  `F ⊆ Ω` (generalized eigenvectors are eigenvectors; `Module.End.iSup_maxGenEigenspace_eq_top`).
  This is `lem:compatible-top`'s "in particular" without the Zhu-algebra structure.
* `genZero_le_omegaSpace`: `N_[0] ⊆ Ω_{A'}(N)` (`VacuumProjective.lowering_mode_eq_zero`);
  `act_one_mem_genZero`: degree-zero modes of weight-two states preserve `N_[0]`
  (`VacuumProjective.act_mem_maxGenEigenspace`); `isNilpotent_restrict_genZero`: `L(0)` is
  nilpotent on a finite-dimensional `N_[0]`.
* `ComponentTops.vacuumTop` (the vacuum-top step, lines 2951–2954: on `Ω_{A'}(M)`, `e_(1) v = 0`
  implies `e_(0) v = 0`) and `ComponentTops.nonnegDiagonalizable` (`e_(1)` is nonnegatively
  diagonalizable on every finite-dimensional invariant `F ⊆ Ω_{A'}(M)`), for any weak module.
* `omega_zero_on_genZero` (**the vacuum-top step on `N_[0]`**, lines 2965–2970): from
  `ω = ∑ cᵢ eᵢ` (`cᵢ > 0`), the regularity data of each component and no negative generalized
  weights, `ω_(0) v = 0` for every `v ∈ N_[0]` (`Energy.eq_zero_of_isNilpotent_sum`,
  `CompatibleTop.vacuum_top_step`, `sum_smul_apply_eq_zero`).
* `vacuum_splitting_of_tops`: with an epimorphism `π : N ↠ V` of modules and `N` spanned by its
  generalized `L(0)`-eigenspaces, there is `v ∈ N_[0]` with `π v = 𝟏`, `ω_(0) v = 0`, and
  `a ↦ a_(-1) v` is a module section of `π` (`VacuumProjective.exists_vacuum_preimage`,
  `VacuumProjective.omega_vacuumLike_section`).

The remaining hypotheses are the regularity data `ComponentTops` ([external]), finite-dimensionality
of `N_[0]` and absence of negative generalized weights (the latter is
`VacuumProjective.maxGenEigenspace_eq_bot_of_filtration` applied to a composition series, whose
existence is the external finite-length theorem).
-/

namespace HaagerupIzumi.C8.VacuumTopZero

open HaagerupIzumi.C8 HaagerupIzumi.C8.VacuumLike HaagerupIzumi.C8.VacuumProjective

/-! ### Diagonal operators on a direct sum of tops -/

section Diagonal

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {K : Type*} [DecidableEq K] {T : K → Type*} [∀ k, AddCommGroup (T k)]
  [∀ k, Module ℂ (T k)]

/-- The operator acting on the summand `T k` by the scalar `wt k`. -/
noncomputable def diagOp (wt : K → ℝ) : Module.End ℂ (DirectSum K T) :=
  DirectSum.toModule ℂ K (DirectSum K T) fun k => ((wt k : ℂ)) • DirectSum.lof ℂ K T k

theorem diagOp_of (wt : K → ℝ) (k : K) (t : T k) :
    diagOp wt (DirectSum.of T k t) = (wt k : ℂ) • DirectSum.of T k t := by
  show DirectSum.toModule ℂ K (DirectSum K T) (fun k => ((wt k : ℂ)) • DirectSum.lof ℂ K T k)
    (DirectSum.lof ℂ K T k t) = _
  rw [DirectSum.toModule_lof, LinearMap.smul_apply]
  rfl

theorem diagOp_apply (wt : K → ℝ) (z : DirectSum K T) (j : K) :
    diagOp wt z j = (wt j : ℂ) • z j := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of k t =>
    rw [diagOp_of, DirectSum.smul_apply]
    by_cases h : j = k
    · subst h
      rfl
    · rw [DirectSum.of_eq_of_ne k j t h]
      simp only [smul_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, smul_add]

theorem diagOp_pow_apply (wt : K → ℝ) (μ : ℂ) (n : ℕ) (z : DirectSum K T) (j : K) :
    (((diagOp (T := T) wt - μ • (1 : Module.End ℂ (DirectSum K T))) ^ n) z) j =
      ((wt j : ℂ) - μ) ^ n • z j := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (diagOp (T := T) wt - μ • (1 : Module.End ℂ (DirectSum K T))),
      Module.End.mul_apply, ih,
      LinearMap.sub_apply, DirectSum.sub_apply, diagOp_apply, LinearMap.smul_apply,
      Module.End.one_apply, DirectSum.smul_apply, pow_succ ((wt j : ℂ) - μ), mul_smul, sub_smul]

variable (wt : K → ℝ) (Ω : Submodule ℂ M) (eqv : Ω ≃ₗ[ℂ] DirectSum K T) (L : M →ₗ[ℂ] M)
  (hL : ∀ k (t : T k), L (eqv.symm (DirectSum.of T k t) : M) =
    (wt k : ℂ) • (eqv.symm (DirectSum.of T k t) : M))

include hL in
/-- Under `Ω ≅ ⨁ T k`, `L` is the diagonal operator. -/
theorem transport (z : DirectSum K T) : L (eqv.symm z : M) = (eqv.symm (diagOp wt z) : M) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of k t => rw [hL, diagOp_of, map_smul, Submodule.coe_smul]
  | add x y hx hy =>
    rw [map_add, Submodule.coe_add, map_add, hx, hy, map_add, map_add, Submodule.coe_add]

include hL in
theorem transport_pow (μ : ℂ) (n : ℕ) (z : DirectSum K T) :
    ((L - μ • (1 : Module.End ℂ M)) ^ n) (eqv.symm z : M) =
      (eqv.symm (((diagOp (T := T) wt - μ • (1 : Module.End ℂ (DirectSum K T))) ^ n) z) : M) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have h1 : (L - μ • (1 : Module.End ℂ M)) (eqv.symm z : M) =
        (eqv.symm ((diagOp (T := T) wt - μ • (1 : Module.End ℂ (DirectSum K T))) z) : M) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, transport wt Ω eqv L hL z,
        LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply,
        map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
    rw [pow_succ (L - μ • (1 : Module.End ℂ M)), Module.End.mul_apply, h1, ih,
      pow_succ (diagOp (T := T) wt - μ • (1 : Module.End ℂ (DirectSum K T))), Module.End.mul_apply]

include hL in
/-- **Diagonalizability on a finite-dimensional invariant subspace** (the "in particular" of
`lem:compatible-top`, lines 2896–2898, for `Ω_A(M) ≅ ⨁ tops`): if `L` acts on `Ω ≅ ⨁ₖ T k` by
the scalars `wt k ≥ 0`, then on every finite-dimensional `L`-invariant `F ⊆ Ω` it is
diagonalizable with nonnegative real eigenvalues. -/
theorem isNonnegDiagonalizable_of_tops (hwt : ∀ k, 0 ≤ wt k) (F : Submodule ℂ M)
    [FiniteDimensional ℂ F] (hFΩ : F ≤ Ω) (hF : ∀ x ∈ F, L x ∈ F) :
    IsNonnegDiagonalizable (L.restrict hF) := by
  classical
  set f := L.restrict hF with hfdef
  have hfpow : ∀ (μ : ℂ) (n : ℕ) (x : F),
      ((((f - μ • (1 : Module.End ℂ F)) ^ n) x : F) : M) =
        ((L - μ • (1 : Module.End ℂ M)) ^ n) (x : M) := by
    intro μ n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ' (f - μ • (1 : Module.End ℂ F)), Module.End.mul_apply,
        pow_succ' (L - μ • (1 : Module.End ℂ M)), Module.End.mul_apply, ← ih]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        Submodule.coe_sub, Submodule.coe_smul, hfdef, LinearMap.coe_restrict_apply]
  -- generalized eigenvectors are eigenvectors, with eigenvalue some `wt j`
  have key : ∀ (μ : ℂ) (x : F), x ∈ Module.End.maxGenEigenspace f μ → x ≠ 0 →
      f x = μ • x ∧ ∃ j, μ = (wt j : ℂ) := by
    intro μ x hx hx0
    rw [Module.End.mem_maxGenEigenspace] at hx
    obtain ⟨n, hn⟩ := hx
    set z := eqv ⟨(x : M), hFΩ x.2⟩ with hz
    have hxz : (eqv.symm z : M) = x := by rw [hz, LinearEquiv.symm_apply_apply]
    have h1 : ((diagOp (T := T) wt - μ • (1 : Module.End ℂ (DirectSum K T))) ^ n) z = 0 := by
      have h := hfpow μ n x
      rw [hn, ZeroMemClass.coe_zero, ← hxz, transport_pow wt Ω eqv L hL] at h
      apply eqv.symm.injective
      rw [map_zero]
      exact Subtype.ext h.symm
    have hcomp : ∀ j, ((wt j : ℂ) - μ) • z j = 0 := by
      intro j
      have h := congrArg (fun w : DirectSum K T => w j) h1
      simp only [diagOp_pow_apply, DirectSum.zero_apply] at h
      rcases smul_eq_zero.mp h with h' | h'
      · rw [(pow_eq_zero_iff'.mp h').1, zero_smul]
      · rw [h', smul_zero]
    have hD : diagOp wt z = μ • z := by
      ext j
      rw [diagOp_apply, DirectSum.smul_apply, ← sub_eq_zero, ← sub_smul]
      exact hcomp j
    refine ⟨Subtype.ext ?_, ?_⟩
    · rw [hfdef, LinearMap.coe_restrict_apply, Submodule.coe_smul, ← hxz, transport wt Ω eqv L hL,
        hD, map_smul, Submodule.coe_smul]
    · have hz0 : z ≠ 0 := by
        intro h0
        apply hx0
        apply Subtype.ext
        rw [← hxz, h0, map_zero, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
      obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hz0 (DirectSum.ext fun j => by rw [hcon j, DirectSum.zero_apply])
      refine ⟨j, ?_⟩
      have h := hcomp j
      rcases smul_eq_zero.mp h with h' | h'
      · exact (sub_eq_zero.mp h').symm
      · exact absurd h' hj
  -- the eigenvectors with nonnegative real eigenvalues span `F`
  let s : Set F := {y | ∃ r : ℝ, 0 ≤ r ∧ f y = (r : ℂ) • y}
  have hspan : Submodule.span ℂ s = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top f, iSup_le_iff]
    intro μ y hy
    by_cases hy0 : y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    · obtain ⟨hfy, j, hj⟩ := key μ y hy hy0
      exact Submodule.subset_span ⟨wt j, hwt j, by rw [hfy, hj]⟩
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℂ s
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → F)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B := Module.Basis.mk hli htop
  have : Finite b := Module.Finite.finite_basis B
  let _ : Fintype b := Fintype.ofFinite b
  refine IsNonnegDiagonalizable.of_basis B (fun i => Classical.choose (hbs i.2))
    (fun i => (Classical.choose_spec (hbs i.2)).1) f (fun i => ?_)
  rw [Module.Basis.mk_apply]
  exact (Classical.choose_spec (hbs i.2)).2

end Diagonal

/-! ### Nilpotency on a finite-dimensional generalized weight-zero space -/

section Nilpotent

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- On a finite-dimensional generalized eigenspace `N_[0]`, `L` is nilpotent. -/
theorem isNilpotent_restrict_genZero (L : Module.End ℂ M)
    [FiniteDimensional ℂ (L.maxGenEigenspace 0)]
    (hF : ∀ x ∈ L.maxGenEigenspace 0, L x ∈ L.maxGenEigenspace 0) :
    IsNilpotent (L.restrict hF) := by
  classical
  set f := L.restrict hF with hfdef
  have hpow : ∀ (n : ℕ) (x : L.maxGenEigenspace 0), (((f ^ n) x : _) : M) = (L ^ n) (x : M) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ' f, Module.End.mul_apply, pow_succ' L, Module.End.mul_apply, ← ih, hfdef,
        LinearMap.coe_restrict_apply]
  have hkill : ∀ x : L.maxGenEigenspace 0, ∃ n, (f ^ n) x = 0 := by
    intro x
    have hx := x.2
    rw [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Subtype.ext (by rw [hpow, hn, ZeroMemClass.coe_zero])⟩
  let b := Module.finBasis ℂ (L.maxGenEigenspace 0)
  choose n hn using fun i => hkill (b i)
  refine ⟨∑ i, n i, b.ext fun i => ?_⟩
  have hle : n i ≤ ∑ i, n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hn i, map_zero,
    LinearMap.zero_apply]

end Nilpotent

/-! ### `Ω_{A'}(M)` and the regularity data of a component algebra -/

section Omega

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- `Ω_{A'}(M)` (proof of `lem:compatible-top`, line 2902): the vectors of the weak module `M`
killed by every mode `a_(n)`, `n ≥ d`, of the states `a ∈ A' ∩ V_d` (for a grading-compatible
component algebra `A' ⊆ V`, the `A'`-weight of `a` is `d`). -/
noncomputable def omegaSpace (A : VertexOperatorAlgebra ℂ V) (W : WeakModule A.toVertexAlgebra M)
    (A' : Submodule ℂ V) : Submodule ℂ M :=
  ⨅ (d : ℕ) (a : V) (_ : a ∈ A' ⊓ A.grade d) (n : ℤ) (_ : (d : ℤ) ≤ n),
    LinearMap.ker (W.act n a)

theorem mem_omegaSpace (A : VertexOperatorAlgebra ℂ V) (W : WeakModule A.toVertexAlgebra M)
    (A' : Submodule ℂ V) {v : M} :
    v ∈ omegaSpace A W A' ↔
      ∀ (d : ℕ) (a : V), a ∈ A' ⊓ A.grade d → ∀ n : ℤ, (d : ℤ) ≤ n → W.act n a v = 0 := by
  simp only [omegaSpace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **[external] Regularity of a component algebra** `A' ⊆ V` with conformal vector `e`, on the
weak module `M` (proof of `lem:compatible-top`, lines 2903–2907, and the vacuum-top step,
lines 2951–2954): `Ω_{A'}(M)` is the direct sum `⨁ₖ T k` of the tops of the simple ordinary
summands of `M↓A'` (regularity of `A'`); `L^{A'}(0) = e_(1)` acts on the top `T k` by its lowest
weight `wt k ≥ 0` (nonnegative lowest weights of the factor); and `L^{A'}(-1) = e_(0)` kills the
tops of lowest weight `0`, which are vacuum tops (the vacuum is the only weight-zero simple
`A'`-module and `L(-1)𝟏 = 0`). -/
structure ComponentTops (A : VertexOperatorAlgebra ℂ V) (W : WeakModule A.toVertexAlgebra M)
    (A' : Submodule ℂ V) (e : V) (K : Type*) [DecidableEq K] (T : K → Type*)
    [∀ k, AddCommGroup (T k)] [∀ k, Module ℂ (T k)] where
  /-- The lowest weights of the tops. -/
  wt : K → ℝ
  wt_nonneg : ∀ k, 0 ≤ wt k
  /-- `Ω_{A'}(M) ≅ ⨁ₖ T k`. -/
  eqv : omegaSpace A W A' ≃ₗ[ℂ] DirectSum K T
  L0_top : ∀ k (t : T k), W.act 1 e (eqv.symm (DirectSum.of T k t) : M) =
    (wt k : ℂ) • (eqv.symm (DirectSum.of T k t) : M)
  Lm1_vac : ∀ k (t : T k), wt k = 0 → W.act 0 e (eqv.symm (DirectSum.of T k t) : M) = 0

/-- **The vacuum-top step** (lines 2951–2954) from the regularity data: a vector of
`Ω_{A'}(M)` with zero partial energy `e_(1) v = 0` is killed by `L^{A'}(-1) = e_(0)`
(`CompatibleTop.vacuum_top_step`). -/
theorem ComponentTops.vacuumTop {A : VertexOperatorAlgebra ℂ V} {W : WeakModule A.toVertexAlgebra M}
    {A' : Submodule ℂ V} {e : V} {K : Type*} [DecidableEq K] {T : K → Type*}
    [∀ k, AddCommGroup (T k)] [∀ k, Module ℂ (T k)] (R : ComponentTops A W A' e K T) {v : M}
    (hvΩ : v ∈ omegaSpace A W A') (hv : W.act 1 e v = 0) : W.act 0 e v = 0 := by
  set z := R.eqv ⟨v, hvΩ⟩ with hz
  have hzv : (R.eqv.symm z : M) = v := by rw [hz, LinearEquiv.symm_apply_apply]
  have hℓ : diagOp R.wt z = 0 := by
    apply R.eqv.symm.injective
    apply Subtype.ext
    rw [map_zero, ZeroMemClass.coe_zero, ← transport R.wt _ R.eqv _ R.L0_top z, hzv, hv]
  have h := CompatibleTop.vacuum_top_step T (fun k => (R.wt k : ℂ)) (diagOp R.wt)
    (fun z k => diagOp_apply R.wt z k)
    ((W.act 0 e) ∘ₗ (omegaSpace A W A').subtype ∘ₗ R.eqv.symm.toLinearMap)
    (fun k x hk => R.Lm1_vac k x (by exact_mod_cast hk)) z hℓ
  have h2 : W.act 0 e (R.eqv.symm z : M) = 0 := h
  rwa [hzv] at h2

/-- **`lem:compatible-top`, "in particular"**, from the regularity data: on every
finite-dimensional subspace `F ⊆ Ω_{A'}(M)` stable under `e_(1)`, the partial energy
`L^{A'}(0) = e_(1)` is diagonalizable with nonnegative real eigenvalues. -/
theorem ComponentTops.nonnegDiagonalizable {A : VertexOperatorAlgebra ℂ V}
    {W : WeakModule A.toVertexAlgebra M} {A' : Submodule ℂ V} {e : V} {K : Type*} [DecidableEq K]
    {T : K → Type*} [∀ k, AddCommGroup (T k)] [∀ k, Module ℂ (T k)]
    (R : ComponentTops A W A' e K T) (F : Submodule ℂ M) [FiniteDimensional ℂ F]
    (hFΩ : F ≤ omegaSpace A W A') (hF : ∀ x ∈ F, W.act 1 e x ∈ F) :
    IsNonnegDiagonalizable ((W.act 1 e).restrict hF) :=
  isNonnegDiagonalizable_of_tops R.wt _ R.eqv _ R.L0_top R.wt_nonneg F hFΩ hF

end Omega

/-! ### The vacuum-top step on `N_[0]` and the splitting -/

section Main

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (A : VertexOperatorAlgebra ℂ V) (W : WeakModule A.toVertexAlgebra M)

/-- `N_[0] ⊆ Ω_{A'}(N)` when there are no negative generalized weights (lines 2962–2965). -/
theorem genZero_le_omegaSpace
    (hneg : ∀ m : ℕ, 1 ≤ m → Module.End.maxGenEigenspace (W.act 1 A.ω) (-(m : ℂ)) = ⊥)
    (A' : Submodule ℂ V) :
    Module.End.maxGenEigenspace (W.act 1 A.ω) 0 ≤ omegaSpace A W A' := by
  intro v hv
  rw [mem_omegaSpace]
  intro d a ha n hn
  exact lowering_mode_eq_zero A W hneg (Submodule.mem_inf.mp ha).2 n (by omega) hv

/-- Degree-zero modes `e_(1)` of weight-two states preserve `N_[0]` (line 2965). -/
theorem act_one_mem_genZero {e : V} (he : e ∈ A.grade 2) {v : M}
    (hv : v ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0) :
    W.act 1 e v ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0 := by
  have h := act_mem_maxGenEigenspace A W he 1 hv
  have e0 : (0 : ℂ) + (((2 : ℕ) : ℂ) - ((1 : ℤ) : ℂ) - 1) = 0 := by norm_num
  rw [e0] at h
  exact h

/-- **The vacuum-top step on `N_[0]`** (lines 2965–2970).  Let `ω = ∑ cᵢ eᵢ` with `cᵢ > 0` and
`eᵢ ∈ V₂` the conformal vectors of grading-compatible component algebras `Aᵢ`, each with the
regularity data `ComponentTops` on the weak module `N`.  If `N` has no negative generalized
`L(0)`-weights and `N_[0]` is finite-dimensional, then `L(-1) = ω_(0)` vanishes on `N_[0]`. -/
theorem omega_zero_on_genZero {N : ℕ} (c : Fin N → ℝ) (hc : ∀ i, 0 < c i) (e : Fin N → V)
    (he : ∀ i, e i ∈ A.grade 2) (hω : A.ω = ∑ i, (c i : ℂ) • e i)
    (Ac : Fin N → Submodule ℂ V) {K : Fin N → Type*} {T : ∀ i, K i → Type*}
    [∀ i k, AddCommGroup (T i k)] [∀ i k, Module ℂ (T i k)] [∀ i, DecidableEq (K i)]
    (reg : ∀ i, ComponentTops A W (Ac i) (e i) (K i) (T i))
    (hneg : ∀ m : ℕ, 1 ≤ m → Module.End.maxGenEigenspace (W.act 1 A.ω) (-(m : ℂ)) = ⊥)
    [FiniteDimensional ℂ (Module.End.maxGenEigenspace (W.act 1 A.ω) 0)] :
    ∀ v ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0, W.act 0 A.ω v = 0 := by
  intro v hv
  have hFi : ∀ i, ∀ x ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0,
      W.act 1 (e i) x ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0 :=
    fun i x hx => act_one_mem_genZero A W (he i) hx
  have hF0 : ∀ x ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0,
      W.act 1 A.ω x ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0 :=
    fun x hx => act_one_mem_genZero A W A.ω_mem hx
  have hmode : ∀ n : ℤ, W.act n A.ω = ∑ i ∈ Finset.univ, (c i : ℂ) • W.act n (e i) := by
    intro n
    rw [hω, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  have hsum_op : ∑ i ∈ Finset.univ, ((c i : ℝ) : ℂ) • (W.act 1 (e i)).restrict (hFi i) =
      (W.act 1 A.ω).restrict hF0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, LinearMap.congr_fun (hmode 1) (x : M), LinearMap.sum_apply,
      LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul,
      LinearMap.coe_restrict_apply]
  have hnil := isNilpotent_restrict_genZero (W.act 1 A.ω) hF0
  have hdiag : ∀ i ∈ Finset.univ, IsNonnegDiagonalizable ((W.act 1 (e i)).restrict (hFi i)) :=
    fun i _ => (reg i).nonnegDiagonalizable _ (genZero_le_omegaSpace A W hneg (Ac i)) (hFi i)
  have hzero := eq_zero_of_isNilpotent_sum Finset.univ c (fun i _ => hc i) _ hdiag
    (by convert hnil using 1; exact hsum_op)
  -- every partial energy vanishes on `v`
  have hLi : ∀ i, W.act 1 (e i) v = 0 := fun i => by
    have h := congrArg Subtype.val (LinearMap.congr_fun (hzero i (Finset.mem_univ i)) ⟨v, hv⟩)
    simpa only [LinearMap.coe_restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
      using h
  -- the vacuum-top step for each component
  have hvac : ∀ i, W.act 0 (e i) v = 0 := fun i =>
    (reg i).vacuumTop (genZero_le_omegaSpace A W hneg (Ac i) hv) (hLi i)
  rw [hmode 0]
  exact sum_smul_apply_eq_zero Finset.univ (fun i => (c i : ℂ)) (fun i => W.act 0 (e i))
    fun i _ => hvac i

/-- **The splitting of `lem:vacuum-projective`** (lines 2959–2978) from the regularity data alone:
for an epimorphism of modules `π : N ↠ V` (`N` spanned by its generalized `L(0)`-eigenspaces, no
negative generalized weights, `N_[0]` finite-dimensional), there is `v ∈ N_[0]` with `π v = 𝟏`
and `ω_(0) v = 0`, and `a ↦ a_(-1) v` is a module map `s : V → N` with `π ∘ s = id`. -/
theorem vacuum_splitting_of_tops {N : ℕ} (c : Fin N → ℝ) (hc : ∀ i, 0 < c i) (e : Fin N → V)
    (he : ∀ i, e i ∈ A.grade 2) (hω : A.ω = ∑ i, (c i : ℂ) • e i)
    (Ac : Fin N → Submodule ℂ V) {K : Fin N → Type*} {T : ∀ i, K i → Type*}
    [∀ i k, AddCommGroup (T i k)] [∀ i k, Module ℂ (T i k)] [∀ i, DecidableEq (K i)]
    (reg : ∀ i, ComponentTops A W (Ac i) (e i) (K i) (T i))
    (hneg : ∀ m : ℕ, 1 ≤ m → Module.End.maxGenEigenspace (W.act 1 A.ω) (-(m : ℂ)) = ⊥)
    [FiniteDimensional ℂ (Module.End.maxGenEigenspace (W.act 1 A.ω) 0)]
    (hspan : ⨆ ν, Module.End.maxGenEigenspace (W.act 1 A.ω) ν = ⊤)
    (π : M →ₗ[ℂ] V) (hsurj : Function.Surjective π)
    (hπ : ∀ (n : ℤ) (a : V) (w : M), π (W.act n a w) = A.mode n a (π w)) :
    ∃ v ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0, π v = A.vac ∧ W.act 0 A.ω v = 0 ∧
      ∃ s : V →ₗ[ℂ] M, (∀ (m : ℤ) (b a : V), s (A.mode m b a) = W.act m b (s a)) ∧
        ∀ a, π (s a) = a := by
  obtain ⟨v, hv, hπv⟩ := exists_vacuum_preimage π hsurj (W.act 1 A.ω) (A.mode 1 A.ω)
    (fun w => hπ 1 A.ω w) hspan (A.mode_vac_nonneg 1 A.ω (by norm_num))
  have h0 := omega_zero_on_genZero A W c hc e he hω Ac reg hneg v hv
  exact ⟨v, hv, hπv, h0, omega_vacuumLike_section A W h0 π hπ hπv⟩

end Main

#print axioms isNonnegDiagonalizable_of_tops
#print axioms isNilpotent_restrict_genZero
#print axioms ComponentTops.vacuumTop
#print axioms ComponentTops.nonnegDiagonalizable
#print axioms omega_zero_on_genZero
#print axioms vacuum_splitting_of_tops

end HaagerupIzumi.C8.VacuumTopZero
