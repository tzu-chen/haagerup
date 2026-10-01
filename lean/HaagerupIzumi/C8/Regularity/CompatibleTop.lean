module

public import HaagerupIzumi.C8.Regularity.Energy
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

/-!
# Lemma `lem:compatible-top`, algebraic core (lines 2890–2914)

"Let `A ⊂ V` be grading compatible and regular, and let `M` be a weak `V`-module.  Suppose a
finite-dimensional subspace `E ⊂ M` is stable under every ambient degree-zero mode from `A` and
is killed by every mode from `A` of negative ambient degree.  Then `E` is a direct sum of
irreducible Zhu-algebra modules belonging to the tops of simple ordinary `A`-modules.  In
particular `L^A(0)|_E` is diagonalizable, with eigenvalues among their lowest weights."

The proof places `E` inside `Ω_A(M)`, on which the Zhu algebra `R` acts by zero modes, and
uses regularity: `Ω_A(M)` is a direct sum of tops of simple ordinary `A`-modules.  Here `Ω` is
any `R`-module with `Ω ≃ ⨁ₖ top (j k)`, each `top j` a simple `R`-module on which
`ℓ = [ω_A]` (acting as `L^A(0)`) is the scalar `wt j`, the lowest weight:

* `exists_equiv_top`: every simple `R`-submodule of `Ω` is isomorphic to some `top (j k)`
  (a nonzero coordinate projection is an isomorphism by Schur's lemma);
* `compatible_top_sum` (first assertion): every `R`-submodule `E ⊆ Ω` is the sum of its simple
  submodules, each isomorphic to a top;
* `compatible_top` ("in particular"): every finite-dimensional `R`-submodule `E ⊆ Ω` has a basis
  of eigenvectors of `ℓ` whose eigenvalues are lowest weights;
* `compatible_top_of_directSum`: with nonnegative lowest weights, `ℓ|_E` satisfies
  `IsNonnegDiagonalizable`;
* `commutator_step`: a mode of degree `d` maps the `L(0)`-eigenspace `h` to `h + d`, so the lowest
  space is killed by lowering modes and stable under zero modes (lines 2941–2943);
* `vacuum_top_step`: if `ℓ = L^A(0)` vanishes on `v ∈ Ω`, every operator killing the weight-zero
  tops (`L^A(-1)` on vacuum tops) kills `v` — the vacuum-top step of `lem:vacuum-projective`;
* `isNonnegDiagonalizable_of_compatible`: the same for an operator `L` on a fixed space `E₀`
  (the lowest space `M_h`, or `N_[0]`) that corresponds to `ℓ|_E` under a linear isomorphism
  `E₀ ≃ E` — exactly the hypothesis `hL` of `top_trace_nonneg` in `Regularity/Energy`, one such
  datum for each component algebra `Aᵢ` (`isNonnegDiagonalizable_of_intertwine` transports the
  predicate).

Modelling step: `E` is an `R`-submodule of `Ω`, i.e. `E ⊆ Ω_A(M)` and `E` is stable under zero
modes; in the manuscript this is the commutator computation of `lem:vacuum-projective`
(lines 2941–2943), whose algebra is `commutator_step` (the commutator relation
`[L(0), a_(n)] = (wt a - n - 1) a_(n)` on modules is a hypothesis).  External inputs (hypotheses): the zero-mode action
of the Zhu algebra on `Ω_A(M)` and the decomposition `Ω_A(M) ≅ ⨁ tops` (regularity of `A`), the
simplicity of each top over the Zhu algebra, `L^A(0) = wt` on each top, and nonnegativity of
the lowest weights.  The manuscript cites nothing at this point; Zhu's theorem and
Dong–Li–Mason are the standard references (not in its bibliography).
-/

namespace HaagerupIzumi.C8.CompatibleTop

open HaagerupIzumi.C8

variable {𝕜 : Type*} [RCLike 𝕜] {R : Type*} [Ring R] [Algebra 𝕜 R]
variable {Ω : Type*} [AddCommGroup Ω] [Module R Ω] [Module 𝕜 Ω] [IsScalarTower 𝕜 R Ω]

/-- The action of `ℓ ∈ R` on an `R`-submodule `E`, as a `𝕜`-linear map of `E`. -/
def actionMap (ℓ : R) (E : Submodule R Ω) : E →ₗ[𝕜] E where
  toFun x := ℓ • x
  map_add' x y := smul_add ℓ x y
  map_smul' c x := by
    apply Subtype.ext
    show ℓ • (c • (x : Ω)) = c • (ℓ • (x : Ω))
    rw [← algebraMap_smul R c (x : Ω), ← algebraMap_smul R c (ℓ • (x : Ω)), smul_smul,
      smul_smul, Algebra.commutes]

theorem actionMap_apply (ℓ : R) (E : Submodule R Ω) (x : E) :
    ((actionMap (𝕜 := 𝕜) ℓ E x : E) : Ω) = ℓ • (x : Ω) := rfl

/-- `ℓ` acting by a scalar on `T` acts by the same scalar on any module isomorphic to `T`. -/
theorem smul_eq_of_equiv (ℓ : R) {T : Type*} [AddCommGroup T] [Module R T] (w : 𝕜)
    (hT : ∀ t : T, ℓ • t = algebraMap 𝕜 R w • t) {N : Type*} [AddCommGroup N] [Module R N]
    (φ : N ≃ₗ[R] T) (x : N) : ℓ • x = algebraMap 𝕜 R w • x := by
  apply φ.injective
  rw [map_smul, map_smul, hT]

/-- **Schur step.**  A simple submodule of `Ω ≅ ⨁ₖ T k`, each `T k` simple, is isomorphic to
some `T k`. -/
theorem exists_equiv_top {K : Type*} (T : K → Type*) [∀ k, AddCommGroup (T k)]
    [∀ k, Module R (T k)] [∀ k, IsSimpleModule R (T k)] (e : Ω ≃ₗ[R] DirectSum K T)
    (N : Submodule R Ω) [IsSimpleModule R N] : ∃ k, Nonempty (N ≃ₗ[R] T k) := by
  classical
  have : Nontrivial N := IsSimpleModule.nontrivial R N
  obtain ⟨x, hx⟩ : ∃ x : N, x ≠ 0 := exists_ne 0
  have hex : e (x : Ω) ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    apply e.injective
    rw [h, Submodule.coe_zero, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, (e (x : Ω)) k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hex (DFinsupp.ext h)
  let f : N →ₗ[R] T k := (DirectSum.component R K T k).comp (e.toLinearMap.comp N.subtype)
  have hf : f ≠ 0 := by
    intro h0
    apply hk
    have h1 : f x = 0 := by rw [h0]; rfl
    exact h1
  exact ⟨k, ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)⟩⟩

/-- **Lemma `lem:compatible-top`, first assertion.**  In a semisimple `Ω` whose simple
submodules are isomorphic to tops, every `R`-submodule `E` is the sum of its simple submodules,
each isomorphic to some `top j`. -/
theorem compatible_top_sum {J : Type*} (top : J → Type*) [∀ j, AddCommGroup (top j)]
    [∀ j, Module R (top j)] [IsSemisimpleModule R Ω]
    (htops : ∀ N : Submodule R Ω, IsSimpleModule R N → ∃ j, Nonempty (N ≃ₗ[R] top j))
    (E : Submodule R Ω) :
    sSup {N : Submodule R E | IsSimpleModule R N} = ⊤ ∧
      ∀ N : Submodule R E, IsSimpleModule R N → ∃ j, Nonempty (N ≃ₗ[R] top j) := by
  refine ⟨IsSemisimpleModule.sSup_simples_eq_top R E, fun N hN => ?_⟩
  have hN' : IsSimpleModule R (N.map E.subtype) :=
    IsSimpleModule.congr (Submodule.equivMapOfInjective E.subtype Subtype.val_injective N).symm
  obtain ⟨j, ⟨φ⟩⟩ := htops _ hN'
  exact ⟨j, ⟨(Submodule.equivMapOfInjective E.subtype Subtype.val_injective N).trans φ⟩⟩

/-- **Lemma `lem:compatible-top`, eigenbasis.**  Let `Ω` be a semisimple `R`-module each of
whose simple submodules is isomorphic to some `top j`, on which `ℓ` is the scalar `wt j`.
Every finite-dimensional `R`-submodule `E` has a basis of eigenvectors of `ℓ` with eigenvalues
among the `wt j`. -/
theorem compatible_top (ℓ : R) {J : Type*} (top : J → Type*) [∀ j, AddCommGroup (top j)]
    [∀ j, Module R (top j)] (wt : J → 𝕜) (hwt : ∀ j (t : top j), ℓ • t = algebraMap 𝕜 R (wt j) • t)
    [IsSemisimpleModule R Ω]
    (htops : ∀ N : Submodule R Ω, IsSimpleModule R N → ∃ j, Nonempty (N ≃ₗ[R] top j))
    (E : Submodule R Ω) [FiniteDimensional 𝕜 E] :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) 𝕜 E) (μ : Fin m → J),
      ∀ i, actionMap (𝕜 := 𝕜) ℓ E (b i) = wt (μ i) • b i := by
  classical
  let s : Set E := {y | ∃ j, actionMap (𝕜 := 𝕜) ℓ E y = wt j • y}
  have hsimple : ∀ N : Submodule R E, IsSimpleModule R N → ∀ y ∈ N, y ∈ s := by
    intro N hN y hy
    have hN' : IsSimpleModule R (N.map E.subtype) :=
      IsSimpleModule.congr (Submodule.equivMapOfInjective E.subtype Subtype.val_injective N).symm
    obtain ⟨j, ⟨φ⟩⟩ := htops _ hN'
    have h := smul_eq_of_equiv ℓ (wt j) (hwt j) φ ⟨(y : Ω), Submodule.mem_map_of_mem hy⟩
    refine ⟨j, Subtype.ext ?_⟩
    have h' := congrArg Subtype.val h
    rw [actionMap_apply, Submodule.coe_smul_of_tower, ← algebraMap_smul R (wt j) (y : Ω)]
    simpa using h'
  have hspan : Submodule.span 𝕜 s = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ sSup {m : Submodule R E | IsSimpleModule R m} := by
      rw [IsSemisimpleModule.sSup_simples_eq_top]
      trivial
    rw [sSup_eq_iSup'] at hy
    refine Submodule.iSup_induction _ (motive := fun y => y ∈ Submodule.span 𝕜 s) hy ?_ ?_ ?_
    · intro N z hz
      exact Submodule.subset_span (hsimple N.1 N.2 z hz)
    · exact Submodule.zero_mem _
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent 𝕜 s
  have htop : ⊤ ≤ Submodule.span 𝕜 (Set.range ((↑) : b → E)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B := Module.Basis.mk hli htop
  haveI : Finite b := Module.Finite.finite_basis B
  letI : Fintype b := Fintype.ofFinite b
  refine ⟨Fintype.card b, B.reindex (Fintype.equivFin b),
    fun i => Classical.choose (hbs ((Fintype.equivFin b).symm i).2), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact Classical.choose_spec (hbs ((Fintype.equivFin b).symm i).2)

/-- **Lemma `lem:compatible-top`.**  If `Ω ≅ ⨁ₖ top (j k)` (regularity: `Ω_A(M)` is the direct
sum of the tops of the simple ordinary summands of `M`), each top a simple `R`-module on which
`ℓ = [ω_A]` acts by its lowest weight `wt j ≥ 0`, then for every finite-dimensional
`R`-submodule `E ⊆ Ω`, `ℓ|_E` is diagonalizable with nonnegative real eigenvalues — the input
`IsNonnegDiagonalizable` of the trace step `eq:top-trace`. -/
theorem compatible_top_of_directSum (ℓ : R) {J : Type*} (top : J → Type*)
    [∀ j, AddCommGroup (top j)] [∀ j, Module R (top j)] [∀ j, IsSimpleModule R (top j)]
    (wt : J → ℝ) (hwt0 : ∀ j, 0 ≤ wt j)
    (hwt : ∀ j (t : top j), ℓ • t = algebraMap 𝕜 R (wt j : 𝕜) • t)
    {K : Type*} (jk : K → J) (e : Ω ≃ₗ[R] DirectSum K (fun k => top (jk k)))
    (E : Submodule R Ω) [FiniteDimensional 𝕜 E] :
    IsNonnegDiagonalizable (actionMap (𝕜 := 𝕜) ℓ E) := by
  classical
  have hsup : ⨆ k, LinearMap.range
      (e.symm.toLinearMap ∘ₗ DirectSum.lof R K (fun k => top (jk k)) k) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [← e.symm_apply_apply x]
    generalize e x = y
    induction y using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of k t =>
      exact Submodule.mem_iSup_of_mem k ⟨t, by simp [DirectSum.lof_eq_of]⟩
    | add a c ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
  haveI : IsSemisimpleModule R Ω :=
    isSemisimpleModule_of_isSemisimpleModule_submodule' (fun k => .range _) hsup
  have htops : ∀ N : Submodule R Ω, IsSimpleModule R N → ∃ j, Nonempty (N ≃ₗ[R] top j) :=
    fun N _ => let ⟨k, hk⟩ := exists_equiv_top _ e N; ⟨jk k, hk⟩
  obtain ⟨m, b, μ, hb⟩ := compatible_top ℓ top (fun j => (wt j : 𝕜)) hwt htops E
  exact IsNonnegDiagonalizable.of_basis b (fun i => wt (μ i)) (fun i => hwt0 _) _ hb

/-- `IsNonnegDiagonalizable` transports along a linear isomorphism intertwining the operators. -/
theorem isNonnegDiagonalizable_of_intertwine {E₀ E₁ : Type*} [AddCommGroup E₀] [Module 𝕜 E₀]
    [AddCommGroup E₁] [Module 𝕜 E₁] (e : E₀ ≃ₗ[𝕜] E₁) {L₀ : E₀ →ₗ[𝕜] E₀} {L₁ : E₁ →ₗ[𝕜] E₁}
    (h : ∀ x, e (L₀ x) = L₁ (e x)) (hL : IsNonnegDiagonalizable L₁) :
    IsNonnegDiagonalizable L₀ := by
  obtain ⟨m, b, μ, hμ, hb⟩ := hL
  refine ⟨m, b.map e.symm, μ, hμ, fun k => ?_⟩
  rw [Module.Basis.map_apply]
  apply e.injective
  rw [h, LinearEquiv.apply_symm_apply, hb, map_smul, LinearEquiv.apply_symm_apply]

/-- **Lemma `lem:compatible-top` for an operator on a fixed space.**  If `L` on `E₀` (e.g.
`L^{eᵢ}(0)` on the lowest space `M_h`) corresponds, under a linear isomorphism `e : E₀ ≃ E`, to
the action of `ℓ` on a finite-dimensional `R`-submodule `E ⊆ Ω ≅ ⨁ tops`, then `L` is
diagonalizable with nonnegative real eigenvalues.  This is the hypothesis `hL` of
`top_trace_nonneg` (`Regularity/Energy`), supplied once for each component algebra. -/
theorem isNonnegDiagonalizable_of_compatible (ℓ : R) {J : Type*} (top : J → Type*)
    [∀ j, AddCommGroup (top j)] [∀ j, Module R (top j)] [∀ j, IsSimpleModule R (top j)]
    (wt : J → ℝ) (hwt0 : ∀ j, 0 ≤ wt j)
    (hwt : ∀ j (t : top j), ℓ • t = algebraMap 𝕜 R (wt j : 𝕜) • t)
    {K : Type*} (jk : K → J) (eΩ : Ω ≃ₗ[R] DirectSum K (fun k => top (jk k)))
    (E : Submodule R Ω) [FiniteDimensional 𝕜 E]
    {E₀ : Type*} [AddCommGroup E₀] [Module 𝕜 E₀] (L : E₀ →ₗ[𝕜] E₀) (e : E₀ ≃ₗ[𝕜] E)
    (he : ∀ x, ((e (L x) : E) : Ω) = ℓ • ((e x : E) : Ω)) :
    IsNonnegDiagonalizable L :=
  isNonnegDiagonalizable_of_intertwine e (L₁ := actionMap (𝕜 := 𝕜) ℓ E)
    (fun x => Subtype.ext (by rw [actionMap_apply]; exact he x))
    (compatible_top_of_directSum ℓ top wt hwt0 hwt jk eΩ E)

/-- **The commutator step of `lem:vacuum-projective`** (lines 2941–2943).  If
`[L(0), A] = d·A` (for `A = a_(n)`, `d = wt a - n - 1`) and `L(0) v = h v`, then
`L(0)(A v) = (h + d) A v`.  So on the lowest space `E = M_h` (no eigenvalue `h + d` when `d < 0`)
lowering modes vanish, and degree-zero modes (`d = 0`) preserve `E`: `E` lies in `Ω_A(M)` and is
stable under zero modes.  The commutator relation itself (module Jacobi identity) is a
hypothesis. -/
theorem commutator_step {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (L0 A : M →ₗ[k] M) (d h : k) (hcomm : ∀ w, L0 (A w) = A (L0 w) + d • A w) {v : M}
    (hv : L0 v = h • v) :
    L0 (A v) = (h + d) • A v ∧ ((∀ w, L0 w = (h + d) • w → w = 0) → A v = 0) := by
  have h1 : L0 (A v) = (h + d) • A v := by rw [hcomm, hv, map_smul, add_smul]
  exact ⟨h1, fun hlow => hlow _ h1⟩

/-- **The vacuum-top step of `lem:vacuum-projective`** (lines 2951–2954).  Let
`Ω = ⨁ₖ Tₖ` (the tops of the simple summands of `M↓A`), with `ℓ = L^A(0)` acting on `Tₖ` by the
lowest weight `wₖ`, and let `D = L^A(-1)` kill the tops of weight zero (these are vacuum tops:
the vacuum is the only simple of weight zero, and `L(-1)𝟏 = 0`; external input).  If `ℓ v = 0`
then `D v = 0`.  Applied to every `v ∈ E` with `L^{eᵢ}(0)|_E = 0`, this gives
`L^{eᵢ}(-1)E = 0`. -/
theorem vacuum_top_step {K : Type*} [DecidableEq K] (T : K → Type*) [∀ k, AddCommGroup (T k)]
    [∀ k, Module 𝕜 (T k)] (w : K → 𝕜) {M' : Type*} [AddCommGroup M'] [Module 𝕜 M']
    (ℓ : DirectSum K T →ₗ[𝕜] DirectSum K T) (hℓ : ∀ v k, ℓ v k = w k • v k)
    (D : DirectSum K T →ₗ[𝕜] M') (hD : ∀ k (x : T k), w k = 0 → D (DirectSum.of T k x) = 0)
    (v : DirectSum K T) (hv : ℓ v = 0) : D v = 0 := by
  classical
  rw [← DirectSum.sum_support_of v, map_sum]
  refine Finset.sum_eq_zero fun k hk => hD k _ ?_
  have h1 : w k • v k = 0 := by
    rw [← hℓ, hv]
    rfl
  by_contra hw
  apply DFinsupp.mem_support_iff.1 hk
  calc v k = (w k)⁻¹ • (w k • v k) := by rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
    _ = 0 := by rw [h1, smul_zero]

#print axioms compatible_top_sum
#print axioms vacuum_top_step
#print axioms commutator_step
#print axioms compatible_top
#print axioms compatible_top_of_directSum
#print axioms isNonnegDiagonalizable_of_compatible

end HaagerupIzumi.C8.CompatibleTop
