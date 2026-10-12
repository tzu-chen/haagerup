module

public import HaagerupIzumi.C8.ProofMapConcreteRegularity
public import HaagerupIzumi.C8.ProofMapConcreteCharacters
public import HaagerupIzumi.C8.ProofMapSimples
public import HaagerupIzumi.C8.Regularity.NoNegativeWeights
public import HaagerupIzumi.C8.Regularity.VacuumTopZero

@[expose] public section

/-!
# The projective-vacuum arrow of the proof map, made concrete

Lemma `lem:vacuum-projective` (lines 2931–2978 of `c8_expanded_20260929/haagerup_c8_expanded.tex`),
with Lemmas `lem:compatible-top` (2889–2914) and `lem:vacuum-like` (2916–2929), is the arrow

* `L_projectiveVacuum : positiveStress → c2Cofinite → initialGrades → projectiveVacuum`.

The concrete objects are those of the regularity branch (`StressData`): the vertex operator algebra
`U = S.U` over `ℂ` on `H`, the conformal vector, and the orbits `S.K k` of the four factor conformal
vectors.  A module is a `VacuumLike.WeakModule` over `U` on a type `M : Type` (modes `a_(n)` acting
on `M`, lower truncation, vacuum axiom, translation covariance, iterate formula), with
`L_M(0) = ω_(1)`.

`vacuumNodes R S SD` overrides `projectiveVacuum` by the conjunction of

* `LowestWeightsNonneg S`: for every weak module and every `h ∈ ℂ` that is a lowest weight
  (`IsLowestWeight`: the `L(0)`-eigenspace `M_h` is finite-dimensional and nonzero, and there is no
  eigenvalue `h - m`, `m ≥ 1`), `h` is real and `≥ 0`, and if `h = 0` there is a nonzero module map
  `U → M` (so a simple `M` of weight zero is `U`);
* `VacuumIsProjective S`: every epimorphism `π : N ↠ U` from a grading-restricted generalized module
  (`IsGRGModule`) that intertwines the modes splits by a module map;
* for the simple `U`-modules `s : Simp` (`SimpleData`, not yet identified with the twelve labels),
  `0 ≤ hw s`, and `hw s = 0` only for the class of `U`.

The label-specific consequence "`b, a, c₀` have no weight-zero vectors" used by the character arrow
is `noWeightZero_of_vacuum`, applied after the identification of the simples with the labels
(`SimpleLabels`, conditional on `modularData`).

The concrete theorems used: `CompatibleTop.commutator_step` via
`VacuumProjective.module_commutator_step` and `VacuumProjective.act_mem_maxGenEigenspace`
(degree-zero modes preserve, lowering modes kill the lowest space and `N_[0]`),
`VacuumProjective.lowering_mode_eq_zero`, `exists_real_nonneg_of_top_trace` (eq:top-trace),
`eq_zero_of_top_trace_eq_zero`, `eq_zero_of_isNilpotent_sum` (Regularity/Energy),
`VacuumLike.vacuumLike_module_map`, and for the splitting
`VacuumTopZero.vacuum_splitting_of_tops` (the vacuum-top step on `N_[0]`,
`VacuumTopZero.omega_zero_on_genZero`, then `VacuumProjective.exists_vacuum_preimage` and
`VacuumProjective.omega_vacuumLike_section`).  Lemma `lem:compatible-top`'s diagonalizability and
the vacuum-top step are derived from one regularity input (`HasComponentTops`:
`VacuumTopZero.ComponentTops.nonnegDiagonalizable`, `VacuumTopZero.ComponentTops.vacuumTop`).  The
remaining inputs (`VacuumInputs`) are tagged in their docstrings.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Characters HaagerupIzumi.C8.VacuumLike
  HaagerupIzumi.C8.VacuumProjective Module

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Modules, compatible subspaces, lowest weights -/

section Defs

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The hypotheses of Lemma `lem:compatible-top` for a subspace `F` of a weak `U`-module:
finite-dimensional, stable under the degree-zero modes and killed by the lowering modes (of all
homogeneous states of `U`, in particular of the component algebras). -/
def CompatibleSubspace (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M)
    (F : Submodule ℂ M) : Prop :=
  FiniteDimensional ℂ F ∧
    (∀ (d : ℕ) (a : H), a ∈ S.U.grade d → ∀ n : ℤ, (d : ℤ) - n - 1 = 0 → ∀ w ∈ F,
      W.act n a w ∈ F) ∧
    (∀ (d : ℕ) (a : H), a ∈ S.U.grade d → ∀ n : ℤ, (d : ℤ) - n - 1 < 0 → ∀ w ∈ F,
      W.act n a w = 0)

/-- The partial energy `L^z(0) = z_(1)` of a weight-two state preserves a compatible subspace. -/
theorem CompatibleSubspace.mapsTo {S : StressData E H} {W : WeakModule S.U.toVertexAlgebra M}
    {F : Submodule ℂ M} (hF : CompatibleSubspace S W F) (z : E) :
    ∀ w ∈ F, W.act 1 (S.ιE z) w ∈ F :=
  hF.2.1 2 _ (S.ιE_grade z) 1 (by norm_num)

/-- A nonzero module map `U → M`. -/
def NonzeroVacuumMap (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M) : Prop :=
  ∃ φ : H →ₗ[ℂ] M, φ S.U.vac ≠ 0 ∧ ∀ (m : ℤ) (b a : H), φ (S.U.mode m b a) = W.act m b (φ a)

/-- `h` is the lowest weight of `M`: the eigenspace `M_h` of `L(0)` is finite-dimensional and
nonzero, and `L(0)` has no eigenvalue `h - m` for integers `m ≥ 1`. -/
def IsLowestWeight (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M) (h : ℂ) : Prop :=
  FiniteDimensional ℂ (Module.End.eigenspace (W.act 1 S.U.ω) h) ∧
    Module.End.eigenspace (W.act 1 S.U.ω) h ≠ ⊥ ∧
    ∀ m : ℕ, 1 ≤ m → ∀ w, W.act 1 S.U.ω w = (h - m) • w → w = 0

/-- `M` is a grading-restricted generalized module: it is spanned by the generalized
`L(0)`-eigenspaces `M_[ν]`, each finite-dimensional, with the nilpotent part of `L(0)` of bounded
order on each (automatic for a finite-dimensional `M_[ν]`). -/
def IsGRGModule (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M) : Prop :=
  (⨆ ν, Module.End.maxGenEigenspace (W.act 1 S.U.ω) ν = ⊤) ∧
    ∀ ν, FiniteDimensional ℂ (Module.End.maxGenEigenspace (W.act 1 S.U.ω) ν) ∧
      ∃ j : ℕ, ∀ w ∈ Module.End.maxGenEigenspace (W.act 1 S.U.ω) ν,
        ((W.act 1 S.U.ω - ν • 1) ^ j) w = 0

end Defs

/-- Every simple ordinary `U`-module has a real nonnegative lowest weight, and weight zero only
admits a nonzero module map from `U` (first two assertions of `lem:vacuum-projective`). -/
def LowestWeightsNonneg (S : StressData E H) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (W : WeakModule S.U.toVertexAlgebra M) (h : ℂ),
    IsLowestWeight S W h → (∃ r : ℝ, 0 ≤ r ∧ h = r) ∧ (h = 0 → NonzeroVacuumMap S W)

/-- `U` is projective among grading-restricted generalized modules: every epimorphism onto `U`
splits (third assertion of `lem:vacuum-projective`). -/
def VacuumIsProjective (S : StressData E H) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (W : WeakModule S.U.toVertexAlgebra M)
    (π : M →ₗ[ℂ] H), IsGRGModule S W → Function.Surjective π →
    (∀ (n : ℤ) (a : H) (w : M), π (W.act n a w) = S.U.mode n a (π w)) →
    ∃ s : H →ₗ[ℂ] M, (∀ (m : ℤ) (b a : H), s (S.U.mode m b a) = W.act m b (s a)) ∧
      ∀ a, π (s a) = a

/-- The concrete `projectiveVacuum` node. -/
def VacuumNode {Simp : Type*} (S : StressData E H) (SD : SimpleData Simp) : Prop :=
  LowestWeightsNonneg S ∧ VacuumIsProjective S ∧ ∀ s, 0 ≤ SD.hw s ∧ (SD.hw s = 0 → s = SD.vac)

/-- The proof map with `projectiveVacuum` made concrete. -/
def vacuumNodes {Simp : Type*} (R : Nodes) (S : StressData E H) (SD : SimpleData Simp) : Nodes :=
  { R with projectiveVacuum := VacuumNode S SD }

/-! ### Remaining inputs -/

/-- The regularity data (`VacuumTopZero.ComponentTops`) of the component algebra with conformal
vector `ιE z` on the weak module `W`: a grading-compatible subspace `A' ⊆ U` and a decomposition
`Ω_{A'}(M) ≅ ⨁ₖ T k` into tops on which `L^{A'}(0)` acts by lowest weights `≥ 0` and
`L^{A'}(-1)` kills the weight-zero tops. -/
def HasComponentTops (S : StressData E H) {M : Type} [AddCommGroup M] [Module ℂ M]
    (W : WeakModule S.U.toVertexAlgebra M) (z : E) : Prop :=
  ∃ (A' : Submodule ℂ H) (K : Type) (_ : DecidableEq K) (T : K → Type)
    (_ : ∀ k, AddCommGroup (T k)) (_ : ∀ k, Module ℂ (T k)),
    Nonempty (VacuumTopZero.ComponentTops S.U W A' (S.ιE z) K T)

/-- The remaining inputs of `L_projectiveVacuum`, tagged.  The factor properties are stated
conditionally on `∀ k, S.factorNonneg k` (the last conjunct of the concrete `positiveStress`),
finite length conditionally on the concrete `c2Cofinite`, and the labels on the opaque part `init`
of `initialGrades`. -/
structure VacuumInputs {Simp : Type*} (S : StressData E H) (SD : SimpleData Simp) (init : Prop) :
    Prop where
  /-- [external] **regularity of the component algebras** (proof of `lem:compatible-top`,
  lines 2903–2907, and the vacuum-top step, lines 2951–2954): for every orbit point `z` of a factor
  conformal vector and every weak `U`-module, `HasComponentTops` — `Ω_{A_z}(M)` is the direct sum of
  the tops of the simple ordinary summands of `M↓A_z` (regularity of the factor), `L^{A_z}(0)` acts
  on them by their lowest weights, which are `≥ 0` (`factorNonneg`, lines 2719–2721), and
  `L^{A_z}(-1)` kills the weight-zero (vacuum) tops (the vacuum is the only weight-zero simple
  of the factor, `L(-1)𝟏 = 0`).  The diagonalizability of `lem:compatible-top` and the vacuum-top
  step are derived from it (`compat_of_reg`, `vtop_of_reg`). -/
  reg : (∀ k, S.factorNonneg k) → ∀ k, ∀ z ∈ S.K k, ∀ (M : Type) [AddCommGroup M]
    [Module ℂ M] (W : WeakModule S.U.toVertexAlgebra M), HasComponentTops S W z
  /-- [external] finite length of grading-restricted generalized modules of a `C₂`-cofinite VOA
  (Huang; Miyamoto; lines 2959–2961), [standard] its composition factors are simple ordinary
  modules, to which the first assertion (`LowestWeightsNonneg`, proved below) applies; the linear
  algebra is `VacuumProjective.maxGenEigenspace_eq_bot_of_filtration`: no generalized weight
  `-m`, `m ≥ 1`. -/
  noNeg : FiniteDimensional ℂ (H ⧸ C2 S.U) → LowestWeightsNonneg S →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (W : WeakModule S.U.toVertexAlgebra M),
    IsGRGModule S W → ∀ m : ℕ, 1 ≤ m →
      Module.End.maxGenEigenspace (W.act 1 S.U.ω) (-(m : ℂ)) = ⊥
  /-- [definitional] `s : Simp` is the isomorphism class of a simple ordinary `U`-module with lowest
  weight `SD.hw s`; [standard] Schur: a nonzero module map from the simple `U` to a simple module
  is an isomorphism, and `SD.vac` is the class of `U` (CFT type, node `initialGrades`). -/
  labels : init → ∀ s, ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M)
    (W : WeakModule S.U.toVertexAlgebra M),
    IsLowestWeight S W (SD.hw s : ℂ) ∧ (NonzeroVacuumMap S W → s = SD.vac)

/-! ### The proof -/

section Proof

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- `ω_(n) = ∑ cᵢ (zᵢ)_(n)` on a module, from `ω = ∑ cᵢ zᵢ` in `E`. -/
theorem act_omega_eq_sum (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M) {N : ℕ}
    (z : Fin N → E) (c : Fin N → ℝ) (hωz : S.ω = ∑ i, c i • z i) (n : ℤ) (w : M) :
    W.act n S.U.ω w = ∑ i, (c i : ℂ) • W.act n (S.ιE (z i)) w := by
  have hιsum : S.ιE (∑ i, c i • z i) = ∑ i, (c i : ℂ) • S.ιE (z i) := by
    have h := map_sum (AddMonoidHom.mk' S.ιE S.ιE_add) (fun i => c i • z i) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => S.ιE_smul (c i) (z i)
  rw [← S.ιE_ω, hωz, hιsum, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply]

/-- A restriction killed by a fixed power is nilpotent. -/
theorem isNilpotent_restrict_of_pow (f : Module.End ℂ M) (F : Submodule ℂ M)
    (hF : ∀ x ∈ F, f x ∈ F) (j : ℕ) (hj : ∀ x ∈ F, (f ^ j) x = 0) :
    IsNilpotent (f.restrict hF) :=
  ⟨j, LinearMap.ext fun x => Subtype.ext (by
    rw [Module.End.pow_restrict j hF, LinearMap.coe_restrict_apply, LinearMap.zero_apply,
      ZeroMemClass.coe_zero]
    exact hj x x.2)⟩

/-- `((d : ℂ) - n - 1)` from the integer `d - n - 1`. -/
theorem cast_shift (d : ℕ) (n : ℤ) : ((d : ℂ) - n - 1) = (((d : ℤ) - n - 1 : ℤ) : ℂ) := by
  simp

/-- The lowest space `M_h` is a compatible subspace (lines 2941–2943). -/
theorem lowest_compatible (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M) {h : ℂ}
    (hL : IsLowestWeight S W h) :
    CompatibleSubspace S W (Module.End.eigenspace (W.act 1 S.U.ω) h) := by
  refine ⟨hL.1, ?_, ?_⟩
  · intro d a ha n hdn w hw
    have hv : W.act 1 S.U.ω w = h • w := Module.End.mem_eigenspace_iff.mp hw
    have h1 := (module_commutator_step S.U W ha n hv).1
    rw [cast_shift, hdn, Int.cast_zero, add_zero] at h1
    exact Module.End.mem_eigenspace_iff.mpr h1
  · intro d a ha n hdn w hw
    have hv : W.act 1 S.U.ω w = h • w := Module.End.mem_eigenspace_iff.mp hw
    refine (module_commutator_step S.U W ha n hv).2 fun x hx => ?_
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -((d : ℤ) - n - 1) := ⟨(-((d : ℤ) - n - 1)).toNat, by omega⟩
    refine hL.2.2 m (by omega) x ?_
    have e : ((d : ℤ) - n - 1) = -(m : ℤ) := by omega
    rw [hx, cast_shift, e, Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]

/-- The generalized weight-zero space of a grading-restricted generalized module without negative
integral weights is a compatible subspace (lines 2959–2966). -/
theorem genZero_compatible (S : StressData E H) (W : WeakModule S.U.toVertexAlgebra M)
    (hG : IsGRGModule S W)
    (hneg : ∀ m : ℕ, 1 ≤ m → Module.End.maxGenEigenspace (W.act 1 S.U.ω) (-(m : ℂ)) = ⊥) :
    CompatibleSubspace S W (Module.End.maxGenEigenspace (W.act 1 S.U.ω) 0) := by
  refine ⟨(hG.2 0).1, ?_, ?_⟩
  · intro d a ha n hdn w hw
    have h := act_mem_maxGenEigenspace S.U W ha n hw
    rw [cast_shift, hdn, Int.cast_zero, add_zero] at h
    exact h
  · intro d a ha n hdn w hw
    exact lowering_mode_eq_zero S.U W hneg ha n hdn hw

/-- A compatible subspace lies in `Ω_{A'}(M)` for every `A' ⊆ U`. -/
theorem CompatibleSubspace.le_omegaSpace {S : StressData E H} {W : WeakModule S.U.toVertexAlgebra M}
    {F : Submodule ℂ M} (hF : CompatibleSubspace S W F) (A' : Submodule ℂ H) :
    F ≤ VacuumTopZero.omegaSpace S.U W A' := by
  intro v hv
  rw [VacuumTopZero.mem_omegaSpace]
  intro d a ha n hn
  exact hF.2.2 d a (Submodule.mem_inf.mp ha).2 n (by omega) v hv

end Proof

/-- **`lem:compatible-top`, "in particular", from the regularity input**: on a compatible subspace
the partial energy of every orbit point is diagonalizable with nonnegative eigenvalues
(`VacuumTopZero.ComponentTops.nonnegDiagonalizable`). -/
theorem compat_of_reg {Simp : Type*} {S : StressData E H} {SD : SimpleData Simp} {init : Prop}
    (I : VacuumInputs S SD init) (hnonneg : ∀ k, S.factorNonneg k) {k : Fin 4} {z : E}
    (hz : z ∈ S.K k) {M : Type} [AddCommGroup M] [Module ℂ M]
    (W : WeakModule S.U.toVertexAlgebra M) (F : Submodule ℂ M) (hF : CompatibleSubspace S W F) :
    IsNonnegDiagonalizable ((W.act 1 (S.ιE z)).restrict (hF.mapsTo z)) := by
  obtain ⟨A', K, _, T, _, _, ⟨R⟩⟩ := I.reg hnonneg k z hz M W
  have : FiniteDimensional ℂ F := hF.1
  exact R.nonnegDiagonalizable F (hF.le_omegaSpace A') (hF.mapsTo z)

/-- **The vacuum-top step from the regularity input**: on a compatible subspace, `z_(1) v = 0`
implies `z_(0) v = 0` (`VacuumTopZero.ComponentTops.vacuumTop`). -/
theorem vtop_of_reg {Simp : Type*} {S : StressData E H} {SD : SimpleData Simp} {init : Prop}
    (I : VacuumInputs S SD init) (hnonneg : ∀ k, S.factorNonneg k) {k : Fin 4} {z : E}
    (hz : z ∈ S.K k) {M : Type} [AddCommGroup M] [Module ℂ M]
    (W : WeakModule S.U.toVertexAlgebra M) (F : Submodule ℂ M) (hF : CompatibleSubspace S W F)
    {v : M} (hv : v ∈ F) (h1 : W.act 1 (S.ιE z) v = 0) : W.act 0 (S.ιE z) v = 0 := by
  obtain ⟨A', K, _, T, _, _, ⟨R⟩⟩ := I.reg hnonneg k z hz M W
  exact R.vacuumTop (hF.le_omegaSpace A' hv) h1

/-- **`L_projectiveVacuum`** (Lemma `lem:vacuum-projective`, lines 2931–2978).

* Concrete nodes: `positiveStress` (the finite identity `ω = ∑ cᵢ zᵢ` with `cᵢ > 0`, and the
  factor properties `factorNonneg` to which `compat`, `vtop` are applied), `c2Cofinite` (to which
  `noNeg` is applied), `projectiveVacuum` (`VacuumNode`).  The opaque part `init` of
  `initialGrades` is applied to `labels`.
* Concrete argument: lowest spaces and `N_[0]` are compatible subspaces (`lowest_compatible`,
  `genZero_compatible`, from the module commutator relation and `lowering_mode_eq_zero`); on them
  `L(0) = ∑ cᵢ L^{zᵢ}(0)` (`act_omega_eq_sum`); eq:top-trace gives `h ≥ 0`
  (`exists_real_nonneg_of_top_trace`); for `h = 0` and on the nilpotent `N_[0]` every partial energy
  vanishes (`eq_zero_of_top_trace_eq_zero`, `eq_zero_of_isNilpotent_sum`), hence (vacuum-top step)
  `L(-1) = ω_(0) = ∑ cᵢ (zᵢ)_(0)` vanishes there, and `lem:vacuum-like` gives the nonzero map
  `U → M` (`vacuumLike_module_map`) resp. the section (`exists_vacuum_preimage`,
  `omega_vacuumLike_section`).
* Remaining inputs: the fields of `VacuumInputs`. -/
theorem projectiveVacuum_arrow {Simp : Type*} (R : Nodes) (S : StressData E H)
    (SD : SimpleData Simp) (init : Prop) (I : VacuumInputs S SD init) :
    (regularityNodes R S).positiveStress → FiniteDimensional ℂ (H ⧸ C2 S.U) → init →
      VacuumNode S SD := by
  rintro ⟨⟨N, z, c, src, hz, hc, hωz⟩, -, hnonneg⟩ hc2 hinit
  have hsum_op : ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (W : WeakModule S.U.toVertexAlgebra M) (F : Submodule ℂ M) (hF : CompatibleSubspace S W F)
      (hF0 : ∀ x ∈ F, W.act 1 S.U.ω x ∈ F),
      ∑ i ∈ Finset.univ, ((c i : ℝ) : ℂ) • (W.act 1 (S.ιE (z i))).restrict (hF.mapsTo (z i)) =
        (W.act 1 S.U.ω).restrict hF0 := by
    intro M _ _ W F hF hF0
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, act_omega_eq_sum S W z c hωz 1 (x : M), LinearMap.sum_apply,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.coe_restrict_apply]
  -- partial energies vanish ⇒ `ω_(0)` vanishes (vacuum-top step)
  have hvac : ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (W : WeakModule S.U.toVertexAlgebra M) (F : Submodule ℂ M) (hF : CompatibleSubspace S W F),
      (∀ i, (W.act 1 (S.ιE (z i))).restrict (hF.mapsTo (z i)) = 0) →
      ∀ v ∈ F, W.act 0 S.U.ω v = 0 := by
    intro M _ _ W F hF hzero v hv
    rw [act_omega_eq_sum S W z c hωz 0 v]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : W.act 1 (S.ιE (z i)) v = 0 := by
      have := congrArg Subtype.val (LinearMap.congr_fun (hzero i) ⟨v, hv⟩)
      simpa only [LinearMap.coe_restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
        using this
    rw [vtop_of_reg I hnonneg (hz i) W F hF hv h1, smul_zero]
  -- first assertion
  have hLW : LowestWeightsNonneg S := by
    intro M _ _ W h hL
    have hF := lowest_compatible S W hL
    have : FiniteDimensional ℂ (Module.End.eigenspace (W.act 1 S.U.ω) h) := hL.1
    have : Nontrivial (Module.End.eigenspace (W.act 1 S.U.ω) h) :=
      Submodule.nontrivial_iff_ne_bot.mpr hL.2.1
    have hF0 : ∀ x ∈ Module.End.eigenspace (W.act 1 S.U.ω) h,
        W.act 1 S.U.ω x ∈ Module.End.eigenspace (W.act 1 S.U.ω) h := fun x hx =>
          hF.2.1 2 _ S.U.ω_mem 1 (by norm_num) x hx
    have hid : (W.act 1 S.U.ω).restrict hF0 = h • LinearMap.id :=
      LinearMap.ext fun x => Subtype.ext (by
        rw [LinearMap.coe_restrict_apply]
        exact Module.End.mem_eigenspace_iff.mp x.2)
    have hsum := (hsum_op W _ hF hF0).trans hid
    have hdiag : ∀ i ∈ Finset.univ,
        IsNonnegDiagonalizable ((W.act 1 (S.ιE (z i))).restrict (hF.mapsTo (z i))) :=
      fun i _ => compat_of_reg I hnonneg (hz i) W _ hF
    refine ⟨exists_real_nonneg_of_top_trace Finset.univ c (fun i _ => (hc i).le) _ hdiag h hsum,
      fun h0 => ?_⟩
    have hzero := eq_zero_of_top_trace_eq_zero Finset.univ c (fun i _ => hc i) _ hdiag h hsum h0
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL.2.1
    obtain ⟨φ, hφ1, hφ⟩ := vacuumLike_module_map (omegaModule S.U W)
      (hvac W _ hF (fun i => hzero i (Finset.mem_univ i)) v hv)
    exact ⟨φ, by rw [hφ1]; exact hv0, hφ⟩
  -- projectivity: `VacuumTopZero.vacuum_splitting_of_tops`
  have hω : S.U.ω = ∑ i, (c i : ℂ) • S.ιE (z i) := by
    have h := map_sum (AddMonoidHom.mk' S.ιE S.ιE_add) (fun i => c i • z i) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at h
    rw [← S.ιE_ω, hωz, h]
    exact Finset.sum_congr rfl fun i _ => S.ιE_smul (c i) (z i)
  have hproj : VacuumIsProjective S := by
    intro M _ _ W π hG hsurj hπ
    have hneg := I.noNeg hc2 hLW M W hG
    have : FiniteDimensional ℂ (Module.End.maxGenEigenspace (W.act 1 S.U.ω) 0) := (hG.2 0).1
    have hreg : ∀ i, HasComponentTops S W (z i) := fun i => I.reg hnonneg (src i) (z i) (hz i) M W
    choose Ac K hdec T hacg hmod hR using hreg
    obtain ⟨v, -, -, -, hs⟩ := VacuumTopZero.vacuum_splitting_of_tops S.U W c hc
      (fun i => S.ιE (z i)) (fun i => S.ιE_grade (z i)) hω Ac (fun i => (hR i).some) hneg hG.1 π
      hsurj hπ
    exact hs
  -- the simple modules
  have hlab : ∀ s, 0 ≤ SD.hw s ∧ (SD.hw s = 0 → s = SD.vac) := by
    intro s
    obtain ⟨M, _, _, W, hL, hmap⟩ := I.labels hinit s
    obtain ⟨⟨r, hr0, hr⟩, h0⟩ := hLW M W _ hL
    refine ⟨?_, fun hw => hmap (h0 (by rw [hw]; simp))⟩
    have hre : ((SD.hw s : ℝ) : ℂ) = (r : ℂ) := by rw [Complex.ofReal_ratCast]; exact hr
    have := Complex.ofReal_injective hre
    have h' : (0 : ℝ) ≤ (SD.hw s : ℝ) := by rw [this]; exact hr0
    exact_mod_cast h'
  exact ⟨hLW, hproj, hlab⟩

/-- **The label-specific consequence for the characters** (strict positivity of nonvacuum lowest
weights, line 4172): once the simples are identified with the twelve labels (`e`, compatible with
lowest weights and the vacuum), the nonvacuum labels `b, a, c₀` of trivial twist have no
weight-zero vectors (`a l 0 = 0`), given the definitional `low` (`a l n = 0` below the lowest
weight, `CharacterInputs.below`). -/
theorem noWeightZero_of_vacuum {Simp : Type*} (SD : SimpleData Simp) (C : CharacterData)
    (e : Simp ≃ Label) (hhw : ∀ s, C.hw (e s) = SD.hw s) (hvac : e SD.vac = .o)
    (low : ∀ l, ∀ n : ℕ, (n : ℚ) + twistExp l < C.hw l → C.a l n = 0)
    (hV : ∀ s, 0 ≤ SD.hw s ∧ (SD.hw s = 0 → s = SD.vac)) :
    ∀ l, (l = .b ∨ l = .a ∨ l = .c0) → C.a l 0 = 0 := by
  intro l hl
  have hl' : C.hw l = SD.hw (e.symm l) := by rw [← hhw, e.apply_symm_apply]
  have hpos : 0 < C.hw l := by
    rw [hl']
    refine lt_of_le_of_ne (hV _).1 fun h => ?_
    have h1 := (hV _).2 h.symm
    have h2 : l = .o := by rw [← hvac, ← h1, e.apply_symm_apply]
    rcases hl with rfl | rfl | rfl <;> cases h2
  refine low l 0 ?_
  rcases hl with rfl | rfl | rfl <;> simpa [twistExp] using hpos

#print axioms projectiveVacuum_arrow
#print axioms noWeightZero_of_vacuum

end HaagerupIzumi.C8.ProofMap
