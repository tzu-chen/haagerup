module

public import HaagerupIzumi.C8.VacuumLike
public import HaagerupIzumi.C8.VertexAlgebra.Borcherds
public import HaagerupIzumi.C8.VertexAlgebra.NormalWords
public import HaagerupIzumi.C8.Regularity.CompatibleTop
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

/-!
# Two steps of Lemma `lem:vacuum-projective` (lines 2931–2978)

Lemma `lem:vacuum-projective` of `c8_expanded_20260929/haagerup_c8_expanded.tex` uses two facts
that were recorded as inputs in `Regularity/CompatibleTop.lean` and `VacuumLike.lean`.  This file
proves both.

* **The module commutator relation** (lines 2941–2943): for homogeneous `a ∈ V_d`,
  `[L(0), a_(n)] = (d - n - 1) a_(n)` on every weak module, where `L(0) = ω_(1)` acts through
  the module.  It is derived from the axioms of `VacuumLike.WeakModule` (vacuum axiom, lower
  truncation, module iterate formula) and the two properties of `ω` recorded in
  `VertexOperatorAlgebra` (`ω_(1) = L(0)` is the grading, `ω_(0) = T`):
  - `act_T`: the `L(-1)`-derivative property `(T a)_(n) = -n a_(n-1)` on the module (iterate
    formula for `a_(-2) 𝟏`);
  - `L0_commutator`: the relation itself (iterate formula for `ω_(1) a` and `ω_(0) a`);
  - `L0_commutator_step`: the hypothesis `hcomm` of `CompatibleTop.commutator_step` in the form
    used there, so that `commutator_step` now applies to every weak module of a VOA;
  - `act_mem_maxGenEigenspace`: the same for generalized weight spaces, `a_(n) N_[μ] ⊆
    N_[μ + d - n - 1]` (lines 2962–2964: `N_[0]` has no lower-weight target and is stable under
    degree-zero modes);
  - `act_zero_omega_comm`, `omegaModule`: `[ω_(0), a_(n)] = -n a_(n-1)` on the module, so the
    weak module with `L_N(-1) := ω_(0)` satisfies translation covariance.
* **The choice of `v ∈ N_[0]` with `π v = 𝟏`** (lines 2971–2973: "generalized weight
  decompositions are preserved by `π`").  `exists_maxGenEigenspace_preimage`: if `π : N → V` is
  surjective and intertwines `L_N(0)` with `L_V(0)`, and `N` is spanned by the generalized
  eigenspaces of `L_N(0)` (a grading-restricted generalized module), then every vector of a
  generalized eigenspace of `L_V(0)` has a preimage in the generalized eigenspace of `L_N(0)` for
  the same eigenvalue.  `exists_vacuum_preimage` applies it to `𝟏` (`L_V(0) 𝟏 = 0`), giving
  `v ∈ N_[0]` with `π v = 𝟏`.  `omega_vacuumLike_section` then gives the splitting
  `a ↦ a_(-1) v`, given `ω_(0) v = 0` (the vacuum-top step, `L_V(-1) N_[0] = 0`).

No hypothesis of this file is external: both facts are consequences of the stated axioms.
What remains of `lem:vacuum-projective` is listed in `ROADMAP.md` (finite length from
`C₂`-cofiniteness; absence of negative weights in the composition factors).
-/

namespace HaagerupIzumi.C8.VacuumProjective

open HaagerupIzumi.C8 VacuumLike

/-! ### The binomial coefficient `(-2 choose t)` -/

theorem choose_neg_two_int (t : ℕ) : Ring.choose (-2 : ℤ) t = (-1) ^ t * ((t : ℤ) + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := Ring.choose_succ_succ (-2 : ℤ) t
    have h1 : (-2 : ℤ) + 1 = -1 := by norm_num
    rw [h1, choose_neg_one_int, ih] at h
    push_cast
    linear_combination (-1 : ℤ) * h

theorem zbinom_neg_two (k : Type*) [Field k] (t : ℕ) :
    zbinom k (-2) t = (-1) ^ t * ((t : k) + 1) := by
  unfold zbinom
  rw [choose_neg_two_int]
  push_cast
  ring

/-! ### The module commutator relation -/

section Commutator

variable {k : Type*} [Field k] [CharZero k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- **`L(-1)`-derivative property on a weak module**: `(T a)_(n) = -n a_(n-1)`.  From the module
iterate formula for `T a = a_(-2) 𝟏` and the vacuum axiom. -/
theorem act_T {A : VertexAlgebra k V} (W : WeakModule A M) (a : V) (n : ℤ) (w : M) :
    W.act n (A.T a) w = -((n : k) • W.act (n - 1) a w) := by
  obtain ⟨Na, hNa⟩ := W.trunc a w
  have hb : ∀ t : ℕ, Na + n.natAbs + 1 ≤ t → W.act (n + t) A.vac w = 0 := by
    intro t ht
    rw [W.vac_act, if_neg (by omega)]
  have ha : ∀ t : ℕ, Na + n.natAbs + 1 ≤ t → W.act t a w = 0 :=
    fun t ht => hNa t (by omega)
  rw [A.T_eq a, W.iterate a A.vac w (-2) n _ hb ha]
  have hz : (-1 : k) ^ (-2 : ℤ) = 1 := by norm_num
  simp only [hz, one_smul, W.vac_act, zbinom_neg_two]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- `n < 0`: only `t₀ = -1 - n` contributes, through the first term.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℕ, (t₀ : ℤ) = -1 - n := ⟨(-1 - n).toNat, by omega⟩
    rw [Finset.sum_eq_single_of_mem t₀ (Finset.mem_range.2 (by omega))]
    · rw [if_pos (by omega), if_neg (by omega), sub_zero]
      have e : -2 - (t₀ : ℤ) = n - 1 := by omega
      rw [e]
      have e2 : ((-1 : k) ^ t₀ * ((-1) ^ t₀ * ((t₀ : k) + 1))) = -(n : k) := by
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
        norm_num
        have : ((t₀ : ℤ) : k) = ((-1 - n : ℤ) : k) := by rw [ht₀]
        push_cast at this
        rw [this]
        ring
      rw [e2, neg_smul]
    · intro t _ ht
      rw [if_neg (by omega), if_neg (by omega), map_zero, sub_zero, smul_zero]
  · -- `n = 0`: no term contributes.
    subst hn
    rw [Finset.sum_eq_zero]
    · simp
    · intro t _
      rw [if_neg (by omega), if_neg (by omega), map_zero, sub_zero, smul_zero]
  · -- `n > 0`: only `t₀ = n - 1` contributes, through the second term.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℕ, (t₀ : ℤ) = n - 1 := ⟨(n - 1).toNat, by omega⟩
    rw [Finset.sum_eq_single_of_mem t₀ (Finset.mem_range.2 (by omega))]
    · rw [if_neg (by omega), if_pos (by omega), map_zero, zero_sub, smul_neg]
      have e2 : ((-1 : k) ^ t₀ * ((-1) ^ t₀ * ((t₀ : k) + 1))) = (n : k) := by
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
        norm_num
        have : ((t₀ : ℤ) : k) = ((n - 1 : ℤ) : k) := by rw [ht₀]
        push_cast at this
        rw [this]
        ring
      rw [e2, ht₀]
    · intro t _ ht
      rw [if_neg (by omega), if_neg (by omega), map_zero, sub_zero, smul_zero]

/-- **The module commutator relation** (lines 2941–2943): on a weak module of a VOA, for
`a ∈ V_d`, `[L(0), a_(n)] = (d - n - 1) a_(n)` with `L(0) = ω_(1)`.  From the module iterate
formula for `ω_(1) a = d·a` and `ω_(0) a = T a`, and `act_T`. -/
theorem L0_commutator (A : VertexOperatorAlgebra k V) (W : WeakModule A.toVertexAlgebra M)
    {d : ℕ} {a : V} (ha : a ∈ A.grade d) (n : ℤ) (w : M) :
    W.act 1 A.ω (W.act n a w) - W.act n a (W.act 1 A.ω w) =
      ((d : k) - n - 1) • W.act n a w := by
  obtain ⟨Na, hNa⟩ := W.trunc a w
  obtain ⟨Nω, hNω⟩ := W.trunc A.ω w
  set N : ℕ := Na + Nω + n.natAbs + 2 with hN
  have ha1 : ∀ t : ℕ, N ≤ t → W.act (n + t) a w = 0 := fun t ht => hNa _ (by omega)
  have ha2 : ∀ t : ℕ, N ≤ t → W.act (n + 1 + t) a w = 0 := fun t ht => hNa _ (by omega)
  have hω : ∀ t : ℕ, N ≤ t → W.act t A.ω w = 0 := fun t ht => hNω _ (by omega)
  -- `ω_(1) a = d a`
  have h1 := W.iterate A.ω a w 1 n N ha1 hω
  rw [A.L0 ha, map_smul, LinearMap.smul_apply] at h1
  have hz1 : ∀ t : ℕ, 2 ≤ t → zbinom k 1 t = 0 := fun t ht => by
    have h := zbinom_natCast_of_lt k (n := 1) (t := t) (by omega)
    rwa [Nat.cast_one] at h
  rw [sum_range_eq_two_terms (by omega) (fun t ht => by
    rw [hz1 t ht, mul_zero, zero_smul])] at h1
  -- `ω_(0) a = T a`
  have h0 := W.iterate A.ω a w 0 (n + 1) N ha2 hω
  rw [A.Lm1, act_T W a (n + 1) w] at h0
  rw [sum_range_eq_zero_term (by omega) (fun t ht => by
    rw [zbinom_zero_left_of_pos k (t := t) (by omega), mul_zero, zero_smul])] at h0
  simp only [pow_zero, pow_one, zbinom_zero_right, zbinom_one_right, zpow_one, zpow_zero,
    one_mul, neg_one_mul, one_smul, neg_smul, Nat.cast_zero, Nat.cast_one, sub_zero,
    add_zero, Int.cast_one] at h0 h1
  have e1 : (1 : ℤ) + n - 1 = n := by ring
  have e2 : (1 : ℤ) + n = n + 1 := by ring
  have e4 : (n + 1 : ℤ) - 1 = n := by ring
  have e5 : (1 : ℤ) - 1 = 0 := by ring
  simp only [e1, e4, e5, zero_add] at h0 h1
  rw [e2] at h1
  push_cast at h0 h1 ⊢
  linear_combination (norm := module) -h1 - h0

/-- The hypothesis `hcomm` of `CompatibleTop.commutator_step` for `L0 = ω_(1)` and `A = a_(n)`
on a weak module, with degree `d - n - 1`. -/
theorem L0_commutator_step (A : VertexOperatorAlgebra k V) (W : WeakModule A.toVertexAlgebra M)
    {d : ℕ} {a : V} (ha : a ∈ A.grade d) (n : ℤ) (w : M) :
    W.act 1 A.ω (W.act n a w) =
      W.act n a (W.act 1 A.ω w) + ((d : k) - n - 1) • W.act n a w := by
  rw [← L0_commutator A W ha n w]
  abel

/-- **The commutator step of `lem:vacuum-projective` on a weak module** (lines 2941–2943):
if `L(0) v = h v` then `L(0) (a_(n) v) = (h + d - n - 1) a_(n) v`, and `a_(n) v = 0` when
`L(0)` has no eigenvector of eigenvalue `h + d - n - 1` (e.g. `v` in the lowest space and
`d - n - 1 < 0`).  `CompatibleTop.commutator_step` with its hypothesis now proved. -/
theorem module_commutator_step (A : VertexOperatorAlgebra k V)
    (W : WeakModule A.toVertexAlgebra M) {d : ℕ} {a : V} (ha : a ∈ A.grade d) (n : ℤ)
    {h : k} {v : M} (hv : W.act 1 A.ω v = h • v) :
    W.act 1 A.ω (W.act n a v) = (h + ((d : k) - n - 1)) • W.act n a v ∧
      ((∀ w, W.act 1 A.ω w = (h + ((d : k) - n - 1)) • w → w = 0) → W.act n a v = 0) :=
  CompatibleTop.commutator_step (W.act 1 A.ω) (W.act n a) ((d : k) - n - 1) h
    (L0_commutator_step A W ha n) hv

/-- **`L(-1) = ω_(0)` on a weak module**: `[ω_(0), a_(n)] = (T a)_(n) = -n a_(n-1)`, from the
module iterate formula for `ω_(0) a = T a` and `act_T`. -/
theorem act_zero_omega_comm (A : VertexOperatorAlgebra k V) (W : WeakModule A.toVertexAlgebra M)
    (a : V) (n : ℤ) (w : M) :
    W.act 0 A.ω (W.act n a w) - W.act n a (W.act 0 A.ω w) = -((n : k) • W.act (n - 1) a w) := by
  obtain ⟨Na, hNa⟩ := W.trunc a w
  obtain ⟨Nω, hNω⟩ := W.trunc A.ω w
  have ha : ∀ t : ℕ, Na + Nω + n.natAbs + 1 ≤ t → W.act (n + t) a w = 0 :=
    fun t ht => hNa _ (by omega)
  have hω : ∀ t : ℕ, Na + Nω + n.natAbs + 1 ≤ t → W.act t A.ω w = 0 :=
    fun t ht => hNω _ (by omega)
  have h0 := W.iterate A.ω a w 0 n _ ha hω
  rw [A.Lm1, act_T W a n w] at h0
  rw [sum_range_eq_zero_term (by omega) (fun t ht => by
    rw [zbinom_zero_left_of_pos k (t := t) (by omega), mul_zero, zero_smul])] at h0
  simp only [pow_zero, zbinom_zero_right, zpow_zero, one_mul, one_smul, Nat.cast_zero,
    sub_zero, add_zero, zero_add] at h0
  exact h0.symm

/-- The weak module `W` with its translation operator replaced by `L_N(-1) = ω_(0)`
(`act_zero_omega_comm` is its translation covariance).  Lemma `lem:vacuum-projective` speaks of
`L_V(-1) N_[0] = 0` for this operator. -/
def omegaModule (A : VertexOperatorAlgebra k V) (W : WeakModule A.toVertexAlgebra M) :
    WeakModule A.toVertexAlgebra M :=
  { W with
    TM := W.act 0 A.ω
    TM_act := fun n a w => act_zero_omega_comm A W a n w }

/-- **The splitting of `lem:vacuum-projective`** (lines 2971–2978), with `L_N(-1) = ω_(0)`: if
`ω_(0) v = 0` and `π v = 𝟏` for a module map `π : N → V`, then `a ↦ a_(-1) v` is a module map
`V → N` with `π ∘ s = id`.  (`VacuumLike.vacuumLike_section` for `omegaModule`.)  The input
`ω_(0) v = 0` is the vacuum-top step (`CompatibleTop.vacuum_top_step` and
eq:finite-positive-stress). -/
theorem omega_vacuumLike_section (A : VertexOperatorAlgebra k V)
    (W : WeakModule A.toVertexAlgebra M) {v : M} (hv : W.act 0 A.ω v = 0) (π : M →ₗ[k] V)
    (hπ : ∀ (n : ℤ) (a : V) (w : M), π (W.act n a w) = A.mode n a (π w))
    (hπv : π v = A.vac) :
    ∃ s : V →ₗ[k] M, (∀ (m : ℤ) (b a : V), s (A.mode m b a) = W.act m b (s a)) ∧
      ∀ a, π (s a) = a :=
  VacuumLike.vacuumLike_section (omegaModule A W) hv π hπ hπv

end Commutator

/-! ### Generalized eigenspaces and epimorphisms -/

section Eigen

variable {K : Type*} [Field K]
variable {N : Type*} [AddCommGroup N] [Module K N]
variable {P : Type*} [AddCommGroup P] [Module K P]

open Module End

theorem map_pow_sub_smul (π : N →ₗ[K] P) (LN : End K N) (LP : End K P)
    (hπ : ∀ w, π (LN w) = LP (π w)) (μ : K) (j : ℕ) (w : N) :
    π (((LN - μ • 1) ^ j) w) = ((LP - μ • 1) ^ j) (π w) := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp [hπ]

theorem map_mem_maxGenEigenspace (π : N →ₗ[K] P) (LN : End K N) (LP : End K P)
    (hπ : ∀ w, π (LN w) = LP (π w)) {μ : K} {w : N} (hw : w ∈ LN.maxGenEigenspace μ) :
    π w ∈ LP.maxGenEigenspace μ := by
  rw [mem_maxGenEigenspace] at hw ⊢
  obtain ⟨j, hj⟩ := hw
  exact ⟨j, by rw [← map_pow_sub_smul π LN LP hπ, hj, map_zero]⟩

/-- **Generalized weight spaces are preserved by epimorphisms** (lines 2971–2973).  Let
`π : N → P` be surjective with `π ∘ L_N = L_P ∘ π`, and let `N` be spanned by the generalized
eigenspaces of `L_N`.  Then every `x` in the generalized `μ`-eigenspace of `L_P` is `π v` for some
`v` in the generalized `μ`-eigenspace of `L_N`. -/
theorem exists_maxGenEigenspace_preimage (π : N →ₗ[K] P) (hsurj : Function.Surjective π)
    (LN : End K N) (LP : End K P) (hπ : ∀ w, π (LN w) = LP (π w))
    (hspan : ⨆ ν, LN.maxGenEigenspace ν = ⊤) {μ : K} {x : P} (hx : x ∈ LP.maxGenEigenspace μ) :
    ∃ v ∈ LN.maxGenEigenspace μ, π v = x := by
  obtain ⟨w, rfl⟩ := hsurj x
  have hw : w ∈ ⨆ ν, LN.maxGenEigenspace ν := by rw [hspan]; trivial
  -- every `w` splits as `v + (rest)` with `π (rest)` in the other generalized eigenspaces
  have key : ∃ v ∈ LN.maxGenEigenspace μ,
      π w - π v ∈ ⨆ ν, ⨆ (_ : ν ≠ μ), LP.maxGenEigenspace ν := by
    refine Submodule.iSup_induction (fun ν => LN.maxGenEigenspace ν)
      (motive := fun w => ∃ v ∈ LN.maxGenEigenspace μ,
        π w - π v ∈ ⨆ ν, ⨆ (_ : ν ≠ μ), LP.maxGenEigenspace ν) hw ?_ ?_ ?_
    · intro ν y hy
      by_cases hν : ν = μ
      · subst hν
        exact ⟨y, hy, by rw [sub_self]; exact Submodule.zero_mem _⟩
      · refine ⟨0, Submodule.zero_mem _, ?_⟩
        rw [map_zero, sub_zero]
        exact (le_iSup₂ (f := fun ν (_ : ν ≠ μ) => LP.maxGenEigenspace ν) ν hν)
          (map_mem_maxGenEigenspace π LN LP hπ hy)
    · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, sub_zero]; exact Submodule.zero_mem _⟩
    · rintro y z ⟨v₁, hv₁, h₁⟩ ⟨v₂, hv₂, h₂⟩
      refine ⟨v₁ + v₂, Submodule.add_mem _ hv₁ hv₂, ?_⟩
      have : π (y + z) - π (v₁ + v₂) = (π y - π v₁) + (π z - π v₂) := by
        rw [map_add, map_add]; abel
      rw [this]
      exact Submodule.add_mem _ h₁ h₂
  obtain ⟨v, hv, hrest⟩ := key
  refine ⟨v, hv, ?_⟩
  have hin : π w - π v ∈ LP.maxGenEigenspace μ :=
    Submodule.sub_mem _ hx (map_mem_maxGenEigenspace π LN LP hπ hv)
  have hdisj := (independent_maxGenEigenspace LP) μ
  have h0 : π w - π v = 0 := by
    have := Submodule.disjoint_def.1 hdisj _ hin hrest
    exact this
  exact (sub_eq_zero.1 h0).symm

/-- **The choice of `v ∈ N_[0]` with `π v = 𝟏`** (lines 2971–2973).  If `π : N ↠ V` intertwines
`L_N(0)` and `L_V(0)`, `N` is spanned by generalized `L_N(0)`-eigenspaces, and `L_V(0) 𝟏 = 0`,
there is `v` in the generalized weight-zero space `N_[0]` with `π v = 𝟏`. -/
theorem exists_vacuum_preimage (π : N →ₗ[K] P) (hsurj : Function.Surjective π)
    (LN : End K N) (LP : End K P) (hπ : ∀ w, π (LN w) = LP (π w))
    (hspan : ⨆ ν, LN.maxGenEigenspace ν = ⊤) {one : P} (hone : LP one = 0) :
    ∃ v ∈ LN.maxGenEigenspace 0, π v = one := by
  refine exists_maxGenEigenspace_preimage π hsurj LN LP hπ hspan ?_
  rw [mem_maxGenEigenspace]
  exact ⟨1, by simp [hone]⟩

end Eigen

/-! ### Modes on generalized weight spaces -/

section ModesOnWeightSpaces

variable {k : Type*} [Field k] [CharZero k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {M : Type*} [AddCommGroup M] [Module k M]

open Module End

/-- **Modes shift generalized weights** (lines 2941–2943 and 2962–2964): for `a ∈ V_d`, the mode
`a_(n)` maps the generalized `L(0)`-eigenspace `N_[μ]` of a weak module into
`N_[μ + d - n - 1]`.  In particular lowering modes have no target below the lowest generalized
weight, and degree-zero modes preserve `N_[0]`. -/
theorem act_mem_maxGenEigenspace (A : VertexOperatorAlgebra k V)
    (W : WeakModule A.toVertexAlgebra M) {d : ℕ} {a : V} (ha : a ∈ A.grade d) (n : ℤ) {μ : k}
    {w : M} (hw : w ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) μ) :
    W.act n a w ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) (μ + ((d : k) - n - 1)) := by
  have hπ : ∀ x, W.act n a (W.act 1 A.ω x) =
      (W.act 1 A.ω - ((d : k) - n - 1) • (1 : End k M)) (W.act n a x) := by
    intro x
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      L0_commutator_step A W ha n x]
    abel
  have h := map_mem_maxGenEigenspace (W.act n a) (W.act 1 A.ω)
    (W.act 1 A.ω - ((d : k) - n - 1) • (1 : End k M)) hπ hw
  rw [mem_maxGenEigenspace] at h ⊢
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  have e : W.act 1 A.ω - (μ + ((d : k) - n - 1)) • (1 : End k M) =
      (W.act 1 A.ω - ((d : k) - n - 1) • (1 : End k M)) - μ • (1 : End k M) := by
    rw [add_smul]
    abel
  rw [e]
  exact hj

end ModesOnWeightSpaces

#print axioms act_T
#print axioms L0_commutator
#print axioms module_commutator_step
#print axioms act_zero_omega_comm
#print axioms omega_vacuumLike_section
#print axioms act_mem_maxGenEigenspace
#print axioms exists_maxGenEigenspace_preimage
#print axioms exists_vacuum_preimage

end HaagerupIzumi.C8.VacuumProjective
