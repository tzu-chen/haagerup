module

public import HaagerupIzumi.C8.Regularity.VacuumProjective

@[expose] public section

/-!
# No negative weights through a composition series (Lemma `lem:vacuum-projective`)

Lines 2959–2964 of `c8_expanded_20260929/haagerup_c8_expanded.tex`: *`C₂`-cofiniteness gives
finite length, and the preceding argument excludes negative weights in all its composition
factors.  The finite generalized weight-zero space `N_[0]` therefore has no lower-weight target
for a lowering mode.*

This file proves the linear algebra behind "therefore":

* `maxGenEigenspace_eq_bot_of_filtration`: if `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = N` is a chain of
  `L`-stable subspaces and `L - μ` is injective on every quotient `F_{i+1}/F_i` (stated without
  quotients: `x ∈ F_{i+1}`, `(L - μ) x ∈ F_i ⇒ x ∈ F_i`; for an `L`-stable chain this is exactly
  injectivity on the quotients, and the Lean statement assumes neither monotonicity nor
  `L`-stability), then `N_[μ] = 0`;
* `lowering_mode_eq_zero`: if `N_[-m] = 0` for every integer `m ≥ 1` (no negative integral
  generalized weights), then for `a ∈ V_d` and `d - n - 1 < 0` the mode `a_(n)` kills `N_[0]`
  (with `VacuumProjective.act_mem_maxGenEigenspace`).

Inputs that stay external: finite length of grading-restricted generalized modules of a
`C₂`-cofinite VOA (Huang; Miyamoto); that the composition factors (simple grading-restricted
generalized modules) are ordinary, i.e. `L(0)` acts semisimply on them (standard: the nilpotent
part of `L(0)` commutes with all modes, so its kernel is a nonzero submodule); and that a simple
ordinary module of lowest weight `h ≥ 0` has `L(0) - μ` injective for `μ < 0` (its `L(0)`
eigenvalues lie in `h + ℕ`; nonnegativity of `h` is eq:top-trace).
-/

namespace HaagerupIzumi.C8.VacuumProjective

open Module End

section Filtration

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N]

/-- `L - μ` is injective on `F r` when it is injective on each step of the chain. -/
theorem sub_smul_injective_of_filtration (L : End K N) (μ : K) (F : ℕ → Submodule K N)
    (hF0 : F 0 = ⊥) (hstep : ∀ i, ∀ x ∈ F (i + 1), L x - μ • x ∈ F i → x ∈ F i) :
    ∀ r, ∀ x ∈ F r, L x - μ • x = 0 → x = 0 := by
  intro r
  induction r with
  | zero =>
    intro x hx _
    rw [hF0] at hx
    exact (Submodule.mem_bot K).1 hx
  | succ r ih =>
    intro x hx h0
    have hxr : x ∈ F r := hstep r x hx (by rw [h0]; exact Submodule.zero_mem _)
    exact ih x hxr h0

/-- **No generalized weight `μ` through a filtration**: if `F₀ = 0`, `F_r = N`, and `L - μ` is
injective on every step of the chain, then the generalized eigenspace `N_[μ]` is zero. -/
theorem maxGenEigenspace_eq_bot_of_filtration (L : End K N) (μ : K) (F : ℕ → Submodule K N)
    (r : ℕ) (hF0 : F 0 = ⊥) (hFr : F r = ⊤)
    (hstep : ∀ i, ∀ x ∈ F (i + 1), L x - μ • x ∈ F i → x ∈ F i) :
    L.maxGenEigenspace μ = ⊥ := by
  have hinj : ∀ x, (L - μ • 1) x = 0 → x = 0 := by
    intro x hx
    refine sub_smul_injective_of_filtration L μ F hF0 hstep r x (by rw [hFr]; trivial) ?_
    simpa using hx
  have hpow : ∀ j : ℕ, ∀ x, ((L - μ • 1) ^ j) x = 0 → x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply] at hx
      exact hinj x (ih _ hx)
  rw [eq_bot_iff]
  intro x hx
  rw [mem_maxGenEigenspace] at hx
  obtain ⟨j, hj⟩ := hx
  rw [Submodule.mem_bot]
  exact hpow j x hj

end Filtration

section Lowering

open VacuumLike

variable {k : Type*} [Field k] [CharZero k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- **Lowering modes kill `N_[0]`** (lines 2962–2964): if the module has no generalized
`L(0)`-weight `-m` for any integer `m ≥ 1`, then for `a ∈ V_d` and `n` with `d - n - 1 < 0`,
`a_(n)` vanishes on the generalized weight-zero space. -/
theorem lowering_mode_eq_zero (A : VertexOperatorAlgebra k V)
    (W : WeakModule A.toVertexAlgebra M)
    (hneg : ∀ m : ℕ, 1 ≤ m → Module.End.maxGenEigenspace (W.act 1 A.ω) (-(m : k)) = ⊥)
    {d : ℕ} {a : V} (ha : a ∈ A.grade d) (n : ℤ) (hn : (d : ℤ) - n - 1 < 0) {w : M}
    (hw : w ∈ Module.End.maxGenEigenspace (W.act 1 A.ω) 0) : W.act n a w = 0 := by
  have h := act_mem_maxGenEigenspace A W ha n hw
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -((d : ℤ) - n - 1) := ⟨(-((d : ℤ) - n - 1)).toNat, by omega⟩
  have hshift : (0 : k) + ((d : k) - n - 1) = -(m : k) := by
    have : ((m : ℤ) : k) = ((-((d : ℤ) - n - 1) : ℤ) : k) := by rw [hm]
    push_cast at this
    rw [this]
    ring
  rw [hshift, hneg m (by omega)] at h
  exact (Submodule.mem_bot k).1 h

end Lowering

#print axioms maxGenEigenspace_eq_bot_of_filtration
#print axioms lowering_mode_eq_zero

end HaagerupIzumi.C8.VacuumProjective
