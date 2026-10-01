module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Order.Filter.AtTopBot.Floor
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! # Regularity from a positive conformal-vector identity: the finite-dimensional steps

This file formalizes the linear-algebra and elementary analytic arguments of Section
`sec:regularity` of `c8_expanded_20260929/haagerup_c8_expanded.tex` (lines 2629–3035).
Throughout, `ω_U = ∑ cᵢ eᵢ` with `cᵢ > 0` is the finite positive identity
`eq:finite-positive-stress` (line 2717), `Lᵢ = L^{eᵢ}(0)` are the partial energies and
`∑ cᵢ Lᵢ = L_V(0)`.

## Lemma `lem:positive-c2` (Orthogonal energy bound, lines 2846–2888)
Fix a grade `E = V_n` (finite-dimensional, with the positive invariant form) and
`C = V_n ∩ C₂(V)`.
* `re_inner_le_of_eigenvectors_mem`: if a symmetric `T` has every eigenvector of
  eigenvalue `> D` inside `C`, then `re ⟪T v, v⟫ ≤ D ‖v‖²` for `v ⊥ C`.  The spectral
  theorem is applied to each `Lᵢ` separately (no simultaneous diagonalization).
* `orthogonal_eq_bot_of_positive_identity`, `eq_top_of_positive_identity`: if
  `∑ cᵢ Lᵢ = n • id` on `V_n` with `cᵢ ≥ 0` and `n > ∑ cᵢ Dᵢ`, then `Cᗮ = ⊥`, i.e.
  `V_n ⊆ C₂(V)`, i.e. `(V/C₂(V))_n = 0`.
* `finiteDimensional_quotient_of_graded`: finite-dimensional grades, all grades above `N`
  inside `C`, imply `V ⧸ C` finite-dimensional.
* `finiteDimensional_quotient_of_positive_identity`: the assembled lemma — symmetric
  grade-preserving `Lᵢ` with `∑ cᵢ Lᵢ = n` on `V_n`, `cᵢ ≥ 0`, and the eigenvector
  hypothesis give `dim V / C₂(V) < ∞`.

External inputs (hypotheses): symmetry of `Lᵢ` on `V_n` (unitarity: `Lᵢ` is self-adjoint
for the positive form); "every eigenvector of energy `> Dᵢ` lies in `C`", which the
manuscript obtains from Abe–Buhl–Dong [ABD, Prop. 5.2] (finite-dimensional `C₂`-quotients
of the simple `Aᵢ`-modules), finiteness of the simple `Aᵢ`-modules and complete
reducibility of `V` as a weak `Aᵢ`-module (regularity of `Aᵢ`), and
`C_{2,Aᵢ}(V) ⊆ C₂(V)`; the identity `∑ cᵢ Lᵢ = n • id` on `V_n` (certificate input
`eq:positive-stress` plus Carathéodory, see `HaagerupIzumi.C8.PositiveStress`).

## Lemma `lem:vacuum-projective` (trace step `eq:top-trace`, lines 2931–2979)
For a finite-dimensional `E` (the lowest space `M_h`, or `N_{[0]}`):
* `top_trace_identity`: `∑ cᵢ Lᵢ = h • id` gives `h · dim E = ∑ cᵢ Tr Lᵢ`;
* `top_trace_nonneg`, `exists_real_nonneg_of_top_trace`: this is a nonnegative real, so
  `h ≥ 0` is real when `E ≠ 0`;
* `eq_zero_of_top_trace_eq_zero`: `h = 0` forces every `Lᵢ = 0` on `E`;
* `eq_zero_of_isNilpotent_sum`: `∑ cᵢ Lᵢ` nilpotent on `E` forces every `Lᵢ = 0`.
Input (hypothesis `IsNonnegDiagonalizable`): each `Lᵢ|_E` is diagonalizable with
nonnegative real eigenvalues — this is the manuscript's own Lemma `lem:compatible-top`,
whose algebraic core is in `Regularity/CompatibleTop`: `isNonnegDiagonalizable_of_compatible`
gives exactly this hypothesis for an operator on `E` that corresponds to `L^{Aᵢ}(0)` on a
Zhu-submodule of `Ω_{Aᵢ}(M) ≅ ⨁ tops`.  The decomposition (regularity of `Aᵢ`) and the
nonnegativity of the lowest weights of the simple `Aᵢ`-modules are external; the commutator step
placing `E` in `Ω_{Aᵢ}(M)` (lines 2941–2943) is `CompatibleTop.commutator_step`, given the module
commutator relation `[L(0), a_(n)] = (wt a - n - 1) a_(n)` as a hypothesis.

## Lemma `lem:vacuum-like` (lines 2916–2929), first assertion
* `modes_nonneg_eq_zero_of_translation`: translation covariance
  `[L(-1), a_{n+1}] = -(n+1) a_n`, lower truncation, and `L(-1) v = 0` give `a_n v = 0`
  for all `n ≥ 0` (downward induction).  The module-homomorphism assertion is
  `VacuumLike.vacuumLike_module_map` (from the `WeakModule.iterate` field).
* `sum_smul_apply_eq_zero`: `L^{eᵢ}(-1) E = 0` for all `i` gives `L_V(-1) E = 0`.

## Lemma `lem:projective-unit` (growth estimate, lines 2994–3000)
* `eventually_sq_mul_pow_lt_factorial`: `d² C^{2n} < n!` for large `n`;
* `eventually_lt_factorial_of_step`: `a (n+1) ≤ C a n` (right exactness:
  `d₀(Z ⊗ X) ≤ C_X d₀(Z)`) and `e n ≤ (a n)²` (`End(Y)` inside the endomorphisms of the
  underlying space) give `e n < n!` eventually — the moderate-growth hypothesis of
  Etingof–Penneys [EP, Thm. 1.1], whose rigidity conclusion is external, as are McRae's
  Grothendieck–Verdier structure and the final semisimplicity deduction.
-/

namespace HaagerupIzumi.C8

open scoped InnerProductSpace ComplexConjugate

section OrthogonalEnergy

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Spectral expansion of the quadratic form of a symmetric operator in an orthonormal
eigenbasis: `⟪T v, v⟫ = ∑ᵢ μᵢ |⟪bᵢ, v⟫|²`. -/
theorem inner_apply_self_eq_sum_of_eigenbasis {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i) (v : E) :
    ⟪T v, v⟫_𝕜 = ((∑ i, μ i * ‖⟪b i, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← b.sum_inner_mul_inner (T v) v, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.ofReal_mul, RCLike.ofReal_pow, hT v (b i), hb i, inner_smul_right,
    ← inner_conj_symm v (b i), mul_assoc, RCLike.conj_mul]

/-- The bound for one operator, given any orthonormal eigenbasis. -/
theorem re_inner_le_of_eigenbasis {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (C : Submodule 𝕜 E) (D : ℝ) (hC : ∀ i, D < μ i → b i ∈ C)
    {v : E} (hv : v ∈ Cᗮ) :
    RCLike.re ⟪T v, v⟫_𝕜 ≤ D * ‖v‖ ^ 2 := by
  rw [inner_apply_self_eq_sum_of_eigenbasis hT b μ hb v, RCLike.ofReal_re,
    ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : D < μ i
  · have h0 : ⟪b i, v⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal (hC i hi) hv
    simp [h0]
  · exact mul_le_mul_of_nonneg_right (not_lt.mp hi) (sq_nonneg _)

/-- **Orthogonal energy bound** (`lem:positive-c2`, line 2872).  Let `T` be symmetric on a
finite-dimensional inner product space and suppose every eigenvector of `T` with
eigenvalue `> D` lies in the subspace `C`.  Then `re ⟪T v, v⟫ ≤ D ‖v‖²` for every `v ⊥ C`.
The spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis`) is applied to `T` alone. -/
theorem re_inner_le_of_eigenvectors_mem [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (C : Submodule 𝕜 E) (D : ℝ)
    (hC : ∀ (μ : ℝ) (x : E), T x = (μ : 𝕜) • x → D < μ → x ∈ C)
    {v : E} (hv : v ∈ Cᗮ) :
    RCLike.re ⟪T v, v⟫_𝕜 ≤ D * ‖v‖ ^ 2 := by
  obtain ⟨b, μ, hb⟩ : ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
      (μ : Fin (Module.finrank 𝕜 E) → ℝ), ∀ i, T (b i) = (μ i : 𝕜) • b i :=
    ⟨hT.eigenvectorBasis rfl, hT.eigenvalues rfl, hT.apply_eigenvectorBasis rfl⟩
  exact re_inner_le_of_eigenbasis hT b μ hb C D (fun i hi => hC (μ i) (b i) (hb i) hi) hv

/-- The quadratic-form identity behind the energy count: if `∑ cᵢ Lᵢ = n • id` then
`n ‖v‖² = ∑ cᵢ re ⟪Lᵢ v, v⟫`. -/
theorem norm_sq_mul_eq_sum_of_identity {ι : Type*} (s : Finset ι) (L : ι → E →ₗ[𝕜] E)
    (c : ι → ℝ) (n : ℝ) (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = (n : 𝕜) • LinearMap.id) (v : E) :
    n * ‖v‖ ^ 2 = ∑ i ∈ s, c i * RCLike.re ⟪L i v, v⟫_𝕜 := by
  have h := congrArg (fun T : E →ₗ[𝕜] E => RCLike.re ⟪T v, v⟫_𝕜) hsum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply, sum_inner,
    inner_smul_left, RCLike.conj_ofReal, map_sum, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq] at h
  exact h.symm

/-- **Lemma `lem:positive-c2`, finite-dimensional core** (lines 2865–2884).
Let `E = V_n`, `C = V_n ∩ C₂(V)`, `Lᵢ = L^{eᵢ}(0)|_{V_n}` (symmetric), `cᵢ ≥ 0`, with
`∑ cᵢ Lᵢ = n • id` (the positive conformal-vector identity on the grade `n`).  If every
eigenvector of `Lᵢ` of eigenvalue `> Dᵢ` lies in `C`, and `n > ∑ cᵢ Dᵢ`, then `Cᗮ = ⊥`. -/
theorem orthogonal_eq_bot_of_positive_identity [FiniteDimensional 𝕜 E] {ι : Type*}
    (s : Finset ι) (L : ι → E →ₗ[𝕜] E) (hL : ∀ i ∈ s, (L i).IsSymmetric)
    (c D : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (C : Submodule 𝕜 E)
    (hC : ∀ i ∈ s, ∀ (μ : ℝ) (x : E), L i x = (μ : 𝕜) • x → D i < μ → x ∈ C)
    (n : ℝ) (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = (n : 𝕜) • LinearMap.id)
    (hn : ∑ i ∈ s, c i * D i < n) :
    Cᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
  have key := norm_sq_mul_eq_sum_of_identity s L c n hsum v
  have hle : ∑ i ∈ s, c i * RCLike.re ⟪L i v, v⟫_𝕜 ≤ ∑ i ∈ s, c i * (D i * ‖v‖ ^ 2) :=
    Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left
        (re_inner_le_of_eigenvectors_mem (hL i hi) C (D i) (hC i hi) hv) (hc i hi)
  have hsplit : ∑ i ∈ s, c i * (D i * ‖v‖ ^ 2) = (∑ i ∈ s, c i * D i) * ‖v‖ ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  have h3 : ‖v‖ ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
  simpa using h3

/-- Same conclusion, phrased as `C = ⊤`: the whole grade `V_n` lies in `C₂(V)`, i.e.
`(V / C₂(V))_n = 0` for `n > ∑ cᵢ Dᵢ`. -/
theorem eq_top_of_positive_identity [FiniteDimensional 𝕜 E] {ι : Type*}
    (s : Finset ι) (L : ι → E →ₗ[𝕜] E) (hL : ∀ i ∈ s, (L i).IsSymmetric)
    (c D : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (C : Submodule 𝕜 E)
    (hC : ∀ i ∈ s, ∀ (μ : ℝ) (x : E), L i x = (μ : 𝕜) • x → D i < μ → x ∈ C)
    (n : ℝ) (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = (n : 𝕜) • LinearMap.id)
    (hn : ∑ i ∈ s, c i * D i < n) :
    C = ⊤ :=
  (Submodule.orthogonal_eq_bot_iff).1
    (orthogonal_eq_bot_of_positive_identity s L hL c D hc C hC n hsum hn)

end OrthogonalEnergy

section GradedFiniteness

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **Graded finiteness** (end of the proof of `lem:positive-c2`, line 2884).  If `V` is
spanned by finite-dimensional grades `V n`, and every grade above `N` lies in the subspace
`C`, then `V ⧸ C` is finite-dimensional.  With `C = C₂(V)` this is `C₂`-cofiniteness. -/
theorem finiteDimensional_quotient_of_graded (Vn : ℕ → Submodule K V) (hV : ⨆ n, Vn n = ⊤)
    [∀ n, FiniteDimensional K (Vn n)] (C : Submodule K V) (N : ℕ)
    (hC : ∀ n, N < n → Vn n ≤ C) :
    FiniteDimensional K (V ⧸ C) := by
  have htop : ⊤ ≤ (Finset.range (N + 1)).sup Vn ⊔ C := by
    rw [← hV]
    refine iSup_le fun n => ?_
    by_cases hn : n ≤ N
    · exact le_sup_of_le_left (Finset.le_sup (f := Vn) (Finset.mem_range.2 (by omega)))
    · exact le_sup_of_le_right (hC n (not_le.mp hn))
  have hsurj :
      Function.Surjective (C.mkQ.comp ((Finset.range (N + 1)).sup Vn).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := C.mkQ_surjective q
    obtain ⟨w, hw, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (htop (show x ∈ (⊤ : Submodule K V) from Submodule.mem_top))
    refine ⟨⟨w, hw⟩, ?_⟩
    show Submodule.Quotient.mk w = Submodule.Quotient.mk (w + y)
    rw [Submodule.Quotient.eq C]
    have hwy : w - (w + y) = -y := by abel
    rw [hwy]
    exact C.neg_mem hy
  exact FiniteDimensional.of_surjective _ hsurj

end GradedFiniteness

section C2Cofinite

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Lemma `lem:positive-c2`, assembled** (Orthogonal energy bound, lines 2846–2888).
Let `V` carry a positive form and be spanned by finite-dimensional grades `V n`.  Let
`Lᵢ` (finitely many) be symmetric, preserve every grade, and satisfy
`∑ cᵢ Lᵢ = n` on `V n` with `cᵢ ≥ 0` (the positive identity `ω_U = ∑ cᵢ eᵢ`).  If, for each
`i`, every eigenvector of `Lᵢ` in a grade with eigenvalue `> Dᵢ` lies in `C` (`= C₂(V)`),
then `V ⧸ C` is finite-dimensional: `C₂`-cofiniteness.  Gradedness of `C` is not needed. -/
theorem finiteDimensional_quotient_of_positive_identity
    (Vn : ℕ → Submodule 𝕜 V) (hV : ⨆ n, Vn n = ⊤) [∀ n, FiniteDimensional 𝕜 (Vn n)]
    {ι : Type*} [Fintype ι] (L : ι → V →ₗ[𝕜] V) (hL : ∀ i, (L i).IsSymmetric)
    (hLV : ∀ i n, ∀ x ∈ Vn n, L i x ∈ Vn n) (c D : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∀ n, ∀ x ∈ Vn n, ∑ i, (c i : 𝕜) • L i x = (n : 𝕜) • x)
    (C : Submodule 𝕜 V)
    (hC : ∀ i n, ∀ x ∈ Vn n, ∀ μ : ℝ, L i x = (μ : 𝕜) • x → D i < μ → x ∈ C) :
    FiniteDimensional 𝕜 (V ⧸ C) := by
  refine finiteDimensional_quotient_of_graded Vn hV C ⌊∑ i, c i * D i⌋₊ fun n hn => ?_
  have hn' : ∑ i, c i * D i < (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one (∑ i, c i * D i)
    have h2 : ((⌊∑ i, c i * D i⌋₊ + 1 : ℕ) : ℝ) ≤ n := Nat.cast_le.2 hn
    push_cast at h2
    linarith
  have hL' : ∀ i ∈ (Finset.univ : Finset ι), ((L i).restrict (hLV i n)).IsSymmetric :=
    fun i _ => (hL i).restrict_invariant (hLV i n)
  have hsum' : ∑ i ∈ (Finset.univ : Finset ι), (c i : 𝕜) • (L i).restrict (hLV i n) =
      ((n : ℝ) : 𝕜) • LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_sum, Submodule.coe_smul, LinearMap.coe_restrict_apply,
      RCLike.ofReal_natCast]
    exact hsum n x x.2
  have hC' : ∀ i ∈ (Finset.univ : Finset ι), ∀ (μ : ℝ) (x : Vn n),
      (L i).restrict (hLV i n) x = (μ : 𝕜) • x → D i < μ → x ∈ C.comap (Vn n).subtype := by
    intro i _ μ x hx hμ
    have hx' : L i x = (μ : 𝕜) • (x : V) := congrArg Subtype.val hx
    exact hC i n x x.2 μ hx' hμ
  have htop := eq_top_of_positive_identity Finset.univ (fun i => (L i).restrict (hLV i n)) hL'
    c D (fun i _ => hc i) (C.comap (Vn n).subtype) hC' (n : ℝ) hsum' hn'
  intro x hx
  have hmem : (⟨x, hx⟩ : Vn n) ∈ C.comap (Vn n).subtype := by
    rw [htop]
    exact Submodule.mem_top
  exact hmem

end C2Cofinite

section TopTrace

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- `L` is diagonalizable with nonnegative real eigenvalues: some finite basis of `E`
consists of eigenvectors of `L` whose eigenvalues are real and `≥ 0`. -/
def IsNonnegDiagonalizable (L : E →ₗ[𝕜] E) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) 𝕜 E) (μ : Fin m → ℝ),
    (∀ k, 0 ≤ μ k) ∧ ∀ k, L (b k) = (μ k : 𝕜) • b k

/-- Any finite eigenbasis with nonnegative real eigenvalues gives the predicate. -/
theorem IsNonnegDiagonalizable.of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 E)
    (μ : ι → ℝ) (hμ : ∀ k, 0 ≤ μ k) (L : E →ₗ[𝕜] E)
    (hL : ∀ k, L (b k) = (μ k : 𝕜) • b k) :
    IsNonnegDiagonalizable L := by
  refine ⟨Fintype.card ι, b.reindex (Fintype.equivFin ι),
    fun k => μ ((Fintype.equivFin ι).symm k), fun k => hμ _, fun k => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact hL _

/-- The trace of an operator with an eigenbasis is the sum of its eigenvalues. -/
theorem trace_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 E) (μ : ι → 𝕜) (L : E →ₗ[𝕜] E) (hL : ∀ k, L (b k) = μ k • b k) :
    LinearMap.trace 𝕜 E L = ∑ k, μ k := by
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b L, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hL k, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- The trace of a nonnegatively diagonalizable operator is a nonnegative real number `t`,
and `t = 0` only for the zero operator. -/
theorem IsNonnegDiagonalizable.exists_trace {L : E →ₗ[𝕜] E} (hL : IsNonnegDiagonalizable L) :
    ∃ t : ℝ, 0 ≤ t ∧ LinearMap.trace 𝕜 E L = (t : 𝕜) ∧ (t = 0 → L = 0) := by
  obtain ⟨m, b, μ, hμ, hb⟩ := hL
  refine ⟨∑ k, μ k, Finset.sum_nonneg fun k _ => hμ k, ?_, fun ht => ?_⟩
  · rw [trace_eq_sum_of_eigenbasis b (fun k => (μ k : 𝕜)) L hb, RCLike.ofReal_sum]
  · have h0 : ∀ k, μ k = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hμ k).1 ht k (Finset.mem_univ k)
    refine b.ext fun k => ?_
    rw [hb k, h0 k, RCLike.ofReal_zero, zero_smul, LinearMap.zero_apply]

variable [FiniteDimensional 𝕜 E]

/-- **Trace identity** (`eq:top-trace`, line 2948): `∑ cᵢ Lᵢ = h • id` implies
`h · dim E = ∑ cᵢ Tr Lᵢ`.  No commutation of the `Lᵢ` is assumed. -/
theorem top_trace_identity {ι : Type*} (s : Finset ι) (c : ι → ℝ) (L : ι → E →ₗ[𝕜] E)
    (h : 𝕜) (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = h • LinearMap.id) :
    h * (Module.finrank 𝕜 E : 𝕜) = ∑ i ∈ s, (c i : 𝕜) * LinearMap.trace 𝕜 E (L i) := by
  have htr := congrArg (LinearMap.trace 𝕜 E) hsum
  simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_id] at htr
  exact htr.symm

omit [FiniteDimensional 𝕜 E] in
/-- Under nonnegative diagonalizability, the traces are nonnegative reals. -/
theorem exists_traces {ι : Type*} (s : Finset ι) (L : ι → E →ₗ[𝕜] E)
    (hL : ∀ i ∈ s, IsNonnegDiagonalizable (L i)) :
    ∃ t : ι → ℝ, ∀ i ∈ s, 0 ≤ t i ∧ LinearMap.trace 𝕜 E (L i) = (t i : 𝕜) ∧
      (t i = 0 → L i = 0) := by
  have hex : ∀ i, ∃ t : ℝ, i ∈ s →
      (0 ≤ t ∧ LinearMap.trace 𝕜 E (L i) = (t : 𝕜) ∧ (t = 0 → L i = 0)) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨t, ht⟩ := (hL i hi).exists_trace
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose t ht using hex
  exact ⟨t, fun i hi => ht i hi⟩

/-- **`eq:top-trace` is nonnegative**: `h · dim E = ∑ cᵢ Tr Lᵢ` is a nonnegative real. -/
theorem top_trace_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (L : ι → E →ₗ[𝕜] E) (hL : ∀ i ∈ s, IsNonnegDiagonalizable (L i)) (h : 𝕜)
    (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = h • LinearMap.id) :
    ∃ r : ℝ, 0 ≤ r ∧ h * (Module.finrank 𝕜 E : 𝕜) = (r : 𝕜) := by
  obtain ⟨t, ht⟩ := exists_traces s L hL
  refine ⟨∑ i ∈ s, c i * t i,
    Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (ht i hi).1, ?_⟩
  rw [top_trace_identity s c L h hsum, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(ht i hi).2.1, RCLike.ofReal_mul]

/-- **Lowest weights are nonnegative** (line 2950): if `E ≠ 0` then `h` is real and `≥ 0`. -/
theorem exists_real_nonneg_of_top_trace [Nontrivial E] {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (L : ι → E →ₗ[𝕜] E)
    (hL : ∀ i ∈ s, IsNonnegDiagonalizable (L i)) (h : 𝕜)
    (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = h • LinearMap.id) :
    ∃ r : ℝ, 0 ≤ r ∧ h = (r : 𝕜) := by
  obtain ⟨r, hr0, hr⟩ := top_trace_nonneg s c hc L hL h hsum
  have hpos : 0 < Module.finrank 𝕜 E := Module.finrank_pos
  have hd : (0 : ℝ) < (Module.finrank 𝕜 E : ℝ) := Nat.cast_pos.2 hpos
  have hd' : (Module.finrank 𝕜 E : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  refine ⟨r / (Module.finrank 𝕜 E : ℝ), div_nonneg hr0 hd.le, ?_⟩
  rw [RCLike.ofReal_div, RCLike.ofReal_natCast, eq_div_iff hd']
  exact hr

omit [FiniteDimensional 𝕜 E] in
/-- **Nilpotent version** (lines 2965–2970): if `∑ cᵢ Lᵢ` is nilpotent on `E`, with `cᵢ > 0` and
each `Lᵢ` diagonalizable with nonnegative real eigenvalues, then every `Lᵢ = 0`. -/
theorem eq_zero_of_isNilpotent_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (L : ι → E →ₗ[𝕜] E)
    (hL : ∀ i ∈ s, IsNonnegDiagonalizable (L i))
    (hnil : IsNilpotent (∑ i ∈ s, (c i : 𝕜) • L i)) :
    ∀ i ∈ s, L i = 0 := by
  obtain ⟨t, ht⟩ := exists_traces s L hL
  have htrace : LinearMap.trace 𝕜 E (∑ i ∈ s, (c i : 𝕜) • L i) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  simp only [map_sum, map_smul, smul_eq_mul] at htrace
  have hcast : ((∑ i ∈ s, c i * t i : ℝ) : 𝕜) =
      ∑ i ∈ s, (c i : 𝕜) * LinearMap.trace 𝕜 E (L i) := by
    rw [RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(ht i hi).2.1, RCLike.ofReal_mul]
  have hreal : ∑ i ∈ s, c i * t i = 0 := RCLike.ofReal_eq_zero.1 (hcast.trans htrace)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    fun i hi => mul_nonneg (hc i hi).le (ht i hi).1).1 hreal
  intro i hi
  exact (ht i hi).2.2 ((mul_eq_zero.1 (hzero i hi)).resolve_left (hc i hi).ne')

omit [FiniteDimensional 𝕜 E] in
/-- **Weight-zero tops** (line 2951): if `∑ cᵢ Lᵢ = 0` on `E` (the case `h = 0`), with
`cᵢ > 0` and each `Lᵢ` nonnegatively diagonalizable, then every partial energy vanishes. -/
theorem eq_zero_of_top_trace_eq_zero {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (L : ι → E →ₗ[𝕜] E)
    (hL : ∀ i ∈ s, IsNonnegDiagonalizable (L i)) (h : 𝕜)
    (hsum : ∑ i ∈ s, (c i : 𝕜) • L i = h • LinearMap.id) (hh : h = 0) :
    ∀ i ∈ s, L i = 0 :=
  eq_zero_of_isNilpotent_sum s c hc L hL (by rw [hsum, hh, zero_smul]; exact IsNilpotent.zero)

end TopTrace

section VacuumLike

variable {K : Type*} [Field K] [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **Lemma `lem:vacuum-like`, first assertion** (lines 2922–2926).  Let `a n` (`n : ℤ`) be
the modes of a field acting on a module `M`, and `T = L_M(-1)` with translation covariance
`T a_{n+1} - a_{n+1} T = -(n+1) a_n`.  If `a_n v = 0` for all `n ≥ N` (lower truncation)
and `T v = 0`, then `a_n v = 0` for every `n ≥ 0`. -/
theorem modes_nonneg_eq_zero_of_translation (a : ℤ → Module.End K M) (T : Module.End K M)
    (hcov : ∀ (n : ℤ) (w : M), T (a (n + 1) w) - a (n + 1) (T w) = -((n + 1 : ℤ) : K) • a n w)
    {v : M} (hv : T v = 0) (N : ℤ) (htrunc : ∀ n, N ≤ n → a n v = 0) :
    ∀ n : ℤ, 0 ≤ n → a n v = 0 := by
  have key : ∀ k : ℕ, ∀ n : ℤ, 0 ≤ n → N - k ≤ n → a n v = 0 := by
    intro k
    induction k with
    | zero =>
      intro n _ hn
      exact htrunc n (by simpa using hn)
    | succ k ih =>
      intro n hn0 hn
      by_cases hk : N - k ≤ n
      · exact ih n hn0 hk
      · have hn1 : a (n + 1) v = 0 := ih (n + 1) (by omega) (by omega)
        have h := hcov n v
        rw [hn1, hv, map_zero, map_zero, sub_zero] at h
        have hne : ((n + 1 : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (by omega)
        have h' : ((n + 1 : ℤ) : K) • a n v = 0 := by
          rw [← neg_eq_zero, ← neg_smul]
          exact h.symm
        exact (smul_eq_zero.1 h').resolve_left hne
  intro n hn
  have hle := Int.self_le_toNat (N - n)
  exact key (N - n).toNat n hn (by omega)

omit [CharZero K] in
/-- The last step of the weight-zero argument (lines 2953–2955): if every partial translation
`Kᵢ = L^{eᵢ}(-1)` kills `v`, then so does `L_V(-1) = ∑ cᵢ Kᵢ`. -/
theorem sum_smul_apply_eq_zero {ι : Type*} (s : Finset ι) (c : ι → K)
    (Kop : ι → Module.End K M) {v : M} (hv : ∀ i ∈ s, Kop i v = 0) :
    (∑ i ∈ s, c i • Kop i) v = 0 := by
  rw [LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i hi => by rw [LinearMap.smul_apply, hv i hi, smul_zero]

end VacuumLike

section Growth

open Filter
open scoped Nat

/-- For all real `d` and `C`, eventually `d² · C^{2n} < n!`. -/
theorem eventually_sq_mul_pow_lt_factorial (d C : ℝ) :
    ∀ᶠ n : ℕ in atTop, d ^ 2 * C ^ (2 * n) < (n ! : ℝ) := by
  filter_upwards [FloorSemiring.eventually_mul_pow_lt_factorial_sub (d ^ 2) (C ^ 2) 0]
    with n hn
  simpa [pow_mul] using hn

/-- Iterating the right-exactness bound `a (n+1) ≤ C · a n`. -/
theorem le_pow_mul_of_step {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, a (n + 1) ≤ C * a n) : ∀ n, a n ≤ C ^ n * a 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc a (n + 1) ≤ C * a n := ha n
      _ ≤ C * (C ^ n * a 0) := mul_le_mul_of_nonneg_left ih hC
      _ = C ^ (n + 1) * a 0 := by ring

/-- **Moderate growth** (`lem:projective-unit`, lines 2994–3000).  If the underlying
dimensions `a n = d₀(X^{⊗ n})` satisfy `a (n+1) ≤ C · a n` and the endomorphism dimensions
satisfy `e n ≤ (a n)²`, then `e n < n!` for all sufficiently large `n`. -/
theorem eventually_lt_factorial_of_step {a e : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a (n + 1) ≤ C * a n) (he : ∀ n, e n ≤ a n ^ 2) :
    ∀ᶠ n : ℕ in atTop, e n < (n ! : ℝ) := by
  filter_upwards [eventually_sq_mul_pow_lt_factorial (a 0) C] with n hn
  calc e n ≤ a n ^ 2 := he n
    _ ≤ (C ^ n * a 0) ^ 2 := pow_le_pow_left₀ (ha0 n) (le_pow_mul_of_step hC ha n) 2
    _ = a 0 ^ 2 * C ^ (2 * n) := by ring
    _ < (n ! : ℝ) := hn

end Growth

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.re_inner_le_of_eigenvectors_mem
#print axioms HaagerupIzumi.C8.orthogonal_eq_bot_of_positive_identity
#print axioms HaagerupIzumi.C8.eq_top_of_positive_identity
#print axioms HaagerupIzumi.C8.finiteDimensional_quotient_of_graded
#print axioms HaagerupIzumi.C8.finiteDimensional_quotient_of_positive_identity
#print axioms HaagerupIzumi.C8.top_trace_identity
#print axioms HaagerupIzumi.C8.top_trace_nonneg
#print axioms HaagerupIzumi.C8.exists_real_nonneg_of_top_trace
#print axioms HaagerupIzumi.C8.eq_zero_of_isNilpotent_sum
#print axioms HaagerupIzumi.C8.eq_zero_of_top_trace_eq_zero
#print axioms HaagerupIzumi.C8.eventually_sq_mul_pow_lt_factorial
#print axioms HaagerupIzumi.C8.eventually_lt_factorial_of_step
#print axioms HaagerupIzumi.C8.modes_nonneg_eq_zero_of_translation
#print axioms HaagerupIzumi.C8.sum_smul_apply_eq_zero
