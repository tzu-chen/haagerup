module

public import HaagerupIzumi.C8.ProofMap
public import HaagerupIzumi.C8.PositiveStress
public import HaagerupIzumi.C8.Regularity.Energy
public import HaagerupIzumi.C8.VertexAlgebra.Basic

@[expose] public section

/-!
# The positive-stress and `C₂` arrows of the proof map, made concrete

Appendix F of `c8_expanded_20260929/haagerup_c8_expanded.tex` (lines 2688–2888) has two
manuscript arrows in `ProofMap` whose concrete core is formalized:

* `L_positiveStress : certStructural → pf13Factor → positiveStress` (eq:finite-positive-stress,
  lines 2688–2721: Haar averages lie in compact convex hulls, Carathéodory);
* `L_c2 : positiveStress → initialGrades → c2Cofinite` (Lemma `lem:positive-c2`, the orthogonal
  energy bound, lines 2846–2888).

The concrete objects (`StressData`): `U` as a vertex operator algebra `S.U` over `ℂ` on a space
`H` with its positive form; the finite-dimensional real space `E` of PCT-fixed weight-two vectors
with its inclusion `S.ιE : E → H` (additive, `ℝ`-homogeneous, into `U₂`); the conformal vector
`S.ω ∈ E` (with `ιE ω = ω_U`); the Haar averages `S.avg k` of the conformal vectors of the four
factors `A_{1,1}, A_{1,39}, K(𝔰𝔩₂,3), K(𝔰𝔩₂,13)` (`k : Fin 4`); their orbits `S.K k` under the
compact current group; and the remaining factor properties `S.factorNonneg k`.  The zero mode of
`z ∈ E` is `S.U.mode 1 (S.ιE z)` (its `L(0)`), and `C₂(U) = span {a_(-2) b}` (`C2`), so the node
`c2Cofinite` is a statement about the vertex algebra `S.U` itself.

`regularityNodes R S` overrides three nodes of `R : Nodes`:

* `certStructural`: `R.certStructural`, and eq:positive-stress
  `ω = ω_{A₁,₁} + (3403/4563) ω̄_{A₁,₃₉} + (25/6) p̄ + (25/26) z̄` in terms of the averages
  (`stressCoeff`);
* `positiveStress`: eq:finite-positive-stress, `ω = ∑_{i < N} c_i z_i` with `c_i > 0` and each
  `z_i` in the orbit of a factor conformal vector; for every factor a bound `D` such that every
  orbit point has symmetric zero mode whose eigenvectors of energy `> D` lie in `C₂(U)`
  (`FactorEnergy`: the content of "regular unitary factors" used by `lem:positive-c2`); and the
  nonnegativity of the factors' lowest weights (`factorNonneg`, an opaque predicate used by the
  unproved `L_projectiveVacuum`);
* `c2Cofinite`: `H ⧸ C₂(U)` is finite-dimensional.

`U` here is not linked to the subalgebra `D.U u` of the properness branch (that model is over an
arbitrary field and has no positive form); the predicate `factorNonneg` is not modelled.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 MeasureTheory

/-- The coefficients `1, 3403/4563, 25/6, 25/26` of eq:positive-stress. -/
noncomputable def stressCoeff : Fin 4 → ℝ := ![1, 3403 / 4563, 25 / 6, 25 / 26]

theorem stressCoeff_pos : ∀ i, 0 < stressCoeff i := by
  obtain ⟨h0, h1, h2, h3⟩ := PositiveStress.positive_stress_coefficients
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- `C₂(U) = span {a_(-2) b}`. -/
def C2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : VertexOperatorAlgebra ℂ H) : Submodule ℂ H :=
  Submodule.span ℂ {x | ∃ a b : H, x = U.mode (-2) a b}

/-- The concrete data of the positive stress identity. -/
structure StressData (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vertex operator algebra `U` on the space `H` carrying its positive form. -/
  U : VertexOperatorAlgebra ℂ H
  /-- The inclusion of the real space `E` of PCT-fixed weight-two vectors. -/
  ιE : E → H
  ιE_add : ∀ x y, ιE (x + y) = ιE x + ιE y
  ιE_smul : ∀ (r : ℝ) x, ιE (r • x) = (r : ℂ) • ιE x
  ιE_grade : ∀ x, ιE x ∈ U.grade 2
  /-- The conformal vector `ω_U`. -/
  ω : E
  ιE_ω : ιE ω = U.ω
  /-- The Haar averages of the factor conformal vectors `ω_{A₁,₁}, ω_{A₁,₃₉}, p, z`. -/
  avg : Fin 4 → E
  /-- The orbits of the factor conformal vectors under the compact current group. -/
  K : Fin 4 → Set E
  /-- "All simple modules of the `k`-th factor have nonnegative lowest weights, zero only for its
  vacuum" (lines 2719–2721); used by the unproved `L_projectiveVacuum`, not modelled. -/
  factorNonneg : Fin 4 → Prop

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The zero mode `L^z(0) = z_(1)` of an orbit point `z` is symmetric, and its eigenvectors of
energy above `D` lie in `C₂(U)`: what "regular unitary factor" gives in the proof of
`lem:positive-c2` (lines 2851–2873). -/
def FactorEnergy (S : StressData E H) (D : ℝ) (z : E) : Prop :=
  (S.U.mode 1 (S.ιE z)).IsSymmetric ∧
    ∀ n, ∀ x ∈ S.U.grade n, ∀ μ : ℝ, S.U.mode 1 (S.ιE z) x = (μ : ℂ) • x → D < μ → x ∈ C2 S.U

/-- The proof map with `certStructural` (its positive-stress part), `positiveStress` and
`c2Cofinite` made concrete. -/
def regularityNodes (R : Nodes) (S : StressData E H) : Nodes :=
  { R with
    certStructural := R.certStructural ∧ S.ω = ∑ k, stressCoeff k • S.avg k
    positiveStress := (∃ (N : ℕ) (z : Fin N → E) (c : Fin N → ℝ) (src : Fin N → Fin 4),
        (∀ i, z i ∈ S.K (src i)) ∧ (∀ i, 0 < c i) ∧ S.ω = ∑ i, c i • z i) ∧
      (∀ k, ∃ D : ℝ, ∀ z ∈ S.K k, FactorEnergy S D z) ∧ ∀ k, S.factorNonneg k
    c2Cofinite := FiniteDimensional ℂ (H ⧸ C2 S.U) }

/-- **`L_positiveStress`** (eq:finite-positive-stress, lines 2688–2721).

* Concrete nodes: `certStructural` (eq:positive-stress with the averages), `pf13Factor` (the
  factor properties are applied to it), `positiveStress`.
* Concrete theorem: `PositiveStress.average_identity_finite` (the Haar average of an orbit lies in
  the compact convex hull of the orbit, `PositiveStress.isCompact_convexHull`; Carathéodory gives
  a finite positive combination), with `PositiveStress.positive_stress_coefficients`.
* Remaining inputs: `μ`, `f`, `hf`, `hfK`, `havg` ([definitional]: the averages are integrals of
  the orbit maps against Haar probability measures of the compact current group), `hK`
  ([standard]: orbits of a compact group are compact); `hfac` ([external] Abe–Buhl–Dong
  Proposition 5.2 for the finitely many simple modules of each regular factor, unitarity, and
  [manuscript step] complete reducibility of `U` as a weak module and `C_{2,A}(U) ⊆ C₂(U)`;
  conjugate factors share the bound), `hnonneg` ([external], uncited in the manuscript); both are
  stated conditionally on `pf13Factor`, which identifies the fourth factor. -/
theorem positiveStress_arrow (R : Nodes) (S : StressData E H)
    {G : Fin 4 → Type*} [∀ k, MeasurableSpace (G k)] (μ : ∀ k, Measure (G k))
    [∀ k, IsProbabilityMeasure (μ k)] (f : ∀ k, G k → E) (hf : ∀ k, Integrable (f k) (μ k))
    (hK : ∀ k, IsCompact (S.K k)) (hfK : ∀ k g, f k g ∈ S.K k)
    (havg : ∀ k, S.avg k = ∫ g, f k g ∂(μ k))
    (hfac : R.pf13Factor → ∀ k, ∃ D : ℝ, ∀ z ∈ S.K k, FactorEnergy S D z)
    (hnonneg : R.pf13Factor → ∀ k, S.factorNonneg k) :
    (regularityNodes R S).certStructural → (regularityNodes R S).pf13Factor →
      (regularityNodes R S).positiveStress := by
  rintro ⟨-, hω⟩ hpf
  obtain ⟨ι, hι, z, c, src, hz, hc, hωz⟩ := PositiveStress.average_identity_finite μ f hf S.K hK
    hfK stressCoeff stressCoeff_pos S.ω (by rw [hω]; simp only [havg])
  refine ⟨⟨Fintype.card ι, z ∘ (Fintype.equivFin ι).symm, c ∘ (Fintype.equivFin ι).symm,
    src ∘ (Fintype.equivFin ι).symm, fun i => hz _, fun i => hc _, ?_⟩, hfac hpf, hnonneg hpf⟩
  rw [hωz]
  exact ((Fintype.equivFin ι).symm.sum_comp (fun j => c j • z j)).symm

omit [FiniteDimensional ℝ E] in
/-- **`L_c2`** (Lemma `lem:positive-c2`, lines 2846–2888).

* Concrete nodes: `positiveStress` (the finite identity and the factor energy bounds),
  `c2Cofinite`.  `initialGrades` stays opaque.
* Concrete theorem: `finiteDimensional_quotient_of_positive_identity` (Regularity/Energy: the
  spectral theorem for each `L^{z_i}(0)` separately, the energy bound on `V_n ∩ C₂(V)^⊥`, and
  graded finiteness); `L(0) = ∑ c_i L^{z_i}(0)` on `V_n` is derived from `ω = ∑ c_i z_i`, the
  linearity of modes and `ω_(1) = L(0)` (`VertexOperatorAlgebra.L0`), grade preservation from
  `VertexAlgebra.mode_grade`.
* Remaining input: the grades of `U` are finite-dimensional (instance argument; [definitional]
  CFT type with finite-dimensional grades, part of `initialGrades`). -/
theorem c2_arrow (R : Nodes) (S : StressData E H) [∀ n, FiniteDimensional ℂ (S.U.grade n)] :
    (regularityNodes R S).positiveStress → (regularityNodes R S).initialGrades →
      (regularityNodes R S).c2Cofinite := by
  rintro ⟨⟨N, z, c, src, hz, hc, hωz⟩, hfac, -⟩ -
  choose D hD using hfac
  have hV : ⨆ n, S.U.grade n = ⊤ := S.U.grade_internal.submodule_iSup_eq_top
  have hιsum : S.ιE (∑ i, c i • z i) = ∑ i, (c i : ℂ) • S.ιE (z i) := by
    have h := map_sum (AddMonoidHom.mk' S.ιE S.ιE_add) (fun i => c i • z i) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => S.ιE_smul (c i) (z i)
  refine finiteDimensional_quotient_of_positive_identity S.U.grade hV
    (fun i => S.U.mode 1 (S.ιE (z i))) (fun i => (hD _ _ (hz i)).1) (fun i n x hx => ?_) c
    (fun i => D (src i)) (fun i => (hc i).le) (fun n x hx => ?_) (C2 S.U)
    (fun i n x hx μ h1 h2 => (hD _ _ (hz i)).2 n x hx μ h1 h2)
  · show S.U.mode 1 (S.ιE (z i)) x ∈ S.U.grade n
    have h := S.U.mode_grade (i := 2) (j := n) 1 (S.ιE_grade (z i)) hx (by omega)
    convert h using 2
    omega
  · have h := S.U.L0 hx
    rw [← S.ιE_ω, hωz, hιsum, map_sum, LinearMap.sum_apply] at h
    have key : ∑ i, (c i : ℂ) • S.U.mode 1 (S.ιE (z i)) x = (n : ℂ) • x := by
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply]
    exact key

/-- **The two regularity arrows of the proof map are theorems** for `regularityNodes R S`, under
the inputs listed in `positiveStress_arrow` and `c2_arrow`. -/
theorem regularity_arrows (R : Nodes) (S : StressData E H)
    {G : Fin 4 → Type*} [∀ k, MeasurableSpace (G k)] (μ : ∀ k, Measure (G k))
    [∀ k, IsProbabilityMeasure (μ k)] (f : ∀ k, G k → E) (hf : ∀ k, Integrable (f k) (μ k))
    (hK : ∀ k, IsCompact (S.K k)) (hfK : ∀ k g, f k g ∈ S.K k)
    (havg : ∀ k, S.avg k = ∫ g, f k g ∂(μ k))
    (hfac : R.pf13Factor → ∀ k, ∃ D : ℝ, ∀ z ∈ S.K k, FactorEnergy S D z)
    (hnonneg : R.pf13Factor → ∀ k, S.factorNonneg k)
    [∀ n, FiniteDimensional ℂ (S.U.grade n)] :
    let N := regularityNodes R S
    (N.certStructural → N.pf13Factor → N.positiveStress) ∧
    (N.positiveStress → N.initialGrades → N.c2Cofinite) :=
  ⟨positiveStress_arrow R S μ f hf hK hfK havg hfac hnonneg, c2_arrow R S⟩

#print axioms positiveStress_arrow
#print axioms c2_arrow
#print axioms regularity_arrows

end HaagerupIzumi.C8.ProofMap
