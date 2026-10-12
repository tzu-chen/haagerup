module

public import HaagerupIzumi.C8.ProofMapConcrete
public import HaagerupIzumi.C8.Lattice.P4Link
public import HaagerupIzumi.C8.Lattice.P4Left
public import HaagerupIzumi.C8.Lattice.P4RFRP
public import HaagerupIzumi.C8.Lattice.P4RFRZ
public import HaagerupIzumi.C8.Lattice.P4RFRM
public import HaagerupIzumi.C8.Lattice.P4RDerived
public import HaagerupIzumi.C8.Lattice.P4RL2
public import HaagerupIzumi.C8.Lattice.KS21
public import HaagerupIzumi.C8.Lattice.PCTLink
public import HaagerupIzumi.C8.Lattice.PCTModes
public import HaagerupIzumi.C8.Lattice.FLMReduce
public import HaagerupIzumi.C8.Lattice.S2Closure

@[expose] public section

/-!
# The concrete proof map for the actual lattice VOA

`concrete_proof_map` (`ProofMapConcrete`) is stated for arbitrary closure data `D : ClosureData A`
over an arbitrary vertex operator algebra `A`.  Here it is instantiated at the lattice model of
`Lattice/`: the algebra is `latticeVOA` of the Fock model `V_{E₆⊕A₂}` (`latA hB`), which needs
only the Borcherds identity `hB : FLMBorcherds` (FLM Theorem 8.10.2, **[external]**; `FLMInput`
follows from it, `flmInput_of_borcherds`), and the closure data is `latticeDP` (`latD hB S₃ hS₃`):
the six currents of `eq:leftcurrents`, `eq:rightcurrents`, `S₂ = S2span` (the 120 echelon vectors
of the minimal-generation record), `u = uV`, the actual triplet `P₄ = (q₊, q₀, q₋)`; only `S₃`
(dimension 956, not yet exported) remains a parameter.

**What the lattice model discharges** (each checked against the node it replaces):

* `C_dimensions`: the node `certDimensions` of `ProofMapProperness.concreteNodes` is
  `dim K = 6 ∧ dim B₁ = 86 ∧ IsSl2SumSpan A K`; `certDimensions_latticeD` is a theorem about that
  very node (`certDimensions_latD`).
* `C_finiteClosure`, partly: the node is `certFiniteClosureProp D u` =
  `LowerCertificate D ∧ (Gate 4 ∧ Gate 5) ∧ (raising nilpotence) ∧ (lowering nilpotence) ∧
  ω ∈ S₂ ∧ u ∈ S₂ ∧ S₂ ≤ U`.  The last three conjuncts are `minimalGeneration_latticeD`
  (`omegaV_mem_S2span`, `uV_mem_S2span`, `S2span_le_U`); of the 26 fields of `LowerCertificate`,
  nineteen are theorems for `latticeDP`: `KK0` (`K_(0) K ⊆ K`, `KK0_latD`: the kernel-checked current
  brackets of `Lattice/Relations.lean` with skew symmetry); `ω_mem` (`omegaV_mem_S2span`);
  `KS₂0`, `TK`, `KmK`
  (`K_(0) S₂ ⊆ S₂`, `T K ⊆ S₂`, `K₋₁K ⊆ S₂`: the closure conditions `S2Closed_S2span` of the
  minimal-generation record, i.e. the half `closureSpace ≤ S₂` of `S2span_eq_closureSpace`, with
  `T x = x_(-2) 𝟏`); `hL_q`, `hR_qp`, `hR_q0`, `hR_qm` (`P4Link`, the Cartan controls of the actual
  triplet); `eL_q`, `fL_q` (`P4Left`); `fR_qp`, `fR_q0`, `fR_qm` (`P4RFRP`, `P4RFRZ`, `P4RFRM`); `eR_qp`, `eR_q0`, `eR_qm` (`P4RERP`,
  `P4RDerived`, the last two by the commutator formula); the Virasoro control `L2_P₄`
  (`L(2) P₄ ⊆ S₂`, `P4RL2`); `KS₂1` (`K_(1) S₂ ⊆ K`, `KS21`: 720 kernel checks with `modeQRF`,
  about 320 s of kernel time).  The remaining 7 fields are
  `LowerRest`; Gates 4/5 and
  the two nilpotence
  statements stay inputs (`LatticeClosureInputs`), all stated about the concrete algebra.
* `C_pct`: in `ProofMap` the node `certPCT` is an opaque proposition, so no concrete statement
  can discharge it as it stands.  `pctNodes R D u` gives it the meaning `PCTCert D u` used at
  line 2604: `θ_g = pctV` (the map `eq:pct`, lines 1975–1989) is compatible with all modes
  (`PCTModeCompatible`; with the proved antilinearity `pctV_smul` and `θ_g² = 1`, an antilinear
  automorphism), `θ_g S₂ = S₂` (`certPCT_latticeD`), and `θ_g U = U` (`pctV_mem_U_latD`, proved
  here from the first two, `θ_g 𝟏 = 𝟏`, `θ_g ω = ω` and `S₂ ≤ U`: each current `k` is
  `½ L(1) T k` with `T k ∈ S₂`).  The first conjunct is a theorem with no hypotheses:
  `LatticeVOA.pctModeCompatible` (Lattice/PCTModes.lean: reduction to basis states and the
  cocycle identity `ε(-α, -β) = ε(α, β)`).  So all three conjuncts are proved, and the PCT node
  is discharged outright.  The node is used only as a premise of `E_cklw529`, whose remaining
  content is: the transported form `⟨v, w⟩_g` is positive definite with PCT operator `θ_g`
  (Dong–Lin unitarity of the lattice VOA, transported by `g`, lines 1985–1987), so the
  `θ_g`-stable `U` is a unitary subalgebra, hence simple (CKLW Proposition 5.29), with `c = 8`
  and the initial grades.
* Not needed by any node: `finrank_S2span` (`dim S₂ = 120`); of `S2span_eq_closureSpace` (all
  524 closure relations) the nodes use `S₂ ≤ closureSpace` (giving `S₂ ≤ U`) and the closure
  conditions (giving `KS₂0`, `TK`, `KmK`).

**What stays an input** (tagged **[certificate]**): `LowerRest` (the 7 other lower
identities: the products of `S₂` with `S₂` in `S₃`, `S₂`, `K`, the
provenance of `S₃` and `P₄` and the Virasoro control `L(1) P₄ ⊆ S₃`), the Gate 4 and Gate 5
certificates, and the two nilpotence statements on `S₃`, bundled in `LatticeClosureInputs`; the
other seventeen fields of `RemainingInputs` (`LatticeRemainingInputs`: `C_structural`,
`C_discriminant` and the fifteen `E_`/open `L_` arrows), and all other inputs of
`concrete_proof_map`, unchanged.

`lattice_proof_map`: from `FLMBorcherds` and these inputs, the conclusions of
`concrete_proof_map` for the lattice VOA, in particular properness `U = ⟨K, ω, u⟩ ≠ V_{E₆⊕A₂}`
and `U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂` *for the actual algebra and the actual `S₂`, `u`, `P₄`*.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Fusion HaagerupIzumi.C8.Characters MeasureTheory
open CategoryTheory MonoidalCategory Limits ClosureData

/-! ### The lattice algebra and its closure data -/

/-- The lattice vertex operator algebra `V_{E₆⊕A₂}` of the Fock model, from the Borcherds
identity alone. -/
noncomputable abbrev latA (hB : LatticeVOA.FLMBorcherds) : VertexOperatorAlgebra ℂ LatticeVOA.V :=
  LatticeVOA.latticeVOA (LatticeVOA.flmInput_of_borcherds hB)

/-- The closure data of the lattice VOA: the actual currents, `S₂ = S2span`, the actual
triplet `P₄`; `S₃` is a parameter. -/
noncomputable abbrev latD (hB : LatticeVOA.FLMBorcherds) (S₃ : Submodule ℂ LatticeVOA.V)
    (hS₃ : S₃ ≤ LatticeVOA.gradeC 3) : ClosureData (latA hB) :=
  LatticeVOA.latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃

/-! ### The PCT node -/

/-- **[definitional]** The PCT node (lines 1975–1992, 2604): the transported PCT map
`θ_g = pctV` (`eq:pct`) is compatible with all modes (with `pctV_smul`, `pctV_pctV`: an
antilinear involutive automorphism of the lattice VOA), it preserves `S₂` (the exact PCT
certificate) and it preserves `U = ⟨K, ω, u⟩` (line 2604: "`U` is PCT-stable"). -/
def PCTCert {A : VertexOperatorAlgebra ℂ LatticeVOA.V} (D : ClosureData A) (u : LatticeVOA.V) :
    Prop :=
  LatticeVOA.PCTModeCompatible ∧ (∀ x : LatticeVOA.V, LatticeVOA.pctV x ∈ D.S₂ ↔ x ∈ D.S₂) ∧
    ∀ x : LatticeVOA.V, LatticeVOA.pctV x ∈ D.U u ↔ x ∈ D.U u

/-- The proof map with the node `certPCT` given its manuscript meaning (`PCTCert`). -/
def pctNodes (R : Nodes) {A : VertexOperatorAlgebra ℂ LatticeVOA.V} (D : ClosureData A)
    (u : LatticeVOA.V) : Nodes :=
  { R with certPCT := PCTCert D u }

/-- A vector of weight one is `½ L(1) T x` (`L(1) T x = T L(1) x + 2x` and `L(1) x ∈ V₀ = ℂ𝟏`). -/
theorem wt_one_eq_L1_T (A : VertexOperatorAlgebra ℂ LatticeVOA.V) {x : LatticeVOA.V}
    (hx : x ∈ A.grade 1) : x = (2 : ℂ)⁻¹ • A.mode 2 A.ω (A.T x) := by
  have h0 : A.mode 2 A.ω x ∈ A.grade 0 := by
    have h := A.mode_grade 2 A.ω_mem hx (by norm_num)
    simpa using h
  rw [A.L1_T hx, A.toVertexAlgebra.T_grade_zero h0, zero_add, smul_smul]
  norm_num

/-! ### The certificate inputs that remain -/

section
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {A : VertexOperatorAlgebra k V}

/-- **[certificate]** The 7 fields of `LowerCertificate` (Setup.lean) other than `KK0`, `ω_mem`,
`KS₂0`, `KS₂1`, `TK`, `KmK`, the six current controls `hL_q`, `eL_q`, `fL_q`, `hR_qp`, `hR_q0`,
`hR_qm`, the six `eR_*`, `fR_*` controls and `L2_P₄`, which the lattice model proves for
`latticeDP`. -/
structure LowerRest (D : ClosureData A) : Prop where
  S₂S₂0 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, A.mode 0 a b ∈ D.S₃
  S₂S₂1 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, A.mode 1 a b ∈ D.S₂
  S₂S₂2 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, A.mode 2 a b ∈ D.K
  N₃_le_S₃ : D.N₃ ≤ D.S₃
  S₃_prov : D.S₃ ≤ D.N₃ ⊔ A.zeroProd D.S₂ D.S₂
  P₄_prov : D.P₄ ≤ A.zeroProd D.S₂ D.S₃ ⊔ D.fullN₄
  L1_P₄ : ∀ q ∈ D.triplet, A.mode 2 A.ω q ∈ D.S₃

end

/-- **[certificate]** The finite-closure certificates that the lattice model does not yet prove,
about the actual algebra and closure data: `LowerRest`, the Gate 4 and Gate 5 certificates, and
nilpotence of the raising and lowering words of length 25 on `S₃` (cert:lower, Gates 4/5,
lines 2253–2600). -/
structure LatticeClosureInputs (hB : LatticeVOA.FLMBorcherds) (S₃ : Submodule ℂ LatticeVOA.V)
    (hS₃ : S₃ ≤ LatticeVOA.gradeC 3) : Prop where
  lower : LowerRest (latD hB S₃ hS₃)
  gates : ∃ G : Gate4Certificate (latD hB S₃ hS₃), Nonempty (Gate5Certificate (latD hB S₃ hS₃) G)
  nilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ (latD hB S₃ hS₃).S₃,
    CFT.raisingWord ((latA hB).mode 0 (latD hB S₃ hS₃).eL) ((latA hB).mode 0 (latD hB S₃ hS₃).eR)
      w v = 0
  nilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ (latD hB S₃ hS₃).S₃,
    CFT.raisingWord ((latA hB).mode 0 (latD hB S₃ hS₃).fL) ((latA hB).mode 0 (latD hB S₃ hS₃).fR)
      w v = 0

/-- The fields of `RemainingInputs` other than `C_finiteClosure`, `C_dimensions`, `C_pct`. -/
structure LatticeRemainingInputs (N : Nodes) : Prop where
  C_structural : N.certStructural
  C_discriminant : N.certDiscriminant
  E_cklw529 : N.strongGen → N.certPCT → N.initialGrades
  L_rational : N.rigidSemisimple → N.c2Cofinite → N.initialGrades → N.stronglyRational
  E_dmno : N.branchH → N.stronglyRational → N.projectiveVacuum → N.branchB →
    N.certDiscriminant → N.lagrangianCenter
  E_gsy : N.twelveTwists → N.untwistedPointed → N.multiplicityOne → N.lagrangianCenter →
    N.modularData
  E_netCR : N.stronglyRational → N.initialGrades → N.netCompletelyRational
  L_reconstruction : N.netCompletelyRational → N.stronglyRational → N.initialGrades →
    N.reconstruction
  L_annulus : N.reconstruction → N.netCompletelyRational → N.initialGrades → N.annulus
  E_tener : N.stronglyUnitary → N.annulus → N.completelyUnitary
  L_boundaryUnitary : N.completelyUnitary → N.lagrangianCenter → N.boundaryUnitary
  E_izumi : N.boundaryUnitary → N.multiplicityOne → N.untwistedPointed → N.boundaryIsHaagerup
  E_moritaCenter : N.boundaryIsHaagerup → N.lagrangianCenter → N.completelyUnitary →
    N.repIsCenter
  E_netCenter : N.netCount → N.netRepIsCenter
  E_netExtension : N.netRepIsCenter → N.netCompletelyRational → N.netExtension
  E_diagonal : N.netCompletelyRational → N.netCount → N.reconstruction →
    N.characterVector → N.stronglyUnitary → N.diagonalTheory
  E_e8Extension : N.repIsCenter → N.projectiveVacuum → N.stronglyRational →
    N.completelyUnitary → N.e8Extension

/-! ### The three certificate nodes for the lattice model -/

section
variable (hB : LatticeVOA.FLMBorcherds) (S₃ : Submodule ℂ LatticeVOA.V)
  (hS₃ : S₃ ≤ LatticeVOA.gradeC 3)

open LatticeVOA in
/-- **`K_(0) K ⊆ K`** (the field `KK0` of `LowerCertificate`) for the lattice currents: the
kernel-checked brackets of `Lattice/Relations.lean` (`left_sl2`, `right_sl2`,
`left_right_commute`) give `a_(0) b` for one order of each pair of currents, and skew symmetry
of the lattice vertex algebra (`b_(0) a = -a_(0) b + T(a_(1) b)` on weight one, `T 𝟏 = 0`)
gives the other order. -/
theorem KK0_latD : ∀ x ∈ (latD hB S₃ hS₃).K, ∀ y ∈ (latD hB S₃ hS₃).K,
    (latA hB).mode 0 x y ∈ (latD hB S₃ hS₃).K := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -, l8, l9, l10, -, -⟩ := left_sl2
  obtain ⟨r1, r2, r3, r4, r5, r6, -, r8, r9, r10, -, -⟩ := right_sl2
  have lr := left_right_commute
  have kc : ∀ c : Vec, (c = hL ∨ c = eL ∨ c = fL ∨ c = hR ∨ c = eR ∨ c = fR) →
      toV c ∈ (latD hB S₃ hS₃).K := fun _ hc => current_mem_Kspan hc
  have kh := kc hL (Or.inl rfl)
  have ke := kc eL (Or.inr (Or.inl rfl))
  have kf := kc fL (Or.inr (Or.inr (Or.inl rfl)))
  have kH := kc hR (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have kE := kc eR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have kF := kc fR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have k0 : toV [] ∈ (latD hB S₃ hS₃).K := by
    rw [toV_nil]
    exact Submodule.zero_mem _
  have ks : ∀ (q : ℚ) {c : Vec}, toV c ∈ (latD hB S₃ hS₃).K →
      toV (smul q c) ∈ (latD hB S₃ hS₃).K := fun q c hc => by
    rw [toV_smul]
    exact Submodule.smul_mem _ _ hc
  have ghL : toV hL ∈ (latA hB).grade 1 := toV_mem_gradeC _ (currents_basisStates 0)
  have geL : toV eL ∈ (latA hB).grade 1 := toV_mem_gradeC _ (currents_basisStates 1)
  have gfL : toV fL ∈ (latA hB).grade 1 := toV_mem_gradeC _ (currents_basisStates 2)
  have ghR : toV hR ∈ (latA hB).grade 1 := toV_mem_gradeC _ (currents_basisStates 3)
  have geR : toV eR ∈ (latA hB).grade 1 := toV_mem_gradeC _ (currents_basisStates 4)
  have gfR : toV fR ∈ (latA hB).grade 1 := toV_mem_gradeC _ (currents_basisStates 5)
  have tnil : (latA hB).T (toV []) = 0 := by rw [toV_nil, map_zero]
  have tvac : (latA hB).T (toV vac) = 0 := by
    rw [toV_vac]
    exact VertexAlgebra.T_vac (latA hB).toVertexAlgebra
  have tsv : ∀ q : ℚ, (latA hB).T (toV (smul q vac)) = 0 := fun q => by
    rw [toV_smul, map_smul, tvac, smul_zero]
  -- one order of a pair: the kernel-checked bracket
  have direct : ∀ {a b c : Vec}, (∀ p ∈ a, Valid p.1) → (∀ p ∈ b, Valid p.1) →
      mode a 0 b = c → toV c ∈ (latD hB S₃ hS₃).K →
      (latA hB).mode 0 (toV a) (toV b) ∈ (latD hB S₃ hS₃).K := fun ha hb h hc => by
    show modeC 0 (toV _) (toV _) ∈ _
    rw [modeC_toV_of_mode ha hb h]
    exact hc
  -- the other order, by skew symmetry
  have opp : ∀ {a b c d : Vec}, (∀ p ∈ a, Valid p.1) → (∀ p ∈ b, Valid p.1) →
      toV a ∈ (latA hB).grade 1 → toV b ∈ (latA hB).grade 1 → mode a 0 b = c →
      toV c ∈ (latD hB S₃ hS₃).K → mode a 1 b = d → (latA hB).T (toV d) = 0 →
      (latA hB).mode 0 (toV b) (toV a) ∈ (latD hB S₃ hS₃).K := by
    intro a b c d ha hb ha1 hb1 h0 hc h1 hd
    refine VertexAlgebra.skew_mem (latA hB).toVertexAlgebra ha1 hb1 0 fun t ht => ?_
    have ht' : t = 0 ∨ t = 1 := by
      simp only [Int.natAbs_zero, add_zero] at ht
      omega
    rcases ht' with rfl | rfl
    · have e0 : (latA hB).mode (0 + ((0 : ℕ) : ℤ)) (toV a) (toV b) = toV c := by
        show modeC _ (toV a) (toV b) = toV c
        rw [show (0 : ℤ) + ((0 : ℕ) : ℤ) = 0 by norm_num]
        exact modeC_toV_of_mode ha hb h0
      rw [e0, pow_zero]
      exact hc
    · have e1 : (latA hB).mode (0 + ((1 : ℕ) : ℤ)) (toV a) (toV b) = toV d := by
        show modeC _ (toV a) (toV b) = toV d
        rw [show (0 : ℤ) + ((1 : ℕ) : ℤ) = 1 by norm_num]
        exact modeC_toV_of_mode ha hb h1
      rw [e1, pow_one, hd]
      exact Submodule.zero_mem _
  have hgen : ∀ x ∈ (latD hB S₃ hS₃).currents, ∀ y ∈ (latD hB S₃ hS₃).currents,
      (latA hB).mode 0 x y ∈ (latD hB S₃ hS₃).K := by
    intro x hx y hy
    have hx' : x = toV hL ∨ x = toV eL ∨ x = toV fL ∨ x = toV hR ∨ x = toV eR ∨ x = toV fR := hx
    have hy' : y = toV hL ∨ y = toV eL ∨ y = toV fL ∨ y = toV hR ∨ y = toV eR ∨ y = toV fR := hy
    rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl
    -- x = h_L
    · exact direct hL_valid hL_valid l4 k0
    · exact direct hL_valid eL_valid l1 (ks _ ke)
    · exact direct hL_valid fL_valid l2 (ks _ kf)
    · exact direct hL_valid hR_valid (lr hL (by simp) hR (by simp)).1 k0
    · exact direct hL_valid eR_valid (lr hL (by simp) eR (by simp)).1 k0
    · exact direct hL_valid fR_valid (lr hL (by simp) fR (by simp)).1 k0
    -- x = e_L
    · exact opp hL_valid eL_valid ghL geL l1 (ks _ ke) l9 tnil
    · exact direct eL_valid eL_valid l5 k0
    · exact direct eL_valid fL_valid l3 kh
    · exact direct eL_valid hR_valid (lr eL (by simp) hR (by simp)).1 k0
    · exact direct eL_valid eR_valid (lr eL (by simp) eR (by simp)).1 k0
    · exact direct eL_valid fR_valid (lr eL (by simp) fR (by simp)).1 k0
    -- x = f_L
    · exact opp hL_valid fL_valid ghL gfL l2 (ks _ kf) l10 tnil
    · exact opp eL_valid fL_valid geL gfL l3 kh l8 tvac
    · exact direct fL_valid fL_valid l6 k0
    · exact direct fL_valid hR_valid (lr fL (by simp) hR (by simp)).1 k0
    · exact direct fL_valid eR_valid (lr fL (by simp) eR (by simp)).1 k0
    · exact direct fL_valid fR_valid (lr fL (by simp) fR (by simp)).1 k0
    -- x = h_R
    · exact opp hL_valid hR_valid ghL ghR (lr hL (by simp) hR (by simp)).1 k0
        (lr hL (by simp) hR (by simp)).2 tnil
    · exact opp eL_valid hR_valid geL ghR (lr eL (by simp) hR (by simp)).1 k0
        (lr eL (by simp) hR (by simp)).2 tnil
    · exact opp fL_valid hR_valid gfL ghR (lr fL (by simp) hR (by simp)).1 k0
        (lr fL (by simp) hR (by simp)).2 tnil
    · exact direct hR_valid hR_valid r4 k0
    · exact direct hR_valid eR_valid r1 (ks _ kE)
    · exact direct hR_valid fR_valid r2 (ks _ kF)
    -- x = e_R
    · exact opp hL_valid eR_valid ghL geR (lr hL (by simp) eR (by simp)).1 k0
        (lr hL (by simp) eR (by simp)).2 tnil
    · exact opp eL_valid eR_valid geL geR (lr eL (by simp) eR (by simp)).1 k0
        (lr eL (by simp) eR (by simp)).2 tnil
    · exact opp fL_valid eR_valid gfL geR (lr fL (by simp) eR (by simp)).1 k0
        (lr fL (by simp) eR (by simp)).2 tnil
    · exact opp hR_valid eR_valid ghR geR r1 (ks _ kE) r9 tnil
    · exact direct eR_valid eR_valid r5 k0
    · exact direct eR_valid fR_valid r3 kH
    -- x = f_R
    · exact opp hL_valid fR_valid ghL gfR (lr hL (by simp) fR (by simp)).1 k0
        (lr hL (by simp) fR (by simp)).2 tnil
    · exact opp eL_valid fR_valid geL gfR (lr eL (by simp) fR (by simp)).1 k0
        (lr eL (by simp) fR (by simp)).2 tnil
    · exact opp fL_valid fR_valid gfL gfR (lr fL (by simp) fR (by simp)).1 k0
        (lr fL (by simp) fR (by simp)).2 tnil
    · exact opp hR_valid fR_valid ghR gfR r2 (ks _ kF) r10 tnil
    · exact opp eR_valid fR_valid geR gfR r3 kH r8 (tsv _)
    · exact direct fR_valid fR_valid r6 k0
  exact VertexAlgebra.mode_span_mem (A := (latA hB).toVertexAlgebra) 0 hgen

/-- `LowerCertificate` for the lattice closure data: nineteen fields proved, 7 from `LowerRest`. -/
theorem lowerCertificate_latD (L : LowerRest (latD hB S₃ hS₃)) :
    LowerCertificate (latD hB S₃ hS₃) where
  KK0 := KK0_latD hB S₃ hS₃
  KS₂0 := fun x hx a ha =>
    (LatticeVOA.S2Closed_S2span (LatticeVOA.flmInput_of_borcherds hB)).2.2.2.2.1 x hx a ha
  KS₂1 := LatticeVOA.KS21_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  TK := fun x hx => by
    rw [(latA hB).T_eq x]
    exact (LatticeVOA.S2Closed_S2span (LatticeVOA.flmInput_of_borcherds hB)).2.2.1 x hx
  KmK := fun x hx y hy =>
    (LatticeVOA.S2Closed_S2span (LatticeVOA.flmInput_of_borcherds hB)).2.2.2.1 x hx y hy
  ω_mem := (LatticeVOA.minimalGeneration_latticeD (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
    LatticeVOA.qpV LatticeVOA.q0V LatticeVOA.qmV LatticeVOA.triplet_grade_P4).2.1
  S₂S₂0 := L.S₂S₂0
  S₂S₂1 := L.S₂S₂1
  S₂S₂2 := L.S₂S₂2
  N₃_le_S₃ := L.N₃_le_S₃
  S₃_prov := L.S₃_prov
  P₄_prov := L.P₄_prov
  hL_q := LatticeVOA.hL_q_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  eL_q := LatticeVOA.eL_q_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  fL_q := LatticeVOA.fL_q_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  hR_qp := LatticeVOA.hR_qp_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  hR_q0 := LatticeVOA.hR_q0_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  hR_qm := LatticeVOA.hR_qm_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  eR_qp := LatticeVOA.eR_qp_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  eR_q0 := LatticeVOA.eR_q0_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  eR_qm := LatticeVOA.eR_qm_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  fR_qp := LatticeVOA.fR_qp_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  fR_q0 := LatticeVOA.fR_q0_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  fR_qm := LatticeVOA.fR_qm_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
  L1_P₄ := L.L1_P₄
  L2_P₄ := LatticeVOA.L2_P4_latticeDP (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃

/-- **`C_finiteClosure`** for the lattice model from the remaining certificate inputs:
`ω ∈ S₂`, `u ∈ S₂`, `S₂ ≤ U` and nineteen lower identities are proved. -/
theorem certFiniteClosure_latD (HL : LatticeClosureInputs hB S₃ hS₃) :
    certFiniteClosureProp (latD hB S₃ hS₃) LatticeVOA.uV := by
  obtain ⟨-, hω, hu, hmin⟩ := LatticeVOA.minimalGeneration_latticeD
    (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃ LatticeVOA.qpV LatticeVOA.q0V LatticeVOA.qmV
    LatticeVOA.triplet_grade_P4
  unfold certFiniteClosureProp
  exact ⟨lowerCertificate_latD hB S₃ hS₃ HL.lower, HL.gates, HL.nilE, HL.nilF, hω, hu, hmin⟩

/-- **`C_dimensions`** for the lattice model: a theorem (`certDimensions_latticeD`). -/
theorem certDimensions_latD (R : Nodes) :
    (concreteNodes R (latD hB S₃ hS₃) LatticeVOA.uV).certDimensions :=
  LatticeVOA.certDimensions_latticeD (LatticeVOA.flmInput_of_borcherds hB) S₃ hS₃
    LatticeVOA.qpV LatticeVOA.q0V LatticeVOA.qmV LatticeVOA.triplet_grade_P4 R

open LatticeVOA in
/-- **`θ_g U ⊆ U`** (line 2604): from the mode compatibility `hθ`, `θ_g 𝟏 = 𝟏`, `θ_g ω = ω`,
`θ_g S₂ = S₂` and `S₂ ≤ U`.  The preimage of `U` under `θ_g` is a vertex subalgebra (`θ_g` is
additive, antilinear and mode-compatible) containing the generators: `ω`; `u` (`θ_g u ∈ S₂`);
each current `k`, since `k = ½ L(1) T k`, `T k ∈ S₂` and so
`θ_g k = ½ L(1) θ_g(T k) ∈ ω_(2) S₂ ⊆ U`. -/
theorem pctV_mem_U_latD (hθ : PCTModeCompatible) :
    ∀ x ∈ (latD hB S₃ hS₃).U uV, pctV x ∈ (latD hB S₃ hS₃).U uV := by
  have hsub := (latA hB).toVertexAlgebra.generated_isSubalgebra ((latD hB S₃ hS₃).gens uV)
  have hS2U : ∀ s ∈ S2span, s ∈ (latD hB S₃ hS₃).U uV := fun s hs =>
    S2span_le_U (flmInput_of_borcherds hB) S₃ hS₃ qpV q0V qmV triplet_grade_P4 hs
  have hωU : (latA hB).ω ∈ (latD hB S₃ hS₃).U uV :=
    (latA hB).toVertexAlgebra.subset_generated _ (Or.inr (Or.inl rfl))
  let W : Submodule ℂ V :=
    { carrier := {x | pctV x ∈ (latD hB S₃ hS₃).U uV}
      add_mem' := fun {a b} ha hb => by
        change pctV (a + b) ∈ (latD hB S₃ hS₃).U uV
        rw [map_add]
        exact Submodule.add_mem _ ha hb
      zero_mem' := by
        change pctV 0 ∈ (latD hB S₃ hS₃).U uV
        rw [map_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun c x hx => by
        change pctV (c • x) ∈ (latD hB S₃ hS₃).U uV
        rw [pctV_smul]
        exact Submodule.smul_mem _ _ hx }
  have hW : (latA hB).toVertexAlgebra.IsSubalgebra W := by
    refine ⟨?_, fun n a ha b hb => ?_⟩
    · change pctV vacV ∈ (latD hB S₃ hS₃).U uV
      rw [pctV_vacV]
      exact hsub.1
    · change pctV (modeC n a b) ∈ (latD hB S₃ hS₃).U uV
      rw [hθ]
      exact hsub.2 n _ ha _ hb
  have hgens : (latD hB S₃ hS₃).gens uV ⊆ W := by
    intro x hx
    rcases hx with hk | hx
    · -- a current
      have hk1 : x ∈ (latA hB).grade 1 := (latD hB S₃ hS₃).currents_grade x hk
      have hkK : x ∈ Kspan := Submodule.subset_span hk
      have hT : (latA hB).T x ∈ S2span := by
        rw [(latA hB).T_eq x]
        exact (S2Closed_S2span (flmInput_of_borcherds hB)).2.2.1 x hkK
      have hθT : pctV ((latA hB).T x) ∈ S2span := pctV_mem_S2span hT
      change pctV x ∈ (latD hB S₃ hS₃).U uV
      rw [wt_one_eq_L1_T (latA hB) hk1, pctV_smul]
      have e : pctV ((latA hB).mode 2 (latA hB).ω ((latA hB).T x)) =
          (latA hB).mode 2 (latA hB).ω (pctV ((latA hB).T x)) := by
        show pctV (modeC 2 omegaV _) = modeC 2 omegaV _
        rw [hθ, pctV_omegaV]
      rw [e]
      exact Submodule.smul_mem _ _ (hsub.2 2 _ hωU _ (hS2U _ hθT))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · change pctV omegaV ∈ (latD hB S₃ hS₃).U uV
        rw [pctV_omegaV]
        exact hωU
      · change pctV uV ∈ (latD hB S₃ hS₃).U uV
        exact hS2U _ pctV_uV_mem
  exact fun x hx => (latA hB).toVertexAlgebra.generated_le hW hgens hx

/-- **`θ_g U ⊆ U`**, unconditionally (`LatticeVOA.pctModeCompatible`). -/
theorem pctV_mem_U_lattice :
    ∀ x ∈ (latD hB S₃ hS₃).U LatticeVOA.uV, LatticeVOA.pctV x ∈ (latD hB S₃ hS₃).U LatticeVOA.uV :=
  pctV_mem_U_latD hB S₃ hS₃ LatticeVOA.pctModeCompatible

/-- **`C_pct`** for the lattice model: `θ_g` is mode-compatible (`pctModeCompatible`),
`θ_g S₂ = S₂` is `certPCT_latticeD`, `θ_g U = U` is `pctV_mem_U_lattice` with `θ_g² = 1`. -/
theorem certPCT_latD : PCTCert (latD hB S₃ hS₃) LatticeVOA.uV :=
  ⟨LatticeVOA.pctModeCompatible, LatticeVOA.certPCT_latticeD (LatticeVOA.flmInput_of_borcherds hB)
    S₃ hS₃ LatticeVOA.qpV LatticeVOA.q0V LatticeVOA.qmV LatticeVOA.triplet_grade_P4,
    fun x => ⟨fun h => LatticeVOA.pctV_pctV x ▸ pctV_mem_U_lattice hB S₃ hS₃ _ h,
      pctV_mem_U_lattice hB S₃ hS₃ x⟩⟩

end

/-! ### The proof map for the lattice VOA -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {kp : Type*} [Field kp] {W W' : Type*} [AddCommGroup W] [Module kp W] [AddCommGroup W']
  [Module kp W']
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Sec : Type*} [Fintype Sec]
variable {σ : Type*}
variable {Simp : Type*} [Fintype Simp] [DecidableEq Simp]
variable {ιn κn : Type*} [Fintype ιn] [DecidableEq ιn] [Fintype κn]
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {τ₁ τ₂ : Type*} [Fintype τ₁] [Fintype τ₂]

/-- **The proof map for the actual lattice VOA.**  `concrete_proof_map` at `A = latA hB`,
`D = latD hB S₃ hS₃`, `u = uV`, with the node `certPCT` given its meaning (`pctNodes`): from
`FLMBorcherds`, the remaining finite-closure certificates `HL`, the seventeen other remaining
fields `RL`, and the inputs of the concrete arrows, the conclusions of `concrete_proof_map`
for the lattice VOA.  `C_dimensions`, `C_pct` and the minimal-generation part of
`C_finiteClosure` (with nineteen lower identities) are theorems here. -/
theorem lattice_proof_map (hB : LatticeVOA.FLMBorcherds) (S₃ : Submodule ℂ LatticeVOA.V)
    (hS₃ : S₃ ≤ LatticeVOA.gradeC 3) (HL : LatticeClosureInputs hB S₃ hS₃)
    [CharZero kp] [Fintype σ] [DecidableEq σ] (R : Nodes)
    (C : CharacterData) (SD : SimpleData Simp) (𝒞 : Type*) [Category 𝒞] [MonoidalCategory 𝒞]
    [Preadditive 𝒞] [Linear ℂ 𝒞] [HasBinaryBiproducts 𝒞] [HasKernels 𝒞]
    [∀ X Y : 𝒞, FiniteDimensional ℂ (X ⟶ Y)] (Bb : BranchBData (latA hB) σ Simp)
    (Hd : BranchHData Simp) (Sg : SignData (latA hB)) (B : BoundaryData ι κ)
    (Bn : BoundaryData ιn κn)
    (Cr : Type*) [Category Cr] [MonoidalCategory Cr] [BraidedCategory Cr] [Preadditive Cr]
    [HasFiniteBiproducts Cr] [HasCoequalizers Cr]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive Cr]
    (𝕜 : Type) [Field 𝕜] [Linear 𝕜 Cr] [MonoidalLinear 𝕜 Cr] (Ah : Mon Cr) [IsCommMonObj Ah.X] (Sv : ZMod 3 × ZMod 3 → Cr) (P : PF13Data kp W W')
    (St : StressData E H)
    (xT yT : Simp → ℕ → ℕ) (recon : Sec → Simp) (Unitarizable : Simp → Prop)
    (RL : LatticeRemainingInputs
      (allConcreteNodes (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV) (latD hB S₃ hS₃) LatticeVOA.uV C SD 𝒞 Bb
        Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable))
    (HB : BoundaryInputs (coreNodes (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV) (latD hB S₃ hS₃) LatticeVOA.uV
      C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B 𝒞)
    (HC : CharacterInputs (regNodes (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV) SD St 𝒞) (latD hB S₃ hS₃)
      LatticeVOA.uV C)
    (LI : SimpleLabels R.modularData SD C)
    (HP : PF13Inputs P) (HBr : BranchBInputs SD (latD hB S₃ hS₃) LatticeVOA.uV Bb R.stronglyRational)
    (HS : SignInputs SD (latD hB S₃ hS₃) LatticeVOA.uV Bb Sg)
    (hadj : R.lagrangianCenter → Fintype.card ι = ∑ l, Hd.mult l ^ 2)
    (hfp : R.stronglyRational → B.dX = 1 → Sg.XInvertible) (HV : VacuumInputs St SD R.initialGrades)
    (HR : RankFourInputs B (latD hB S₃ hS₃) LatticeVOA.uV R.lagrangianCenter R.stronglyRational
      R.initialGrades (VacuumNode St SD) (BranchB SD (latD hB S₃ hS₃) LatticeVOA.uV Bb))
    (S₁ : SectorData (latA hB) M₁ τ₁ Simp) (S₂ : SectorData (latA hB) M₂ τ₂ Simp)
    (I₁ : SectorInputs SD (latD hB S₃ hS₃) LatticeVOA.uV S₁ R.certStructural R.stronglyRational)
    (I₂ : SectorInputs SD (latD hB S₃ hS₃) LatticeVOA.uV S₂ R.certStructural R.stronglyRational)
    (IH : BranchHInputs SD Bb Hd S₁ S₂)
    (hunit : VacuumNode St SD → Projective (𝟙_ 𝒞))
    (hEP : FiniteDimensional ℂ (H ⧸ C2 St.U) → R.initialGrades → Projective (𝟙_ 𝒞) →
      ∀ X : 𝒞, Nonempty (HasRightDual X))
    (HN : NetInputs (latD hB S₃ hS₃) LatticeVOA.uV Sg Bn Sec R.netCompletelyRational
      R.certDiscriminant (∃ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m) (UntwistedNode 𝕜 Cr Ah Sv))
    [∀ X Y : Cr, FiniteDimensional 𝕜 (X ⟶ Y)] (HU : UntwistedInputs 𝕜 Cr Ah Sv R.certDiscriminant)
    (hν : UntwistedNode 𝕜 Cr Ah Sv → R.certDiscriminant → R.lagrangianCenter → R.stronglyRational →
      (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
      B.ν₃ = 1)
    {G : Fin 4 → Type*} [∀ i, MeasurableSpace (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, G i → E) (hf : ∀ i, Integrable (f i) (μ i))
    (hK : ∀ i, IsCompact (St.K i)) (hfK : ∀ i g, f i g ∈ St.K i)
    (havg : ∀ i, St.avg i = ∫ g, f i g ∂(μ i))
    (hfac : (pf13Nodes (boundaryNodes (coreNodes (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV) (latD hB S₃ hS₃)
      LatticeVOA.uV C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P).pf13Factor →
      ∀ i, ∃ Dc : ℝ, ∀ z ∈ St.K i, FactorEnergy St Dc z)
    (hnonneg : (pf13Nodes (boundaryNodes (coreNodes (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV)
      (latD hB S₃ hS₃) LatticeVOA.uV C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P).pf13Factor →
      ∀ i, St.factorNonneg i)
    [∀ n, FiniteDimensional ℂ (St.U.grade n)]
    (HT : TopBoundInputs (regularityNodes (pf13Nodes (boundaryNodes
      (coreNodes (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV) (latD hB S₃ hS₃) LatticeVOA.uV C SD St 𝒞 Bb Hd Sg
        B Bn Cr 𝕜 Ah Sv) B) P) St) (topDataOf SD xT yT)) :
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1) ∧
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1 ∧ B.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 B ∧
      SixResidualTwists B) ∧
    (C.F = C.Ξ₀ ∧ ∀ l n, (C.a l n : ℂ) = C.e₀ l n) ∧
    (∀ l, C.hw l = lowestWeight l ∧ C.td l = topDim l) ∧
    (∀ s, 0 ≤ SD.hw s ∧ SD.hw s ≤ 17 / 10) ∧
    VacuumNode St SD ∧ RigidSemisimple 𝒞 ∧
    BranchB SD (latD hB S₃ hS₃) LatticeVOA.uV Bb ∧ HBranching SD Hd ∧
    (NetHI Bn ∧ Fintype.card Sec = 12) ∧
    (UntwistedNode 𝕜 Cr Ah Sv ∧ B.ν₃ = 1) ∧
    ((¬ Sg.XInvertible ∧ ∀ g, ¬ FixesExactlyU (latD hB S₃ hS₃) LatticeVOA.uV Sg g) ∧
      B.dX ≠ 1) ∧
    (∀ l, Unitarizable l) ∧
    ((latD hB S₃ hS₃).U LatticeVOA.uV ⊓ (latA hB).grade 1 = (latD hB S₃ hS₃).K ∧
      Module.finrank ℂ (latD hB S₃ hS₃).K = 6 ∧ IsSl2SumSpan (latA hB) (latD hB S₃ hS₃).K) ∧
    (latD hB S₃ hS₃).U LatticeVOA.uV ≠ ⊤ ∧
    FiniteDimensional ℂ (H ⧸ C2 St.U) ∧
    (∃ φ : W ≃ₗ[kp] W', φ P.L = P.L' ∧ φ P.a = P.a' ∧ φ P.b = P.b' ∧ φ P.d = P.d' ∧
      φ P.A.vac = P.A'.vac ∧ ∀ (n : ℤ) (x y : W), φ (P.A.mode n x y) = P.A'.mode n (φ x) (φ y)) :=
  concrete_proof_map (pctNodes R (latD hB S₃ hS₃) LatticeVOA.uV) (latD hB S₃ hS₃) LatticeVOA.uV C SD 𝒞 Bb Hd
    Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable
    { C_finiteClosure := certFiniteClosure_latD hB S₃ hS₃ HL
      C_dimensions := certDimensions_latD hB S₃ hS₃ R
      C_pct := certPCT_latD hB S₃ hS₃
      C_structural := RL.C_structural
      C_discriminant := RL.C_discriminant
      E_cklw529 := RL.E_cklw529
      L_rational := RL.L_rational
      E_dmno := RL.E_dmno
      E_gsy := RL.E_gsy
      E_netCR := RL.E_netCR
      L_reconstruction := RL.L_reconstruction
      L_annulus := RL.L_annulus
      E_tener := RL.E_tener
      L_boundaryUnitary := RL.L_boundaryUnitary
      E_izumi := RL.E_izumi
      E_moritaCenter := RL.E_moritaCenter
      E_netCenter := RL.E_netCenter
      E_netExtension := RL.E_netExtension
      E_diagonal := RL.E_diagonal
      E_e8Extension := RL.E_e8Extension }
    HB HC LI HP HBr HS hadj hfp HV HR S₁ S₂ I₁ I₂ IH hunit hEP HN HU hν μ f hf hK hfK havg hfac
    hnonneg HT

#print axioms KK0_latD
#print axioms lowerCertificate_latD
#print axioms certFiniteClosure_latD
#print axioms certDimensions_latD
#print axioms pctV_mem_U_latD
#print axioms pctV_mem_U_lattice
#print axioms certPCT_latD
#print axioms lattice_proof_map

end HaagerupIzumi.C8.ProofMap
