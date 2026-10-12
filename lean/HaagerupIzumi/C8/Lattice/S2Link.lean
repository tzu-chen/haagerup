module

public import HaagerupIzumi.C8.Lattice.S2MinGen

@[expose] public section

/-!
# The semantic link: minimal generation, `S₂`, and properness for the lattice VOA given FLM

Work item W2 (`C8/ROADMAP.md`), options (c) and (a).  Everything is stated for the lattice
vertex operator algebra `latticeVOA hF` of `Lattice/VOA.lean`, whose only hypothesis is
`hF : FLMInput` (FLM: the Borcherds identity and the `L(0)`, `L(-1)` properties of `ω` for the
concrete modes).

**Kernel replay of the minimal-generation record** (`hi_cft_20260923_c8_minimal_generators.json`,
manuscript lines 2047–2055; data `S2Data.lean`, relations `S2Rel*.lean`, pivots `S2Echelon.lean`):

* `S2span`: the span of the 120 echelon basis vectors `r_k` of the record; `S2span_grade`:
  it lies in `B₂`.
* `finrank_S2span`: `dim S₂ = 120` (the `r_k` are triangular at their pivots).
* `omegaV_mem_S2span`, `uV_mem_S2span`: `ω, u ∈ S₂` (relations 42 and 43).
* `S2span_le_closureSpace`: `S₂` lies in the closure of `ω`, `u`, `T K`, `K₋₁K` under the
  current zero modes and `u_(1)` (`ClosureData.closureSpace`), because every `r_k` is created
  by a kernel-checked relation from earlier vectors (`s2mem_k`); hence
  `S2span_le_U : S₂ ≤ U = ⟨K, ω, u⟩` (`S₂_le_U_of_closure`), the hypothesis `hmin` of
  `prop_mainproper`.

**The proof-map nodes** for the closure data `latticeD` (currents of `Lattice/Data.lean`,
`S₂ = S2span`, `u = uV`; `S₃` and the triplet `P₄` remain parameters, since their data are not
exported yet):

* `certDimensions_latticeD`: the node `certDimensions` (from `Lattice/VOA.lean`).
* `certFiniteClosure_latticeD_tail`: the three last conjuncts of `certFiniteClosure`
  (`ω ∈ S₂`, `u ∈ S₂`, `S₂ ≤ U`) are theorems; the remaining certificate inputs are
  `LowerCertificate`, `Gate4Certificate`, `Gate5Certificate` and the two nilpotence
  statements, now *about this concrete algebra*.
* `proper_latticeD`: properness `U ≠ B` for the lattice VOA from `FLMInput` and exactly those
  remaining certificate inputs (`prop_mainproper_proper`).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

/-! ## The space `S₂` -/

/-- The `k`-th basis vector of `S₂` in `V`. -/
noncomputable def s2vec (k : Fin 120) : V := toV4 (s2basis.getD k.val Vec4.zero)

/-- The weight-two space `S₂` of the minimal-generation record. -/
noncomputable def S2span : Submodule ℂ V := Submodule.span ℂ (Set.range s2vec)

theorem s2basis_getD_mem (k : Fin 120) : s2basis.getD k.val Vec4.zero ∈ s2basis := by
  have hk : k.val < s2basis.length := by
    rw [s2basis_length]
    exact k.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

theorem s2vec_allValid (k : Fin 120) : (s2basis.getD k.val Vec4.zero).AllStates Valid :=
  (s2basis_states _ (s2basis_getD_mem k)).mono fun _ h => h.1

theorem S2span_grade : S2span ≤ gradeC 2 := by
  rw [S2span, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact toV4_mem_gradeC _ (s2basis_states _ (s2basis_getD_mem k))

theorem s2basis_mem_span : ∀ x ∈ s2basis, toV4 x ∈ S2span := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
  have hk' : k < 120 := by
    rw [← s2basis_length]
    exact hk
  apply Submodule.subset_span
  refine ⟨⟨k, hk'⟩, ?_⟩
  simp only [s2vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

theorem omegaV_mem_S2span : omegaV ∈ S2span := by
  have h := s2omega_rel_mem s2basis_mem_span
  rwa [toV4_ofVec] at h

theorem uV_mem_S2span : uV ∈ S2span := s2u_rel_mem s2basis_mem_span

/-- The pivot of `r_j` as a canonical monomial. -/
noncomputable def s2pivV (j : Fin 120) : ValidState :=
  ⟨s2piv.getD j.val vacState, s2piv_valid j.val j.2⟩

theorem s2vec_linearIndependent : LinearIndependent ℂ s2vec := by
  refine linearIndependent_of_triangular s2vec (fun j => Finsupp.lapply (s2pivV j)) ?_ ?_
  · intro k
    have h := s2piv_diag k.val k.2
    simp only [Finsupp.lapply_apply, s2vec, toV4_apply _ (s2vec_allValid k), s2pivV, h,
      QA.toC_one]
    exact one_ne_zero
  · intro j k hjk
    have h := s2piv_low k.val k.2 j.val hjk
    simp only [Finsupp.lapply_apply, s2vec, toV4_apply _ (s2vec_allValid k), s2pivV, h,
      QA.toC_zero]

/-- **`dim S₂ = 120`.** -/
theorem finrank_S2span : Module.finrank ℂ S2span = 120 := by
  rw [S2span, finrank_span_eq_card s2vec_linearIndependent, Fintype.card_fin]

/-- **Minimal generation**: `S₂` lies in every subspace satisfying the closure conditions. -/
theorem S2span_le {W : Submodule ℂ V} (hW : S2Closed W) : S2span ≤ W := by
  rw [S2span, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact s2basis_mem hW _ (s2basis_getD_mem k)

/-! ## The closure data of the lattice VOA -/

/-- The closure data of the properness argument for the lattice VOA, with `S₂ = S2span`;
`S₃` and the triplet are parameters. -/
noncomputable def latticeD (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3)
    (qp q0 qm : V) (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4) :
    ClosureData (latticeVOA hF) :=
  latticeClosureData hF S2span S₃ S2span_grade hS₃ qp q0 qm hq

section
variable (hF : FLMInput) (S₃ : Submodule ℂ V) (hS₃ : S₃ ≤ gradeC 3) (qp q0 qm : V)
  (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4)

theorem S2span_le_closureSpace : S2span ≤ (latticeD hF S₃ hS₃ qp q0 qm hq).closureSpace uV :=
  fun _ hx => mem_closureSpace_of hF _ _ _ _ _ _ _ _ fun _ hW => S2span_le hW hx

/-- **`hmin`**: `S₂ ≤ U = ⟨K, ω, u⟩` for the lattice VOA. -/
theorem S2span_le_U : (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ ≤ (latticeD hF S₃ hS₃ qp q0 qm hq).U uV :=
  S₂_le_U_of_closure _ uV (S2span_le_closureSpace hF S₃ hS₃ qp q0 qm hq)

/-- The minimal-generation record for the lattice VOA: `dim S₂ = 120`, `ω, u ∈ S₂`, `S₂ ≤ U`. -/
theorem minimalGeneration_latticeD :
    Module.finrank ℂ (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ = 120 ∧
      (latticeVOA hF).ω ∈ (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ ∧
      uV ∈ (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ ∧
      (latticeD hF S₃ hS₃ qp q0 qm hq).S₂ ≤ (latticeD hF S₃ hS₃ qp q0 qm hq).U uV :=
  ⟨finrank_S2span, omegaV_mem_S2span, uV_mem_S2span, S2span_le_U hF S₃ hS₃ qp q0 qm hq⟩

/-- **The `certDimensions` node** of `concreteNodes` for the lattice closure data. -/
theorem certDimensions_latticeD (R : Nodes) :
    (concreteNodes R (latticeD hF S₃ hS₃ qp q0 qm hq) uV).certDimensions :=
  certDimensions_lattice hF R S2span S₃ S2span_grade hS₃ qp q0 qm hq uV

/-- The last three conjuncts of the node `certFiniteClosure` are theorems; the node reduces to
the remaining certificate inputs, stated about the concrete algebra. -/
theorem certFiniteClosure_latticeD_iff (R : Nodes) :
    (concreteNodes R (latticeD hF S₃ hS₃ qp q0 qm hq) uV).certFiniteClosure ↔
      LowerCertificate (latticeD hF S₃ hS₃ qp q0 qm hq) ∧
      (∃ G : Gate4Certificate (latticeD hF S₃ hS₃ qp q0 qm hq),
        Nonempty (Gate5Certificate (latticeD hF S₃ hS₃ qp q0 qm hq) G)) ∧
      (∀ w : List Bool, w.length = 25 → ∀ v ∈ S₃,
        CFT.raisingWord (modeC 0 (toV eL)) (modeC 0 (toV eR)) w v = 0) ∧
      (∀ w : List Bool, w.length = 25 → ∀ v ∈ S₃,
        CFT.raisingWord (modeC 0 (toV fL)) (modeC 0 (toV fR)) w v = 0) := by
  dsimp only [concreteNodes, certFiniteClosureProp]
  constructor
  · rintro ⟨L, G, hE, hF', -, -, -⟩
    exact ⟨L, G, hE, hF'⟩
  · rintro ⟨L, G, hE, hF'⟩
    exact ⟨L, G, hE, hF', omegaV_mem_S2span, uV_mem_S2span, S2span_le_U hF S₃ hS₃ qp q0 qm hq⟩

/-- **Properness of `U = ⟨K, ω, u⟩` in the lattice VOA** from `FLMInput` and the remaining
certificate inputs (lower identities, Gates 4 and 5, nilpotence), all stated about the concrete
algebra; `dim K = 6`, `dim B₁ = 86`, `ω, u ∈ S₂` and `S₂ ≤ U` are proved. -/
theorem proper_latticeD (L : LowerCertificate (latticeD hF S₃ hS₃ qp q0 qm hq))
    (G : Gate4Certificate (latticeD hF S₃ hS₃ qp q0 qm hq))
    (G5 : Gate5Certificate (latticeD hF S₃ hS₃ qp q0 qm hq) G)
    (hnilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ S₃,
      CFT.raisingWord (modeC 0 (toV eL)) (modeC 0 (toV eR)) w v = 0)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ S₃,
      CFT.raisingWord (modeC 0 (toV fL)) (modeC 0 (toV fR)) w v = 0) :
    (latticeD hF S₃ hS₃ qp q0 qm hq).U uV ≠ ⊤ :=
  prop_mainproper_proper (latticeD hF S₃ hS₃ qp q0 qm hq) L G G5 hnilE hnilF uV
    omegaV_mem_S2span uV_mem_S2span (S2span_le_U hF S₃ hS₃ qp q0 qm hq) finrank_span_currentV
    finrank_gradeC_one

end

#print axioms finrank_S2span
#print axioms S2span_le_U
#print axioms minimalGeneration_latticeD
#print axioms certDimensions_latticeD
#print axioms certFiniteClosure_latticeD_iff
#print axioms proper_latticeD

end LatticeVOA
end HaagerupIzumi.C8
