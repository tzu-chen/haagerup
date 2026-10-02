module

public import HaagerupIzumi.C8.Lattice.ModelVacuum
public import HaagerupIzumi.C8.Lattice.Dimensions
public import HaagerupIzumi.C8.Lattice.Relations
public import HaagerupIzumi.C8.VertexAlgebra.Borcherds
public import HaagerupIzumi.C8.ProofMapProperness

@[expose] public section

/-!
# The lattice vertex operator algebra `B = V_{E₆ ⊕ A₂}` on the Fock model, given FLM

Work item W2, option (c) (`C8/ROADMAP.md`): the semantic link between the kernel computations
and the abstract interface of `VertexAlgebra/Basic.lean`.

**The FLM input.**  `FLMInput` is the single named hypothesis: the Borcherds identity for the
concrete modes `modeC` of the Fock model `V` (`Lattice/Model.lean`), and the two properties of the
conformal vector `ω` recorded by `VertexOperatorAlgebra` (`L(0) = ω_(1)` is the grading,
`L(-1) = ω_(0)` is `T`).  This is the content of Frenkel–Lepowsky–Meurman, *Vertex operator
algebras and the Monster*, Theorem 8.10.2 (with §8.7 for the conformal vector; also Kac,
*Vertex algebras for beginners*, §5.5), for the even lattice `L = E₆ ⊕ A₂`, the cocycle
`Lattice.epsilon` and the modes of `Lattice/Modes.lean` (cross-checked against the certificate
engine on 822 samples, `Lattice/Samples*.lean`).

Everything else is **proved** from the model: the direct-sum grading of CFT type
(`gradeC_internal`, `gradeC_zero`), the weight rule and truncation (`modeC_mem_gradeC`,
`modeC_eq_zero_of_le`), the vacuum axioms (`modeC_vac`, `modeC_vac_nonneg`,
`modeC_vac_neg_one`), and `ω ∈ V₂`.  `latticeBVA` is the resulting
`BorcherdsVertexAlgebra ℂ V` and `latticeVOA` the `VertexOperatorAlgebra` (via
`BorcherdsVertexAlgebra.toVertexAlgebra`).

The model is `V = ValidState →₀ ℂ`, the span of the canonical monomials (nondecreasing code
lists): the rational model `Fock` of `Lattice/Semantic.lean` is free on all code lists, on which
creation fails for unsorted lists; here every output state is canonicalized (`canon`, sorting
commuting oscillators), so no sortedness of the outputs of `basisMode` is needed.

**The proof-map nodes.**  `latticeClosureData` is the `ClosureData` of the properness argument
for this algebra, with the six currents of `eq:leftcurrents`, `eq:rightcurrents`
(`Lattice/Data.lean`) and the spaces `S₂`, `S₃`, `P₄` as parameters (with their grades).
`certDimensions_lattice`: the node `certDimensions` of `ProofMapProperness.concreteNodes` —
`dim K = 6`, `dim B₁ = 86` and `K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂` (`IsSl2SumSpan`, from the kernel-checked brackets
of `Lattice/Relations.lean`) — holds for it, given only `FLMInput` (which is needed only to
have the algebra).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

open ProofMap

/-! ## Vectors of the model -/

theorem toV_mem_gradeC {d : ℕ} :
    ∀ v : Vec, (∀ p ∈ v, Valid p.1 ∧ grade p.1 = d) → toV v ∈ gradeC d
  | [], _ => by simp
  | (t, c) :: v, h => by
    have ht := h (t, c) List.mem_cons_self
    rw [toV_cons_mk, canon_of_valid ht.1]
    exact Submodule.add_mem _ (single_mem_gradeC (s := ⟨t, ht.1⟩) ht.2 (c : ℂ))
      (toV_mem_gradeC v fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem toV4_mem_gradeC {d : ℕ} (x : Vec4) (h : x.AllStates fun s => Valid s ∧ grade s = d) :
    toV4 x ∈ gradeC d := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have m0 : toV x.c0 ∈ gradeC d := toV_mem_gradeC _ h0
  have m1 : sC • toV x.c1 ∈ gradeC d := Submodule.smul_mem (gradeC d) sC (toV_mem_gradeC _ h1)
  have m2 : tC • toV x.c2 ∈ gradeC d := Submodule.smul_mem (gradeC d) tC (toV_mem_gradeC _ h2)
  have m3 : (sC * tC) • toV x.c3 ∈ gradeC d :=
    Submodule.smul_mem (gradeC d) (sC * tC) (toV_mem_gradeC _ h3)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ m0 m1) m2) m3

theorem toV_apply_of_valid :
    ∀ (v : Vec), (∀ p ∈ v, Valid p.1) → ∀ s : ValidState, toV v s = (coeffOf v s.1 : ℂ)
  | [], _, s => by simp [coeffOf]
  | (t, c) :: v, h, s => by
    have ht := h (t, c) List.mem_cons_self
    rw [toV_cons_mk, canon_of_valid ht, Finsupp.add_apply,
      toV_apply_of_valid v (fun p hp => h p (List.mem_cons_of_mem _ hp)) s, Finsupp.single_apply]
    by_cases hts : t = s.1
    · have hs : (⟨t, ht⟩ : ValidState) = s := Subtype.ext hts
      simp [coeffOf, hts]
    · have hs : (⟨t, ht⟩ : ValidState) ≠ s := fun e => hts (congrArg Subtype.val e)
      simp [coeffOf, hs, hts]

/-- A kernel-checked list identity `mode a m b = c` (canonical states) is the identity
`a_(m) b = c` in `V`. -/
theorem modeC_toV_of_mode {a b c : Vec} {m : ℤ} (ha : ∀ p ∈ a, Valid p.1)
    (hb : ∀ p ∈ b, Valid p.1) (h : mode a m b = c) : modeC m (toV a) (toV b) = toV c := by
  rw [← toV_mode m a b ha hb, h]

/-- The vacuum and the conformal vector of the model. -/
noncomputable def omegaV : V := toV omega

theorem omega_states : ∀ p ∈ omega, Valid p.1 ∧ grade p.1 = 2 := by
  decide +kernel

theorem omegaV_mem : omegaV ∈ gradeC 2 := toV_mem_gradeC _ omega_states

/-! ## The FLM input and the vertex operator algebra -/

/-- **The FLM input** (Frenkel–Lepowsky–Meurman, Theorem 8.10.2 and §8.7): the modes of the Fock
model satisfy the Borcherds identity on homogeneous vectors (stated with exactly the summation
range of `BorcherdsVertexAlgebra.borcherds`), `L(0) = ω_(1)` acts on `V_d` by `d`, and
`L(-1) = ω_(0)` is the translation `a ↦ a_(-2) 𝟏`. -/
structure FLMInput : Prop where
  borcherds : ∀ {i j l : ℕ} {a b c : V}, a ∈ gradeC i → b ∈ gradeC j → c ∈ gradeC l →
    ∀ p q r : ℤ,
    ∑ t ∈ Finset.range (i + j + l + p.natAbs + q.natAbs + r.natAbs + 1),
        zbinom ℂ p t • modeC (p + q - t) (modeC (r + t) a b) c =
      ∑ t ∈ Finset.range (i + j + l + p.natAbs + q.natAbs + r.natAbs + 1),
        ((-1 : ℂ) ^ t * zbinom ℂ r t) •
          (modeC (p + r - t) a (modeC (q + t) b c) -
            (-1 : ℂ) ^ r • modeC (q + r - t) b (modeC (p + t) a c))
  L0 : ∀ {d : ℕ} {a : V}, a ∈ gradeC d → modeC 1 omegaV a = (d : ℂ) • a
  Lm1 : ∀ a : V, modeC 0 omegaV a = modeC (-2) a vacV

/-- The Borcherds vertex algebra of the Fock model: every field except `borcherds` is proved. -/
noncomputable def latticeBVA (hF : FLMInput) : BorcherdsVertexAlgebra ℂ V where
  mode := modeC
  vac := vacV
  grade := gradeC
  grade_internal := gradeC_internal
  grade_zero := gradeC_zero
  mode_grade := modeC_mem_gradeC
  mode_trunc := modeC_eq_zero_of_le
  vac_mode := modeC_vac
  mode_vac_nonneg := modeC_vac_nonneg
  mode_vac_neg_one := modeC_vac_neg_one
  borcherds := hF.borcherds

/-- **The lattice vertex operator algebra `B = V_{E₆ ⊕ A₂}`** on the Fock model. -/
noncomputable def latticeVOA (hF : FLMInput) : VertexOperatorAlgebra ℂ V where
  toVertexAlgebra := (latticeBVA hF).toVertexAlgebra
  ω := omegaV
  ω_mem := omegaV_mem
  L0 := hF.L0
  Lm1 := hF.Lm1

theorem latticeVOA_mode (hF : FLMInput) : (latticeVOA hF).mode = modeC := rfl

theorem latticeVOA_grade (hF : FLMInput) : (latticeVOA hF).grade = gradeC := rfl

theorem latticeVOA_vac (hF : FLMInput) : (latticeVOA hF).vac = vacV := rfl

theorem latticeVOA_ω (hF : FLMInput) : (latticeVOA hF).ω = omegaV := rfl

theorem latticeVOA_T (hF : FLMInput) (a : V) : (latticeVOA hF).T a = modeC (-2) a vacV := rfl

/-! ## The current space -/

theorem hL_valid : ∀ p ∈ hL, Valid p.1 := fun p hp => (currents_basisStates 0 p hp).1
theorem eL_valid : ∀ p ∈ eL, Valid p.1 := fun p hp => (currents_basisStates 1 p hp).1
theorem fL_valid : ∀ p ∈ fL, Valid p.1 := fun p hp => (currents_basisStates 2 p hp).1
theorem hR_valid : ∀ p ∈ hR, Valid p.1 := fun p hp => (currents_basisStates 3 p hp).1
theorem eR_valid : ∀ p ∈ eR, Valid p.1 := fun p hp => (currents_basisStates 4 p hp).1
theorem fR_valid : ∀ p ∈ fR, Valid p.1 := fun p hp => (currents_basisStates 5 p hp).1

/-- The six currents in `V`. -/
noncomputable def currentV (i : Fin 6) : V := toV (currentVec i)

theorem range_currentV : Set.range currentV =
    {toV hL, toV eL, toV fL, toV hR, toV eR, toV fR} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

theorem currentV_linearIndependent : LinearIndependent ℂ currentV := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have ev : ∀ (s : State) (hs : Valid s), g 0 * (coeffOf hL s : ℂ) + g 1 * (coeffOf eL s : ℂ) +
      g 2 * (coeffOf fL s : ℂ) + g 3 * (coeffOf hR s : ℂ) + g 4 * (coeffOf eR s : ℂ) +
      g 5 * (coeffOf fR s : ℂ) = 0 := by
    intro s hs
    have h := congrArg (fun F : V => F ⟨s, hs⟩) hg
    simpa [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, currentV, Fin.sum_univ_six,
      currentVec, toV_apply_of_valid hL hL_valid, toV_apply_of_valid eL eL_valid,
      toV_apply_of_valid fL fL_valid, toV_apply_of_valid hR hR_valid,
      toV_apply_of_valid eR eR_valid, toV_apply_of_valid fR fR_valid] using h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5, d6⟩, ⟨e1, e2, e3, e4, e5, e6⟩, ⟨f1, f2, f3, f4, f5, f6⟩⟩ :=
    current_coeffs
  have q0 := ev (S 0 0 0 0 0 0 0 0 [0]) (by decide)
  have q1 := ev (S 0 0 0 0 0 0 0 0 [1]) (by decide)
  have q2 := ev (S (-1) (-2) (-3) (-2) (-1) (-2) 0 0 []) (by decide)
  have q3 := ev (S 1 2 3 2 1 2 0 0 []) (by decide)
  have q4 := ev (S 1 0 0 0 0 0 0 0 []) (by decide)
  have q5 := ev (S (-1) 0 0 0 0 0 0 0 []) (by decide)
  rw [a1, a2, a3, a4, a5, a6] at q0
  rw [b1, b2, b3, b4, b5, b6] at q1
  rw [c1, c2, c3, c4, c5, c6] at q2
  rw [d1, d2, d3, d4, d5, d6] at q3
  rw [e1, e2, e3, e4, e5, e6] at q4
  rw [f1, f2, f3, f4, f5, f6] at q5
  push_cast at q0 q1 q2 q3 q4 q5
  have g3 : g 3 = 0 := by linear_combination (-1 / 2 : ℂ) * q1 + q0
  have g0 : g 0 = 0 := by linear_combination 4 * q0 - (5 / 2 : ℂ) * q1
  have g1 : g 1 = 0 := by linear_combination q2
  have g2 : g 2 = 0 := by linear_combination -q3
  have g4 : g 4 = 0 := by linear_combination q4
  have g5 : g 5 = 0 := by linear_combination (-1 / 5 : ℂ) * q5
  intro i
  fin_cases i <;> assumption

theorem finrank_span_currentV :
    Module.finrank ℂ (Submodule.span ℂ ({toV hL, toV eL, toV fL, toV hR, toV eR, toV fR} : Set V))
      = 6 := by
  rw [← range_currentV, finrank_span_eq_card currentV_linearIndependent, Fintype.card_fin]

/-! ## The weight-one space -/

theorem finrank_supported_finset (F : Finset ValidState) :
    Module.finrank ℂ (Finsupp.supported ℂ ℂ (↑F : Set ValidState)) = F.card := by
  rw [(Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) (↑F : Set ValidState)).finrank_eq,
    Module.finrank_finsupp_self]
  exact Fintype.card_coe F

theorem gradeOneStates_valid : ∀ s ∈ gradeOneStates, Valid s := fun s hs =>
  (gradeOneStates_spec s hs).1

/-- The 86 canonical monomials of grade one. -/
def gradeOneValid : List ValidState :=
  gradeOneStates.pmap (fun s h => (⟨s, h⟩ : ValidState)) gradeOneStates_valid

theorem gradeSetC_one : gradeSetC 1 = ↑gradeOneValid.toFinset := by
  ext s
  simp only [gradeSetC, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, gradeOneValid,
    List.mem_pmap]
  constructor
  · intro h
    exact ⟨s.1, mem_gradeOneStates h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (gradeOneStates_spec a ha).2

theorem gradeOneValid_nodup : gradeOneValid.Nodup :=
  List.Nodup.pmap (fun _ _ _ _ h => Subtype.mk.inj h) gradeOneStates_nodup

theorem gradeOneValid_length : gradeOneValid.length = 86 := by
  rw [gradeOneValid, List.length_pmap, gradeOneStates_length]

/-- **`dim B₁ = 86`** in the Fock model over `ℂ`. -/
theorem finrank_gradeC_one : Module.finrank ℂ (gradeC 1) = 86 := by
  rw [gradeC, gradeSetC_one, finrank_supported_finset,
    List.toFinset_card_of_nodup gradeOneValid_nodup, gradeOneValid_length]

/-! ## The closure data and the `certDimensions` node -/

/-- The closure data of the properness argument for the lattice VOA: the six currents of
`Lattice/Data.lean`; `S₂`, `S₃` and the triplet `q₊, q₀, q₋` are parameters (with their
grades). -/
noncomputable def latticeClosureData (hF : FLMInput) (S₂ S₃ : Submodule ℂ V)
    (hS₂ : S₂ ≤ gradeC 2) (hS₃ : S₃ ≤ gradeC 3) (qp q0 qm : V)
    (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4) : ClosureData (latticeVOA hF) where
  hL := toV hL
  eL := toV eL
  fL := toV fL
  hR := toV hR
  eR := toV eR
  fR := toV fR
  S₂ := S₂
  S₃ := S₃
  qp := qp
  q0 := q0
  qm := qm
  currents_grade := by
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact toV_mem_gradeC _ (currents_basisStates 0)
    · exact toV_mem_gradeC _ (currents_basisStates 1)
    · exact toV_mem_gradeC _ (currents_basisStates 2)
    · exact toV_mem_gradeC _ (currents_basisStates 3)
    · exact toV_mem_gradeC _ (currents_basisStates 4)
    · exact toV_mem_gradeC _ (currents_basisStates 5)
  S₂_grade := hS₂
  S₃_grade := hS₃
  triplet_grade := hq

/-- `K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`: the kernel-checked brackets of `Lattice/Relations.lean`. -/
theorem isSl2SumSpan_lattice (hF : FLMInput) (K : Submodule ℂ V)
    (hK : K = Submodule.span ℂ {toV hL, toV eL, toV fL, toV hR, toV eR, toV fR}) :
    IsSl2SumSpan (latticeVOA hF) K := by
  obtain ⟨l1, l2, l3, -⟩ := left_sl2
  obtain ⟨r1, r2, r3, -⟩ := right_sl2
  refine ⟨toV hL, toV eL, toV fL, toV hR, toV eR, toV fR, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [latticeVOA_mode, modeC_toV_of_mode hL_valid eL_valid l1, toV_smul]
    norm_num
  · rw [latticeVOA_mode, modeC_toV_of_mode hL_valid fL_valid l2, toV_smul]
    norm_num
  · rw [latticeVOA_mode, modeC_toV_of_mode eL_valid fL_valid l3]
  · rw [latticeVOA_mode, modeC_toV_of_mode hR_valid eR_valid r1, toV_smul]
    norm_num
  · rw [latticeVOA_mode, modeC_toV_of_mode hR_valid fR_valid r2, toV_smul]
    norm_num
  · rw [latticeVOA_mode, modeC_toV_of_mode eR_valid fR_valid r3]
  · have hc := left_right_commute
    rintro x hx y hy
    rw [latticeVOA_mode]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals
      first
      | exact (modeC_toV_of_mode hL_valid hR_valid (hc hL (by simp) hR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode hL_valid eR_valid (hc hL (by simp) eR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode hL_valid fR_valid (hc hL (by simp) fR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode eL_valid hR_valid (hc eL (by simp) hR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode eL_valid eR_valid (hc eL (by simp) eR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode eL_valid fR_valid (hc eL (by simp) fR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode fL_valid hR_valid (hc fL (by simp) hR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode fL_valid eR_valid (hc fL (by simp) eR (by simp)).1).trans toV_nil
      | exact (modeC_toV_of_mode fL_valid fR_valid (hc fL (by simp) fR (by simp)).1).trans toV_nil

/-- **The `certDimensions` node for the lattice VOA** (given only the FLM input, needed to have
the algebra): `dim K = 6`, `dim B₁ = 86`, `K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`, for any `S₂`, `S₃`, `P₄` and `u`. -/
theorem certDimensions_lattice (hF : FLMInput) (R : Nodes) (S₂ S₃ : Submodule ℂ V)
    (hS₂ : S₂ ≤ gradeC 2) (hS₃ : S₃ ≤ gradeC 3) (qp q0 qm : V)
    (hq : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ gradeC 4) (u : V) :
    (concreteNodes R (latticeClosureData hF S₂ S₃ hS₂ hS₃ qp q0 qm hq) u).certDimensions := by
  dsimp only [concreteNodes]
  refine ⟨finrank_span_currentV, finrank_gradeC_one, isSl2SumSpan_lattice hF _ rfl⟩

#print axioms latticeVOA
#print axioms finrank_gradeC_one
#print axioms finrank_span_currentV
#print axioms isSl2SumSpan_lattice
#print axioms certDimensions_lattice

end LatticeVOA
end HaagerupIzumi.C8
