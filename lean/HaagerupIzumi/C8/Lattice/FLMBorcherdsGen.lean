module

public import HaagerupIzumi.C8.Lattice.FLMReduce
public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsClosure

@[expose] public section

/-!
# `FLMBorcherds` from the Borcherds identity for the 24 generating fields

W3, first milestone (`Lattice/W3_PLAN.md`).  The Fock model `V` with the modes `modeC` is a
`ModeAlgebra` (`fockMA`; every field is a theorem of `Lattice/Model*.lean`).  With the abstract
results of `VertexAlgebra/BorcherdsReduce.lean` and the generation theorem
`eq_top_of_genClosed` (`Lattice/FLMGen.lean`: `V` is generated from `𝟏` by the modes of the 24
fields `hᵢ(-1)𝟏`, `e^{±αᵢ}`):

* `flmBorcherds_iff_good`: `FLMBorcherds` (the one remaining assumption of the lattice model,
  `FLMInput.borcherds`) is equivalent to `Good a` for every `a`;
* `flmBorcherds_of_productClosedFor`: `FLMBorcherds` holds as soon as `Good` is stable under
  `g_(n) -` for the 24 generators `g` (the vacuum is `Good` by `ModeAlgebra.good_vac`);
* **`flmBorcherds_of_generators`**: `FLMBorcherds` follows from the closure of `Good` under
  `n`-th products of homogeneous vectors (`ModeAlgebra.ProductClosedHom`, the general theorem of
  milestone item (1), not yet formalized) and the Borcherds identity `Good g` for the 24
  generating fields (`flmBorcherds_of_generators'`: the same with the stronger
  `ProductClosed`).

So, modulo the general closure theorem (1), `FLMBorcherds` reduces to the Borcherds identity
for the 24 generator fields in the first slot (the Heisenberg and lattice vertex operator
commutator/iterate formulas).  Nothing here is an external hypothesis; (1) and `Good g` enter
as hypotheses of `flmBorcherds_of_generators` only.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- The Fock model as a `ModeAlgebra`: every field is proved. -/
noncomputable def fockMA : ModeAlgebra ℂ V where
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

theorem fockMA_mode : fockMA.mode = modeC := rfl

/-- `FLMBorcherds` in terms of `ModeAlgebra.bL`, `bR`. -/
theorem flmBorcherds_iff_bL_bR : FLMBorcherds ↔
    ∀ {i j l : ℕ} {a b c : V}, a ∈ gradeC i → b ∈ gradeC j → c ∈ gradeC l → ∀ p q r : ℤ,
      fockMA.bL a b c p q r (ModeAlgebra.bN i j l p q r) =
        fockMA.bR a b c p q r (ModeAlgebra.bN i j l p q r) :=
  Iff.rfl

/-- **`FLMBorcherds` is `Good` for every vector.** -/
theorem flmBorcherds_iff_good : FLMBorcherds ↔ ∀ a, fockMA.Good a := by
  constructor
  · intro hB
    have hhom : ∀ i, gradeC i ≤ fockMA.goodSub := by
      intro i a ha
      rw [ModeAlgebra.mem_goodSub, fockMA.good_iff_bD (i := i) ha]
      intro j l b c hb hc p q r
      exact sub_eq_zero.2 (hB ha hb hc p q r)
    have htop : fockMA.goodSub = ⊤ := by
      rw [eq_top_iff, ← gradeC_internal.submodule_iSup_eq_top]
      exact iSup_le hhom
    intro a
    rw [← ModeAlgebra.mem_goodSub, htop]
    exact Submodule.mem_top
  · intro h i j l a b c ha hb hc p q r
    exact sub_eq_zero.1 ((fockMA.good_iff_bD ha).1 (h a) hb hc p q r)

/-- **`FLMBorcherds` from closure under the generators**: if `Good` is stable under `g_(n) -` for
the 24 fields `g ∈ GenSet`, then `FLMBorcherds` holds. -/
theorem flmBorcherds_of_productClosedFor (h : fockMA.ProductClosedFor GenSet) : FLMBorcherds :=
  fun ha hb hc p q r =>
    fockMA.borcherds_of_generation h (fun _ hW hcl => eq_top_of_genClosed ⟨hW, hcl⟩) ha hb hc
      p q r

/-- **`FLMBorcherds` reduces to the 24 generator fields**, given the general closure of the
Borcherds identity under `n`-th products of homogeneous vectors (`ProductClosedHom`, milestone
item (1)). -/
theorem flmBorcherds_of_generators (hP : fockMA.ProductClosedHom)
    (hgen : ∀ g ∈ GenSet, fockMA.Good g) : FLMBorcherds := by
  have htop := fockMA.goodSub_eq_top_of_hom (G := GenSet)
    (fun g hg => ⟨⟨1, (genSet_facts g hg).1⟩, hgen g hg⟩) hP
    (fun _ hW hcl => eq_top_of_genClosed ⟨hW, hcl⟩)
  have hall : ∀ a, fockMA.Good a := fun a => by
    rw [← ModeAlgebra.mem_goodSub, htop]
    exact Submodule.mem_top
  intro i j l a b c ha hb hc p q r
  exact (flmBorcherds_iff_good.2 hall) ha hb hc p q r

/-- The same with the general closure `ProductClosed`. -/
theorem flmBorcherds_of_generators' (hP : fockMA.ProductClosed)
    (hgen : ∀ g ∈ GenSet, fockMA.Good g) : FLMBorcherds :=
  flmBorcherds_of_generators (fockMA.productClosedHom_of_productClosed hP) hgen

/-- With the general closure theorem, `FLMInput` (hence the lattice VOA) follows from the
Borcherds identity for the 24 generator fields. -/
theorem flmInput_of_generators (hP : fockMA.ProductClosedHom)
    (hgen : ∀ g ∈ GenSet, fockMA.Good g) : FLMInput :=
  flmInput_of_borcherds (flmBorcherds_of_generators hP hgen)

end LatticeVOA
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.LatticeVOA.flmBorcherds_iff_good
#print axioms HaagerupIzumi.C8.LatticeVOA.flmBorcherds_of_productClosedFor
#print axioms HaagerupIzumi.C8.LatticeVOA.flmBorcherds_of_generators
#print axioms HaagerupIzumi.C8.LatticeVOA.flmInput_of_generators
