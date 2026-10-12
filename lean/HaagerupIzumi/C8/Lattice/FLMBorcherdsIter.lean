module

public import HaagerupIzumi.C8.Lattice.FLMBorcherdsGen
public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsProduct
public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsAssocFace

@[expose] public section

/-!
# `FLMBorcherds` from the iterate family of products and the 24 generators

W3 (`Lattice/W3_PLAN.md`).  With Dong's lemma formalized
(`VertexAlgebra/BorcherdsDongModes.lean`), the general closure hypothesis `ProductClosedHom` of
`flmBorcherds_of_generators` is replaced by the weaker `IterClosed` (the iterate family of the
Borcherds identity for `a_(n) w`, homogeneous `Good a`, `Good w`):

* `flmBorcherds_of_generators_iter (hI : fockMA.IterClosed) (hgen : ∀ g ∈ GenSet, fockMA.Good g)
  : FLMBorcherds`;
* `flmBorcherds_of_generators_assoc (hA : fockMA.AssocStep) (hgen) : FLMBorcherds`, the same with
  the induction step `AssocStep` of the downward induction on `n`
  (`VertexAlgebra/BorcherdsAssocFace.lean`).

Nothing here is an external hypothesis; `hI` and `hgen` are hypotheses of the theorem.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- **`FLMBorcherds` from the iterate family of products and the 24 generator fields.** -/
theorem flmBorcherds_of_generators_iter (hI : fockMA.IterClosed)
    (hgen : ∀ g ∈ GenSet, fockMA.Good g) : FLMBorcherds :=
  flmBorcherds_of_generators (fockMA.productClosedHom_of_iterClosed hI) hgen

/-- The same for `FLMInput`. -/
theorem flmInput_of_generators_iter (hI : fockMA.IterClosed)
    (hgen : ∀ g ∈ GenSet, fockMA.Good g) : FLMInput :=
  flmInput_of_borcherds (flmBorcherds_of_generators_iter hI hgen)

/-- **`FLMBorcherds` from the induction step `AssocStep` and the 24 generator fields.** -/
theorem flmBorcherds_of_generators_assoc (hA : fockMA.AssocStep)
    (hgen : ∀ g ∈ GenSet, fockMA.Good g) : FLMBorcherds :=
  flmBorcherds_of_generators (fockMA.productClosedHom_of_assocStep hA) hgen

end LatticeVOA
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.LatticeVOA.flmBorcherds_of_generators_iter
#print axioms HaagerupIzumi.C8.LatticeVOA.flmInput_of_generators_iter
#print axioms HaagerupIzumi.C8.LatticeVOA.flmBorcherds_of_generators_assoc
