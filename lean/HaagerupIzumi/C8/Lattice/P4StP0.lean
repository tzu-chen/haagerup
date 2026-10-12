module

public import HaagerupIzumi.C8.Lattice.P4DataP0
public import HaagerupIzumi.C8.Lattice.P4Eig

@[expose] public section
/-!
# The triplet field `P4_plus`, chunk 0: canonical grade-four states, Cartan eigenvalues

Kernel check: every state of `p4P_0` is canonical of grade four with integer Cartan
eigenvalues `H_L ↦ 0`, `H_R ↦ 2` (`P4Good`, `P4Eig.lean`), each state checked once (on the
component `c1`, which carries every state of the triplet data; the other components are sorted
sublists of it, `subsetSorted`).  `p4P_0_good`: the consequence for all components.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA
set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem p4P_0_check : (∀ p ∈ p4P_0.c1, P4Good (2) p.1) ∧
    subsetSorted (p4P_0.c0.map Prod.fst) (p4P_0.c1.map Prod.fst) = true ∧
    subsetSorted (p4P_0.c2.map Prod.fst) (p4P_0.c1.map Prod.fst) = true ∧
    subsetSorted (p4P_0.c3.map Prod.fst) (p4P_0.c1.map Prod.fst) = true := by
  decide +kernel

theorem p4P_0_good : p4P_0.AllStates (P4Good (2)) :=
  allStates_of_c1 p4P_0_check.1 p4P_0_check.2.1 p4P_0_check.2.2.1
    p4P_0_check.2.2.2

end LatticeVOA
end HaagerupIzumi.C8
