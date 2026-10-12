module

public import HaagerupIzumi.C8.Lattice.P4DataZ1
public import HaagerupIzumi.C8.Lattice.P4Eig

@[expose] public section
/-!
# The triplet field `P4_zero`, chunk 1: canonical grade-four states, Cartan eigenvalues

Kernel check: every state of `p4Z_1` is canonical of grade four with integer Cartan
eigenvalues `H_L ↦ 0`, `H_R ↦ 0` (`P4Good`, `P4Eig.lean`), each state checked once (on the
component `c1`, which carries every state of the triplet data; the other components are sorted
sublists of it, `subsetSorted`).  `p4Z_1_good`: the consequence for all components.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA
set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem p4Z_1_check : (∀ p ∈ p4Z_1.c1, P4Good (0) p.1) ∧
    subsetSorted (p4Z_1.c0.map Prod.fst) (p4Z_1.c1.map Prod.fst) = true ∧
    subsetSorted (p4Z_1.c2.map Prod.fst) (p4Z_1.c1.map Prod.fst) = true ∧
    subsetSorted (p4Z_1.c3.map Prod.fst) (p4Z_1.c1.map Prod.fst) = true := by
  decide +kernel

theorem p4Z_1_good : p4Z_1.AllStates (P4Good (0)) :=
  allStates_of_c1 p4Z_1_check.1 p4Z_1_check.2.1 p4Z_1_check.2.2.1
    p4Z_1_check.2.2.2

end LatticeVOA
end HaagerupIzumi.C8
