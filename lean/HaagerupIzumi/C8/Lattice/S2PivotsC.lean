module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# The echelon basis of `S₂`, part C: canonical states of `r_k`, 60 ≤ k ≤ 74

Split from the generated `S2Pivots.lean` (`lean/tools/lattice_export/gen_s2.py`): kernel
memory accumulates over the declarations of a file (about 0.2 GiB per second of kernel time),
so the checks are spread over several files.  `s2r_k_states`: all states of `r_k` are canonical
(sorted code lists) of grade two.  Assembled in `S2Pivots.lean`.
-/


namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem s2r_60_states : s2r_60.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_61_states : s2r_61.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_62_states : s2r_62.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_63_states : s2r_63.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_64_states : s2r_64.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_65_states : s2r_65.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_66_states : s2r_66.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_67_states : s2r_67.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_68_states : s2r_68.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_69_states : s2r_69.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_70_states : s2r_70.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_71_states : s2r_71.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_72_states : s2r_72.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_73_states : s2r_73.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_74_states : s2r_74.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
