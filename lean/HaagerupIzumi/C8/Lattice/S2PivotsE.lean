module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# The echelon basis of `S₂`, part E: canonical states of `r_k`, 90 ≤ k ≤ 104

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

theorem s2r_90_states : s2r_90.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_91_states : s2r_91.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_92_states : s2r_92.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_93_states : s2r_93.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_94_states : s2r_94.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_95_states : s2r_95.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_96_states : s2r_96.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_97_states : s2r_97.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_98_states : s2r_98.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_99_states : s2r_99.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_100_states : s2r_100.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_101_states : s2r_101.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_102_states : s2r_102.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_103_states : s2r_103.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_104_states : s2r_104.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
