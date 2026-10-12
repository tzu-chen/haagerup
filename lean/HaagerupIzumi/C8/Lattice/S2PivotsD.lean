module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# The echelon basis of `S₂`, part D: canonical states of `r_k`, 75 ≤ k ≤ 89

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

theorem s2r_75_states : s2r_75.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_76_states : s2r_76.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_77_states : s2r_77.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_78_states : s2r_78.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_79_states : s2r_79.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_80_states : s2r_80.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_81_states : s2r_81.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_82_states : s2r_82.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_83_states : s2r_83.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_84_states : s2r_84.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_85_states : s2r_85.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_86_states : s2r_86.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_87_states : s2r_87.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_88_states : s2r_88.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_89_states : s2r_89.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
