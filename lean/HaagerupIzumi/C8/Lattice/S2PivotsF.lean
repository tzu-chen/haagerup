module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# The echelon basis of `S₂`, part F: canonical states of `r_k`, 105 ≤ k ≤ 119

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

theorem s2r_105_states : s2r_105.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_106_states : s2r_106.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_107_states : s2r_107.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_108_states : s2r_108.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_109_states : s2r_109.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_110_states : s2r_110.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_111_states : s2r_111.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_112_states : s2r_112.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_113_states : s2r_113.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_114_states : s2r_114.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_115_states : s2r_115.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_116_states : s2r_116.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_117_states : s2r_117.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_118_states : s2r_118.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_119_states : s2r_119.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
