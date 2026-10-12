module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# The echelon basis of `S₂`, part B: canonical states of `r_k`, 30 ≤ k ≤ 59

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

theorem s2r_30_states : s2r_30.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_31_states : s2r_31.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_32_states : s2r_32.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_33_states : s2r_33.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_34_states : s2r_34.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_35_states : s2r_35.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_36_states : s2r_36.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_37_states : s2r_37.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_38_states : s2r_38.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_39_states : s2r_39.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_40_states : s2r_40.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_41_states : s2r_41.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_42_states : s2r_42.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_43_states : s2r_43.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_44_states : s2r_44.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_45_states : s2r_45.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_46_states : s2r_46.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_47_states : s2r_47.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_48_states : s2r_48.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_49_states : s2r_49.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_50_states : s2r_50.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_51_states : s2r_51.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_52_states : s2r_52.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_53_states : s2r_53.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_54_states : s2r_54.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_55_states : s2r_55.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_56_states : s2r_56.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_57_states : s2r_57.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_58_states : s2r_58.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_59_states : s2r_59.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
