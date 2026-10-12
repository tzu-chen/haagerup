module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-!
# The echelon basis of `S₂`, part A: canonical states of `r_k`, 0 ≤ k ≤ 29

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

theorem s2u_valid : s2u.AllStates Valid := by
  decide +kernel

theorem s2r_0_states : s2r_0.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_1_states : s2r_1.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_2_states : s2r_2.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_3_states : s2r_3.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_4_states : s2r_4.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_5_states : s2r_5.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_6_states : s2r_6.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_7_states : s2r_7.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_8_states : s2r_8.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_9_states : s2r_9.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_10_states : s2r_10.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_11_states : s2r_11.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_12_states : s2r_12.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_13_states : s2r_13.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_14_states : s2r_14.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_15_states : s2r_15.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_16_states : s2r_16.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_17_states : s2r_17.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_18_states : s2r_18.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_19_states : s2r_19.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_20_states : s2r_20.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_21_states : s2r_21.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_22_states : s2r_22.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_23_states : s2r_23.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_24_states : s2r_24.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_25_states : s2r_25.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_26_states : s2r_26.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_27_states : s2r_27.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_28_states : s2r_28.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel

theorem s2r_29_states : s2r_29.AllStates fun s => Valid s ∧ grade s = 2 := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
