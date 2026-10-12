module

public import HaagerupIzumi.C8.Lattice.P4DataM2
public import HaagerupIzumi.C8.Lattice.Data

@[expose] public section

/-!
# `F_L(0)` on the triplet chunk `p4M_2`, components `c2`, `c3`

Half of the check of `P4FLM2.lean` (this chunk is large; the components of `Vec4.mode` are
evaluated separately).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem p4M_2_fL_b : (Vec4.mode (Vec4.ofVec fL) 0 p4M_2).c2 = [] ∧
    (Vec4.mode (Vec4.ofVec fL) 0 p4M_2).c3 = [] := by
  decide +kernel

end LatticeVOA
end HaagerupIzumi.C8
