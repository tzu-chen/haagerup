module

public import HaagerupIzumi.C8.Lattice.P4DataZ1
public import HaagerupIzumi.C8.Lattice.Data

@[expose] public section

/-!
# `F_L(0)` on the triplet chunk `p4Z_1`, components `c0`, `c1`

Half of the check of `P4FLZ1.lean` (this chunk is large; the components of `Vec4.mode` are
evaluated separately).
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem p4Z_1_fL_a : (Vec4.mode (Vec4.ofVec fL) 0 p4Z_1).c0 = [] ∧
    (Vec4.mode (Vec4.ofVec fL) 0 p4Z_1).c1 = [] := by
  decide +kernel

end LatticeVOA
end HaagerupIzumi.C8
