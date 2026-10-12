module

public import HaagerupIzumi.C8.Lattice.P4DataP3
public import HaagerupIzumi.C8.Lattice.Data

@[expose] public section

/-!
# The left current `F_L(0)` kills the triplet field `P4_plus`, chunk 3

Kernel evaluation of the lattice modes (`Vec4.mode`): `F_L(0) p4P_3 = 0`.  The chunks of the
triplet data are cut at changes of momentum (`gen_p4.py`), and `F_L` is a single root vector,
so the image of each chunk vanishes separately.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem p4P_3_fL : Vec4.mode (Vec4.ofVec fL) 0 p4P_3 = Vec4.zero := by
  decide +kernel

end LatticeVOA
end HaagerupIzumi.C8
