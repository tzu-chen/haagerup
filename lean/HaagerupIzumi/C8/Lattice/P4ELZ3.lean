module

public import HaagerupIzumi.C8.Lattice.P4DataZ3
public import HaagerupIzumi.C8.Lattice.Data

@[expose] public section

/-!
# The left current `E_L(0)` kills the triplet field `P4_zero`, chunk 3

Kernel evaluation of the lattice modes (`Vec4.mode`): `E_L(0) p4Z_3 = 0`.  The chunks of the
triplet data are cut at changes of momentum (`gen_p4.py`), and `E_L` is a single root vector,
so the image of each chunk vanishes separately.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem p4Z_3_eL : Vec4.mode (Vec4.ofVec eL) 0 p4Z_3 = Vec4.zero := by
  decide +kernel

end LatticeVOA
end HaagerupIzumi.C8
