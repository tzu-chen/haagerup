module

public import HaagerupIzumi.C8.Lattice.P4FLZ1a
public import HaagerupIzumi.C8.Lattice.P4FLZ1b

@[expose] public section

/-!
# The left current `F_L(0)` kills the triplet chunk `p4Z_1`

Assembled from the component checks `P4FLZ1a`, `P4FLZ1b`.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem p4Z_1_fL : Vec4.mode (Vec4.ofVec fL) 0 p4Z_1 = Vec4.zero := by
  have ha := p4Z_1_fL_a
  have hb := p4Z_1_fL_b
  cases h : Vec4.mode (Vec4.ofVec fL) 0 p4Z_1 with
  | mk a b c d =>
    rw [h] at ha hb
    simp only at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    rfl

end LatticeVOA
end HaagerupIzumi.C8
