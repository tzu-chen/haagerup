module

public import HaagerupIzumi.C8.Lattice.P4ELZ1a
public import HaagerupIzumi.C8.Lattice.P4ELZ1b

@[expose] public section

/-!
# The left current `E_L(0)` kills the triplet chunk `p4Z_1`

Assembled from the component checks `P4ELZ1a`, `P4ELZ1b`.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem p4Z_1_eL : Vec4.mode (Vec4.ofVec eL) 0 p4Z_1 = Vec4.zero := by
  have ha := p4Z_1_eL_a
  have hb := p4Z_1_eL_b
  cases h : Vec4.mode (Vec4.ofVec eL) 0 p4Z_1 with
  | mk a b c d =>
    rw [h] at ha hb
    simp only at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    rfl

end LatticeVOA
end HaagerupIzumi.C8
