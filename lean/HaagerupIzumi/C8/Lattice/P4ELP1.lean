module

public import HaagerupIzumi.C8.Lattice.P4ELP1a
public import HaagerupIzumi.C8.Lattice.P4ELP1b

@[expose] public section

/-!
# The left current `E_L(0)` kills the triplet chunk `p4P_1`

Assembled from the component checks `P4ELP1a`, `P4ELP1b`.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem p4P_1_eL : Vec4.mode (Vec4.ofVec eL) 0 p4P_1 = Vec4.zero := by
  have ha := p4P_1_eL_a
  have hb := p4P_1_eL_b
  cases h : Vec4.mode (Vec4.ofVec eL) 0 p4P_1 with
  | mk a b c d =>
    rw [h] at ha hb
    simp only at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    rfl

end LatticeVOA
end HaagerupIzumi.C8
