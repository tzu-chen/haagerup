module

public import HaagerupIzumi.C8.Lattice.P4FLM2a
public import HaagerupIzumi.C8.Lattice.P4FLM2b

@[expose] public section

/-!
# The left current `F_L(0)` kills the triplet chunk `p4M_2`

Assembled from the component checks `P4FLM2a`, `P4FLM2b`.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem p4M_2_fL : Vec4.mode (Vec4.ofVec fL) 0 p4M_2 = Vec4.zero := by
  have ha := p4M_2_fL_a
  have hb := p4M_2_fL_b
  cases h : Vec4.mode (Vec4.ofVec fL) 0 p4M_2 with
  | mk a b c d =>
    rw [h] at ha hb
    simp only at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    rfl

end LatticeVOA
end HaagerupIzumi.C8
