module

public import HaagerupIzumi.C8.Lattice.P4ELM2a
public import HaagerupIzumi.C8.Lattice.P4ELM2b

@[expose] public section

/-!
# The left current `E_L(0)` kills the triplet chunk `p4M_2`

Assembled from the component checks `P4ELM2a`, `P4ELM2b`.  Used in `P4Left.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem p4M_2_eL : Vec4.mode (Vec4.ofVec eL) 0 p4M_2 = Vec4.zero := by
  have ha := p4M_2_eL_a
  have hb := p4M_2_eL_b
  cases h : Vec4.mode (Vec4.ofVec eL) 0 p4M_2 with
  | mk a b c d =>
    rw [h] at ha hb
    simp only at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    rfl

end LatticeVOA
end HaagerupIzumi.C8
