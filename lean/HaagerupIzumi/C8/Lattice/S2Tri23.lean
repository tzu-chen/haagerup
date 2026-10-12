module

public import HaagerupIzumi.C8.Lattice.S2Coeff

@[expose] public section

/-!
# Triangularity of the echelon basis of `S₂`, part 23

`s2tri_k`, 107 ≤ k ≤ 109: `r_k` has coefficient `1` at its pivot `s2piv[k]`
(`Vec4.PivotAt`) and coefficient `0` at the pivots of all earlier vectors (`Vec4.AbsentAt`),
checked by kernel evaluation of state comparisons only (`S2Coeff.lean`).  The checks are spread
over the files `S2Tri*.lean` so that each file needs at most about 2.5 s of kernel time (kernel
memory accumulates over the declarations of a file).  Assembled in `S2Pivots.lean`.
-/


namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 50
set_option Elab.async false

theorem s2tri_107 :
    (s2basis.getD 107 Vec4.zero).PivotAt (s2piv.getD 107 vacState) ∧
      ∀ j < 107, (s2basis.getD 107 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_108 :
    (s2basis.getD 108 Vec4.zero).PivotAt (s2piv.getD 108 vacState) ∧
      ∀ j < 108, (s2basis.getD 108 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_109 :
    (s2basis.getD 109 Vec4.zero).PivotAt (s2piv.getD 109 vacState) ∧
      ∀ j < 109, (s2basis.getD 109 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
