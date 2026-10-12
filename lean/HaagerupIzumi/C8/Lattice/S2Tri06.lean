module

public import HaagerupIzumi.C8.Lattice.S2Coeff

@[expose] public section

/-!
# Triangularity of the echelon basis of `S₂`, part 6

`s2tri_k`, 69 ≤ k ≤ 70: `r_k` has coefficient `1` at its pivot `s2piv[k]`
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

theorem s2tri_69 :
    (s2basis.getD 69 Vec4.zero).PivotAt (s2piv.getD 69 vacState) ∧
      ∀ j < 69, (s2basis.getD 69 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_70 :
    (s2basis.getD 70 Vec4.zero).PivotAt (s2piv.getD 70 vacState) ∧
      ∀ j < 70, (s2basis.getD 70 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
