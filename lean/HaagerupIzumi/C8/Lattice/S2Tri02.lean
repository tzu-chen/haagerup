module

public import HaagerupIzumi.C8.Lattice.S2Coeff

@[expose] public section

/-!
# Triangularity of the echelon basis of `S₂`, part 2

`s2tri_k`, 52 ≤ k ≤ 57: `r_k` has coefficient `1` at its pivot `s2piv[k]`
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

theorem s2tri_52 :
    (s2basis.getD 52 Vec4.zero).PivotAt (s2piv.getD 52 vacState) ∧
      ∀ j < 52, (s2basis.getD 52 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_53 :
    (s2basis.getD 53 Vec4.zero).PivotAt (s2piv.getD 53 vacState) ∧
      ∀ j < 53, (s2basis.getD 53 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_54 :
    (s2basis.getD 54 Vec4.zero).PivotAt (s2piv.getD 54 vacState) ∧
      ∀ j < 54, (s2basis.getD 54 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_55 :
    (s2basis.getD 55 Vec4.zero).PivotAt (s2piv.getD 55 vacState) ∧
      ∀ j < 55, (s2basis.getD 55 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_56 :
    (s2basis.getD 56 Vec4.zero).PivotAt (s2piv.getD 56 vacState) ∧
      ∀ j < 56, (s2basis.getD 56 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_57 :
    (s2basis.getD 57 Vec4.zero).PivotAt (s2piv.getD 57 vacState) ∧
      ∀ j < 57, (s2basis.getD 57 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
