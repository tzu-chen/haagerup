module

public import HaagerupIzumi.C8.Lattice.S2Coeff

@[expose] public section

/-!
# Triangularity of the echelon basis of `S₂`, part 1

`s2tri_k`, 40 ≤ k ≤ 51: `r_k` has coefficient `1` at its pivot `s2piv[k]`
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

theorem s2tri_40 :
    (s2basis.getD 40 Vec4.zero).PivotAt (s2piv.getD 40 vacState) ∧
      ∀ j < 40, (s2basis.getD 40 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_41 :
    (s2basis.getD 41 Vec4.zero).PivotAt (s2piv.getD 41 vacState) ∧
      ∀ j < 41, (s2basis.getD 41 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_42 :
    (s2basis.getD 42 Vec4.zero).PivotAt (s2piv.getD 42 vacState) ∧
      ∀ j < 42, (s2basis.getD 42 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_43 :
    (s2basis.getD 43 Vec4.zero).PivotAt (s2piv.getD 43 vacState) ∧
      ∀ j < 43, (s2basis.getD 43 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_44 :
    (s2basis.getD 44 Vec4.zero).PivotAt (s2piv.getD 44 vacState) ∧
      ∀ j < 44, (s2basis.getD 44 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_45 :
    (s2basis.getD 45 Vec4.zero).PivotAt (s2piv.getD 45 vacState) ∧
      ∀ j < 45, (s2basis.getD 45 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_46 :
    (s2basis.getD 46 Vec4.zero).PivotAt (s2piv.getD 46 vacState) ∧
      ∀ j < 46, (s2basis.getD 46 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_47 :
    (s2basis.getD 47 Vec4.zero).PivotAt (s2piv.getD 47 vacState) ∧
      ∀ j < 47, (s2basis.getD 47 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_48 :
    (s2basis.getD 48 Vec4.zero).PivotAt (s2piv.getD 48 vacState) ∧
      ∀ j < 48, (s2basis.getD 48 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_49 :
    (s2basis.getD 49 Vec4.zero).PivotAt (s2piv.getD 49 vacState) ∧
      ∀ j < 49, (s2basis.getD 49 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_50 :
    (s2basis.getD 50 Vec4.zero).PivotAt (s2piv.getD 50 vacState) ∧
      ∀ j < 50, (s2basis.getD 50 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_51 :
    (s2basis.getD 51 Vec4.zero).PivotAt (s2piv.getD 51 vacState) ∧
      ∀ j < 51, (s2basis.getD 51 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
