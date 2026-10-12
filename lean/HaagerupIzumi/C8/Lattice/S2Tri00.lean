module

public import HaagerupIzumi.C8.Lattice.S2Coeff

@[expose] public section

/-!
# Triangularity of the echelon basis of `S₂`, part 0

`s2tri_k`, 0 ≤ k ≤ 39: `r_k` has coefficient `1` at its pivot `s2piv[k]`
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

theorem s2tri_0 :
    (s2basis.getD 0 Vec4.zero).PivotAt (s2piv.getD 0 vacState) ∧
      ∀ j < 0, (s2basis.getD 0 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_1 :
    (s2basis.getD 1 Vec4.zero).PivotAt (s2piv.getD 1 vacState) ∧
      ∀ j < 1, (s2basis.getD 1 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_2 :
    (s2basis.getD 2 Vec4.zero).PivotAt (s2piv.getD 2 vacState) ∧
      ∀ j < 2, (s2basis.getD 2 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_3 :
    (s2basis.getD 3 Vec4.zero).PivotAt (s2piv.getD 3 vacState) ∧
      ∀ j < 3, (s2basis.getD 3 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_4 :
    (s2basis.getD 4 Vec4.zero).PivotAt (s2piv.getD 4 vacState) ∧
      ∀ j < 4, (s2basis.getD 4 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_5 :
    (s2basis.getD 5 Vec4.zero).PivotAt (s2piv.getD 5 vacState) ∧
      ∀ j < 5, (s2basis.getD 5 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_6 :
    (s2basis.getD 6 Vec4.zero).PivotAt (s2piv.getD 6 vacState) ∧
      ∀ j < 6, (s2basis.getD 6 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_7 :
    (s2basis.getD 7 Vec4.zero).PivotAt (s2piv.getD 7 vacState) ∧
      ∀ j < 7, (s2basis.getD 7 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_8 :
    (s2basis.getD 8 Vec4.zero).PivotAt (s2piv.getD 8 vacState) ∧
      ∀ j < 8, (s2basis.getD 8 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_9 :
    (s2basis.getD 9 Vec4.zero).PivotAt (s2piv.getD 9 vacState) ∧
      ∀ j < 9, (s2basis.getD 9 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_10 :
    (s2basis.getD 10 Vec4.zero).PivotAt (s2piv.getD 10 vacState) ∧
      ∀ j < 10, (s2basis.getD 10 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_11 :
    (s2basis.getD 11 Vec4.zero).PivotAt (s2piv.getD 11 vacState) ∧
      ∀ j < 11, (s2basis.getD 11 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_12 :
    (s2basis.getD 12 Vec4.zero).PivotAt (s2piv.getD 12 vacState) ∧
      ∀ j < 12, (s2basis.getD 12 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_13 :
    (s2basis.getD 13 Vec4.zero).PivotAt (s2piv.getD 13 vacState) ∧
      ∀ j < 13, (s2basis.getD 13 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_14 :
    (s2basis.getD 14 Vec4.zero).PivotAt (s2piv.getD 14 vacState) ∧
      ∀ j < 14, (s2basis.getD 14 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_15 :
    (s2basis.getD 15 Vec4.zero).PivotAt (s2piv.getD 15 vacState) ∧
      ∀ j < 15, (s2basis.getD 15 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_16 :
    (s2basis.getD 16 Vec4.zero).PivotAt (s2piv.getD 16 vacState) ∧
      ∀ j < 16, (s2basis.getD 16 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_17 :
    (s2basis.getD 17 Vec4.zero).PivotAt (s2piv.getD 17 vacState) ∧
      ∀ j < 17, (s2basis.getD 17 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_18 :
    (s2basis.getD 18 Vec4.zero).PivotAt (s2piv.getD 18 vacState) ∧
      ∀ j < 18, (s2basis.getD 18 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_19 :
    (s2basis.getD 19 Vec4.zero).PivotAt (s2piv.getD 19 vacState) ∧
      ∀ j < 19, (s2basis.getD 19 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_20 :
    (s2basis.getD 20 Vec4.zero).PivotAt (s2piv.getD 20 vacState) ∧
      ∀ j < 20, (s2basis.getD 20 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_21 :
    (s2basis.getD 21 Vec4.zero).PivotAt (s2piv.getD 21 vacState) ∧
      ∀ j < 21, (s2basis.getD 21 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_22 :
    (s2basis.getD 22 Vec4.zero).PivotAt (s2piv.getD 22 vacState) ∧
      ∀ j < 22, (s2basis.getD 22 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_23 :
    (s2basis.getD 23 Vec4.zero).PivotAt (s2piv.getD 23 vacState) ∧
      ∀ j < 23, (s2basis.getD 23 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_24 :
    (s2basis.getD 24 Vec4.zero).PivotAt (s2piv.getD 24 vacState) ∧
      ∀ j < 24, (s2basis.getD 24 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_25 :
    (s2basis.getD 25 Vec4.zero).PivotAt (s2piv.getD 25 vacState) ∧
      ∀ j < 25, (s2basis.getD 25 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_26 :
    (s2basis.getD 26 Vec4.zero).PivotAt (s2piv.getD 26 vacState) ∧
      ∀ j < 26, (s2basis.getD 26 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_27 :
    (s2basis.getD 27 Vec4.zero).PivotAt (s2piv.getD 27 vacState) ∧
      ∀ j < 27, (s2basis.getD 27 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_28 :
    (s2basis.getD 28 Vec4.zero).PivotAt (s2piv.getD 28 vacState) ∧
      ∀ j < 28, (s2basis.getD 28 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_29 :
    (s2basis.getD 29 Vec4.zero).PivotAt (s2piv.getD 29 vacState) ∧
      ∀ j < 29, (s2basis.getD 29 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_30 :
    (s2basis.getD 30 Vec4.zero).PivotAt (s2piv.getD 30 vacState) ∧
      ∀ j < 30, (s2basis.getD 30 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_31 :
    (s2basis.getD 31 Vec4.zero).PivotAt (s2piv.getD 31 vacState) ∧
      ∀ j < 31, (s2basis.getD 31 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_32 :
    (s2basis.getD 32 Vec4.zero).PivotAt (s2piv.getD 32 vacState) ∧
      ∀ j < 32, (s2basis.getD 32 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_33 :
    (s2basis.getD 33 Vec4.zero).PivotAt (s2piv.getD 33 vacState) ∧
      ∀ j < 33, (s2basis.getD 33 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_34 :
    (s2basis.getD 34 Vec4.zero).PivotAt (s2piv.getD 34 vacState) ∧
      ∀ j < 34, (s2basis.getD 34 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_35 :
    (s2basis.getD 35 Vec4.zero).PivotAt (s2piv.getD 35 vacState) ∧
      ∀ j < 35, (s2basis.getD 35 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_36 :
    (s2basis.getD 36 Vec4.zero).PivotAt (s2piv.getD 36 vacState) ∧
      ∀ j < 36, (s2basis.getD 36 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_37 :
    (s2basis.getD 37 Vec4.zero).PivotAt (s2piv.getD 37 vacState) ∧
      ∀ j < 37, (s2basis.getD 37 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_38 :
    (s2basis.getD 38 Vec4.zero).PivotAt (s2piv.getD 38 vacState) ∧
      ∀ j < 38, (s2basis.getD 38 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel

theorem s2tri_39 :
    (s2basis.getD 39 Vec4.zero).PivotAt (s2piv.getD 39 vacState) ∧
      ∀ j < 39, (s2basis.getD 39 Vec4.zero).AbsentAt (s2piv.getD j vacState) := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
