module

public import HaagerupIzumi.C8.Lattice.S2Data

@[expose] public section

/-! # Pilot: kernel cost of a few minimal-generation relations (scratch) -/


namespace HaagerupIzumi.C8
namespace LatticeVOA

set_option profiler true
set_option profiler.threshold 10
set_option Elab.async false

/-- Relation 0: source `['initial', 0]`, new basis vector `0`. -/
theorem s2rel_0 :
    Vec4.mode (Vec4.ofVec hL) (-2) (Vec4.ofVec vac) =
      Vec4.add (Vec4.smulQA (decQA [1, 1, 0, 1, 0, 1, 0, 1]) s2r_0)
      (combo []) := by
  decide +kernel

theorem s2scale_0 :
    QA.mul (decQA [1, 1, 0, 1, 0, 1, 0, 1]) (QA.inv (decQA [1, 1, 0, 1, 0, 1, 0, 1])) = QA.one := by
  decide +kernel

/-- Relation 6: source `['initial', 6]`, new basis vector `6`. -/
theorem s2rel_6 :
    Vec4.mode (Vec4.ofVec hL) (-1) (Vec4.ofVec hL) =
      Vec4.add (Vec4.smulQA (decQA [2, 1, 0, 1, 0, 1, 0, 1]) s2r_6)
      (combo []) := by
  decide +kernel

theorem s2scale_6 :
    QA.mul (decQA [2, 1, 0, 1, 0, 1, 0, 1]) (QA.inv (decQA [2, 1, 0, 1, 0, 1, 0, 1])) = QA.one := by
  decide +kernel

/-- Relation 42: source `['initial', 42]`, new basis vector `22`. -/
theorem s2rel_42 :
    Vec4.ofVec omega =
      Vec4.add (Vec4.smulQA (decQA [2, 1, 0, 1, 0, 1, 0, 1]) s2r_22)
      (combo [(decQA [4, 3, 0, 1, 0, 1, 0, 1], s2r_6), (decQA [1, 1, 0, 1, 0, 1, 0, 1], s2r_7), (decQA [2, 1, 0, 1, 0, 1, 0, 1], s2r_16)]) := by
  decide +kernel

theorem s2scale_42 :
    QA.mul (decQA [2, 1, 0, 1, 0, 1, 0, 1]) (QA.inv (decQA [2, 1, 0, 1, 0, 1, 0, 1])) = QA.one := by
  decide +kernel

/-- Relation 43: source `['initial', 43]`, new basis vector `23`. -/
theorem s2rel_43 :
    s2u =
      Vec4.add (Vec4.smulQA (decQA [2, 1, 0, 1, 0, 1, 0, 1]) s2r_23)
      (combo []) := by
  decide +kernel

theorem s2scale_43 :
    QA.mul (decQA [2, 1, 0, 1, 0, 1, 0, 1]) (QA.inv (decQA [2, 1, 0, 1, 0, 1, 0, 1])) = QA.one := by
  decide +kernel

/-- Relation 352: source `['op', 3, 61]`, new basis vector `65`. -/
theorem s2rel_352 :
    Vec4.mode (s2op 3) (s2opIdx 3) s2r_61 =
      Vec4.add (Vec4.smulQA (decQA [16, 1, 0, 1, 0, 1, 0, 1]) s2r_65)
      (combo [(decQA [0, 1, 10, 2, 29, 2, 0, 1], s2r_63), (decQA [0, 1, 19, 3, 20, 1, 0, 1], s2r_64), (decQA [14, 72, 10, 18, 9, 6, 2, 24], s2r_6), (decQA [42, 20, 25, 9, 26, 3, 18, 20], s2r_7), (decQA [195, 15, 10, 1, 29, 1, 27, 5], s2r_22), (decQA [13, 15, 8, 1, 23, 1, 1, 5], s2r_16), (decQA [154, 72, 10, 6, 9, 2, 22, 24], s2r_0), (decQA [153, 180, 1, 3, 2, 1, 21, 60], s2r_3)]) := by
  decide +kernel

theorem s2scale_352 :
    QA.mul (decQA [16, 1, 0, 1, 0, 1, 0, 1]) (QA.inv (decQA [16, 1, 0, 1, 0, 1, 0, 1])) = QA.one := by
  decide +kernel


end LatticeVOA
end HaagerupIzumi.C8
