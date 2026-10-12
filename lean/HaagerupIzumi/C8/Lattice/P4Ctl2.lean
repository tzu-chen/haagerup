module

public import HaagerupIzumi.C8.Lattice.P4Ctl

@[expose] public section

/-!
# Concatenation of vectors, for merge checks by output-state ranges

The partial images of a control are cut (as data) into pieces by ranges of output states; each
merge check adds up one piece of every image, and `cat4` reassembles images and the expected
vector from their pieces (`toV4_cat4`).  `vec4_ext`: equality from the four components (for
link checks split by component).  No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- Concatenation, component by component. -/
def cat4 (l : List Vec4) : Vec4 :=
  ⟨(l.map Vec4.c0).flatten, (l.map Vec4.c1).flatten, (l.map Vec4.c2).flatten,
    (l.map Vec4.c3).flatten⟩

theorem toV_append (a b : Vec) : toV (a ++ b) = toV a + toV b := by
  unfold toV toFock
  rw [List.map_append, List.sum_append, map_add]

theorem toV_flatten : ∀ L : List Vec, toV L.flatten = (L.map toV).sum
  | [] => by simp
  | v :: L => by rw [List.flatten_cons, toV_append, toV_flatten L, List.map_cons, List.sum_cons]

theorem toV4_cat4 (l : List Vec4) : toV4 (cat4 l) = (l.map toV4).sum := by
  simp only [toV4, cat4, toV_flatten, List.map_map]
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
    rw [← ih]
    simp only [toV4, smul_add]
    abel

theorem vec4_ext {x y : Vec4} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2)
    (h3 : x.c3 = y.c3) : x = y := by
  cases x
  cases y
  simp_all

#print axioms toV4_cat4

end LatticeVOA
end HaagerupIzumi.C8
