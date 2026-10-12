module

public import HaagerupIzumi.C8.Lattice.ModeHH

@[expose] public section

/-!
# Replaying a mode identity on the triplet from per-chunk partial results

For the right-current controls of `hi_cft_20260923_next_structure_p4_controls.json`: the input
vector is cut into sub-chunks (`QVec`, spec `lean/tools/lattice_export/p4_chunks.py`), the image
of each sub-chunk is checked by kernel evaluation of `modeQRF` against exported data, and the
images are added up (`sum4`, balanced merging) and compared with the expected vector.

* `dropZero`, `nz4`: drop zero coefficients (`toV4_nz4`); `sum4`: sum of a list of `Vec4`s
  (`toV4_sum4`); `toVQ_flatten`.
* `ctl_pairs`: if every pair `(s, R)` satisfies `nz4 (sort4 (toVec4Q (modeQRF a m s))) = R`
  (and `s` has canonical states), then `modeC m (toV a) (∑ toVQ s) = ∑ toV4 R`.

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-- Drop the terms with coefficient zero. -/
def dropZero (v : Vec) : Vec := v.filter fun p => decide (p.2 ≠ 0)

theorem toV_dropZero : ∀ v : Vec, toV (dropZero v) = toV v
  | [] => rfl
  | (s, c) :: v => by
    have ih := toV_dropZero v
    by_cases hc : c = 0
    · rw [show dropZero ((s, c) :: v) = dropZero v by simp [dropZero, hc], ih, toV_cons_mk, hc,
        Rat.cast_zero, Finsupp.single_zero, zero_add]
    · rw [show dropZero ((s, c) :: v) = (s, c) :: dropZero v by simp [dropZero, hc], toV_cons_mk,
        toV_cons_mk, ih]

/-- Drop zero coefficients in all four components. -/
def nz4 (x : Vec4) : Vec4 := ⟨dropZero x.c0, dropZero x.c1, dropZero x.c2, dropZero x.c3⟩

theorem toV4_nz4 (x : Vec4) : toV4 (nz4 x) = toV4 x := by
  simp only [toV4, nz4, toV_dropZero]

/-- The sum of a list of `Vec4`s (balanced merging in each component). -/
def sum4 (l : List Vec4) : Vec4 :=
  ⟨mergeAll l.length (l.map Vec4.c0), mergeAll l.length (l.map Vec4.c1),
    mergeAll l.length (l.map Vec4.c2), mergeAll l.length (l.map Vec4.c3)⟩

theorem toV_mergeAll (fuel : ℕ) (l : List Vec) : toV (mergeAll fuel l) = (l.map toV).sum := by
  unfold toV
  rw [toFock_mergeAll, map_list_sum, List.map_map]
  rfl

theorem toV4_sum4 : ∀ l : List Vec4, toV4 (sum4 l) = (l.map toV4).sum := by
  intro l
  simp only [toV4, sum4, toV_mergeAll, List.map_map]
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
    rw [← ih]
    simp only [toV4, smul_add]
    abel

theorem toVQ_flatten : ∀ L : List QVec, toVQ L.flatten = (L.map toVQ).sum
  | [] => by simp [toVQ_nil]
  | x :: L => by rw [List.flatten_cons, toVQ_append, toVQ_flatten L, List.map_cons, List.sum_cons]

/-- **Assembly**: the per-chunk checks give the identity for the sum of the chunks. -/
theorem ctl_pairs (a : Vec) (ha : ∀ p ∈ a, Valid p.1) (m : ℤ) :
    ∀ pairs : List (QVec × Vec4),
      (∀ p ∈ pairs, (∀ q ∈ p.1, Valid q.1) ∧ nz4 (sort4 (toVec4Q (modeQRF a m p.1))) = p.2) →
      modeC m (toV a) (pairs.map fun p => toVQ p.1).sum = (pairs.map fun p => toV4 p.2).sum
  | [], _ => by simp
  | p :: pairs, h => by
    obtain ⟨hv, he⟩ := h p List.mem_cons_self
    have ih := ctl_pairs a ha m pairs fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.sum_cons]
    rw [map_add, ih, ← toVQ_modeQRF m a p.1 ha hv, ← toV4_toVec4Q, ← toV4_sort4, ← toV4_nz4, he]

/-- A data vector as the sum of its sub-chunks (from a kernel-checked normalization). -/
theorem toV4_eq_of_link {subs : List QVec} {x : Vec4}
    (h : nz4 (sort4 (toVec4Q subs.flatten)) = x) : toV4 x = (subs.map toVQ).sum := by
  rw [← h, toV4_nz4, toV4_sort4, toV4_toVec4Q, toVQ_flatten]

#print axioms ctl_pairs

end LatticeVOA
end HaagerupIzumi.C8
