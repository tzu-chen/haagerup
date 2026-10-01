module

public import HaagerupIzumi.C8.Properness.Lower

@[expose] public section

/-! # The full normal spaces equal the displayed spans

The manuscript (`haagerup_c8_expanded.tex`, line 2216) says that `N₃, N₄` "denote full
differential normal spaces, using the lower closure identities to reorder expressions".
Here this is proved: with `𝒩_d(S) = 𝒩(S) ∩ V_d` (Definition `def:normal-span`),

* `fullN₃_eq : 𝒩₃(K + S₂) = K₋₁S₂ + TS₂`,
* `fullN₄_eq : 𝒩₄(K + S₂ + S₃) = K₋₁S₃ + TS₃ + (S₂)₋₁S₂`,

from the lower identities only.  The method: the subspace `⨆_d P_d`, with `P_d` the expected
weight-`d` pieces (and all of `V_d` above the relevant weight), contains the generators and
the vacuum and is closed under `T` and `(-1)`-products (skew symmetry handles the reversed
products); hence it contains the normal span, and the independence of the grading extracts
the weight-`d` part.  Consequently every certificate membership in a full normal space (the
lattice solver's words are arbitrary normal words) is a membership in the displayed spans used
in the rest of the development.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace VertexAlgebra

variable (A : VertexAlgebra k V)

/-- If graded pieces `P d ⊂ V_d` contain the vacuum and the generators and are closed under
`T` and `(-1)`-products, then the weight-`d` part of the normal span lies in `P d`. -/
theorem normalSpan_inf_grade_le {G : Set V} (P : ℕ → Submodule k V)
    (hPg : ∀ d, P d ≤ A.grade d) (hvac : A.vac ∈ P 0) (hG : ∀ g ∈ G, ∃ d, g ∈ P d)
    (hT : ∀ d, ∀ x ∈ P d, A.T x ∈ P (d + 1))
    (hprod : ∀ i j, ∀ x ∈ P i, ∀ y ∈ P j, A.mode (-1) x y ∈ P (i + j)) (d : ℕ) :
    A.normalSpan G ⊓ A.grade d ≤ P d := by
  have hZ : A.normalSpan G ≤ ⨆ e, P e := by
    refine A.normalSpan_le (Submodule.mem_iSup_of_mem 0 hvac) ?_ ?_ ?_
    · intro g hg
      obtain ⟨e, he⟩ := hG g hg
      exact Submodule.mem_iSup_of_mem e he
    · intro x hx
      refine Submodule.iSup_induction P (motive := fun x => A.T x ∈ ⨆ e, P e) hx ?_ ?_ ?_
      · intro e x hx
        exact Submodule.mem_iSup_of_mem (e + 1) (hT e x hx)
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    · intro x hx y hy
      refine Submodule.iSup_induction P (motive := fun x => A.mode (-1) x y ∈ ⨆ e, P e) hx
        ?_ ?_ ?_
      · intro i x hx
        refine Submodule.iSup_induction P (motive := fun y => A.mode (-1) x y ∈ ⨆ e, P e) hy
          ?_ ?_ ?_
        · intro j y hy
          exact Submodule.mem_iSup_of_mem (i + j) (hprod i j x hx y hy)
        · rw [map_zero]
          exact Submodule.zero_mem _
        · intro y₁ y₂ h₁ h₂
          rw [map_add]
          exact Submodule.add_mem _ h₁ h₂
      · rw [map_zero, LinearMap.zero_apply]
        exact Submodule.zero_mem _
      · intro x₁ x₂ h₁ h₂
        rw [map_add, LinearMap.add_apply]
        exact Submodule.add_mem _ h₁ h₂
  intro x hx
  obtain ⟨hxZ, hxd⟩ := Submodule.mem_inf.mp hx
  have hxZ' := hZ hxZ
  rw [iSup_split_single P d] at hxZ'
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxZ'
  have hz0 : z = 0 := by
    have hzd : z ∈ A.grade d := by
      have h := Submodule.sub_mem _ hxd (hPg d hy)
      rwa [add_sub_cancel_left] at h
    have hzo : z ∈ ⨆ (e) (_ : e ≠ d), A.grade e :=
      (iSup₂_mono fun e _ => hPg e) hz
    exact (Submodule.disjoint_def.mp (A.grade_internal.submodule_iSupIndep d)) z hzd hzo
  rw [hz0, add_zero]
  exact hy

theorem T_pow_mem_family (P : ℕ → Submodule k V) (hT : ∀ d, ∀ x ∈ P d, A.T x ∈ P (d + 1)) :
    ∀ t d, ∀ x ∈ P d, (A.T ^ t) x ∈ P (d + t)
  | 0, d, x, hx => by simpa using hx
  | t + 1, d, x, hx => by
      rw [pow_succ', Module.End.mul_apply]
      have := hT (d + t) _ (T_pow_mem_family P hT t d x hx)
      rwa [show d + t + 1 = d + (t + 1) by omega] at this

/-- Reordering a normal product inside a graded family closed under `T`. -/
theorem reorder_mem_family (P : ℕ → Submodule k V) (hT : ∀ d, ∀ x ∈ P d, A.T x ∈ P (d + 1))
    {w e : ℕ} {x y : V} (hx : x ∈ A.grade w) (hy : y ∈ A.grade e)
    (h0 : A.mode (-1) x y ∈ P (w + e))
    (hsing : ∀ m : ℕ, m < w + e → A.mode (m : ℤ) x y ∈ P (w + e - m - 1)) :
    A.mode (-1) y x ∈ P (w + e) := by
  refine A.skew_mem hx hy (-1) fun t ht => ?_
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simpa using h0
  · have ht' : t ≤ w + e := by simp at ht; omega
    have := A.T_pow_mem_family P hT t _ _ (hsing (t - 1) (by omega))
    rw [show w + e - (t - 1) - 1 + t = w + e by omega] at this
    rw [show (-1 : ℤ) + t = ((t - 1 : ℕ) : ℤ) by omega]
    exact this

end VertexAlgebra

namespace ClosureData

variable {A : VertexOperatorAlgebra k V} (D : ClosureData A)

/-- Expected weight pieces below weight four. -/
def piece₃ : ℕ → Submodule k V
  | 0 => A.grade 0
  | 1 => D.K
  | 2 => D.S₂
  | 3 => D.N₃
  | d + 4 => A.grade (d + 4)

/-- Expected weight pieces below weight five. -/
def piece₄ : ℕ → Submodule k V
  | 0 => A.grade 0
  | 1 => D.K
  | 2 => D.S₂
  | 3 => D.S₃
  | 4 => D.N₄
  | d + 5 => A.grade (d + 5)

theorem piece₃_grade : ∀ d, D.piece₃ d ≤ A.grade d
  | 0 => le_rfl
  | 1 => D.K_grade
  | 2 => D.S₂_grade
  | 3 => D.N₃_grade
  | _ + 4 => le_rfl

theorem piece₄_grade : ∀ d, D.piece₄ d ≤ A.grade d
  | 0 => le_rfl
  | 1 => D.K_grade
  | 2 => D.S₂_grade
  | 3 => D.S₃_grade
  | 4 => D.N₄_grade
  | _ + 5 => le_rfl

theorem vac_mem_grade_zero : A.vac ∈ A.grade 0 := by
  rw [A.grade_zero]
  exact Submodule.mem_span_singleton_self _

theorem N₃_le_fullN₃ : D.N₃ ≤ D.fullN₃ := by
  refine le_inf (sup_le (VertexAlgebra.negProd_le fun x hx a ha => ?_)
    (VertexAlgebra.map_T_le fun a ha => ?_)) D.N₃_grade
  · exact A.prod_mem_normalSpan (A.subset_normalSpan _ (Or.inl hx))
      (A.subset_normalSpan _ (Or.inr ha))
  · exact A.T_mem_normalSpan (A.subset_normalSpan _ (Or.inr ha))

theorem N₄_le_fullN₄ : D.N₄ ≤ D.fullN₄ := by
  refine le_inf (sup_le (sup_le (VertexAlgebra.negProd_le fun x hx s hs => ?_)
    (VertexAlgebra.map_T_le fun s hs => ?_)) (VertexAlgebra.negProd_le fun a ha b hb => ?_))
    D.N₄_grade
  · exact A.prod_mem_normalSpan (A.subset_normalSpan _ (Or.inl (Or.inl hx)))
      (A.subset_normalSpan _ (Or.inr hs))
  · exact A.T_mem_normalSpan (A.subset_normalSpan _ (Or.inr hs))
  · exact A.prod_mem_normalSpan (A.subset_normalSpan _ (Or.inl (Or.inr ha)))
      (A.subset_normalSpan _ (Or.inl (Or.inr hb)))

end ClosureData

namespace LowerCertificate

variable [CharZero k] {A : VertexOperatorAlgebra k V} {D : ClosureData A}
variable (L : LowerCertificate D)
include L

theorem piece₃_T : ∀ d, ∀ x ∈ D.piece₃ d, A.T x ∈ D.piece₃ (d + 1)
  | 0, x, hx => by
      show A.T x ∈ D.K
      rw [A.T_grade_zero hx]
      exact Submodule.zero_mem _
  | 1, x, hx => L.TK x hx
  | 2, _, hx => D.N₃_of_T hx
  | 3, _, hx => A.T_grade (D.N₃_grade hx)
  | _ + 4, _, hx => A.T_grade hx

theorem piece₄_T : ∀ d, ∀ x ∈ D.piece₄ d, A.T x ∈ D.piece₄ (d + 1)
  | 0, x, hx => by
      show A.T x ∈ D.K
      rw [A.T_grade_zero hx]
      exact Submodule.zero_mem _
  | 1, x, hx => L.TK x hx
  | 2, _, hx => L.N₃_le_S₃ (D.N₃_of_T hx)
  | 3, _, hx => D.N₄_of_T hx
  | 4, _, hx => A.T_grade (D.N₄_grade hx)
  | _ + 5, _, hx => A.T_grade hx

/-- `(-1)`-products of the pieces at weight zero. -/
theorem piece_prod_zero_left (P : ℕ → Submodule k V) (hP0 : P 0 = A.grade 0) {j : ℕ}
    {x y : V} (hx : x ∈ P 0) (hy : y ∈ P j) : A.mode (-1) x y ∈ P (0 + j) := by
  rw [hP0] at hx
  obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left hx y
  rw [hr, zero_add]
  exact (P j).smul_mem r hy

theorem piece_prod_zero_right (P : ℕ → Submodule k V) (hP0 : P 0 = A.grade 0) {i : ℕ}
    {x y : V} (hx : x ∈ P i) (hy : y ∈ P 0) : A.mode (-1) x y ∈ P (i + 0) := by
  rw [hP0] at hy
  obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_right hy x
  rw [hr, add_zero]
  exact (P i).smul_mem r hx

theorem piece₃_prod : ∀ i j, ∀ x ∈ D.piece₃ i, ∀ y ∈ D.piece₃ j,
    A.mode (-1) x y ∈ D.piece₃ (i + j) := by
  intro i j x hx y hy
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact L.piece_prod_zero_left D.piece₃ rfl hx hy
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact L.piece_prod_zero_right D.piece₃ rfl hx hy
  by_cases h4 : 4 ≤ i + j
  · obtain ⟨d, hd⟩ : ∃ d, i + j = d + 4 := ⟨i + j - 4, by omega⟩
    rw [hd]
    exact A.mode_mem_grade (D.piece₃_grade i hx) (D.piece₃_grade j hy) (by push_cast; omega)
  · have hi' : i = 1 ∨ i = 2 := by omega
    have hj' : j = 1 ∨ j = 2 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact L.KmK x hx y hy
    · exact D.N₃_of_K_S₂ hx hy
    · -- reorder `a₋₁k` with `a ∈ S₂`, `k ∈ K`
      refine A.reorder_mem_family D.piece₃ L.piece₃_T (w := 1) (e := 2) (D.K_grade hy)
        (D.S₂_grade hx)
        (D.N₃_of_K_S₂ hy hx) fun m hm => ?_
      interval_cases m
      · exact L.KS₂0 y hy x hx
      · exact L.KS₂1 y hy x hx
      · exact A.mode_mem_grade (D.K_grade hy) (D.S₂_grade hx) (by norm_num)
    · exact (h4 (by norm_num)).elim

theorem piece₄_prod : ∀ i j, ∀ x ∈ D.piece₄ i, ∀ y ∈ D.piece₄ j,
    A.mode (-1) x y ∈ D.piece₄ (i + j) := by
  intro i j x hx y hy
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact L.piece_prod_zero_left D.piece₄ rfl hx hy
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact L.piece_prod_zero_right D.piece₄ rfl hx hy
  by_cases h5 : 5 ≤ i + j
  · obtain ⟨d, hd⟩ : ∃ d, i + j = d + 5 := ⟨i + j - 5, by omega⟩
    rw [hd]
    exact A.mode_mem_grade (D.piece₄_grade i hx) (D.piece₄_grade j hy) (by push_cast; omega)
  · have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
    · exact L.KmK x hx y hy
    · exact L.N₃_le_S₃ (D.N₃_of_K_S₂ hx hy)
    · exact D.N₄_of_K_S₃ hx hy
    · exact L.S₂mK hx hy
    · exact D.N₄_of_S₂_S₂ hx hy
    · exact (h5 (by norm_num)).elim
    · -- reorder `s₋₁k` with `s ∈ S₃`, `k ∈ K`
      refine A.reorder_mem_family D.piece₄ L.piece₄_T (w := 1) (e := 3) (D.K_grade hy)
        (D.S₃_grade hx)
        (D.N₄_of_K_S₃ hy hx) fun m hm => ?_
      interval_cases m
      · exact L.KS₃0 hy x hx
      · exact L.KS₃1 hy x hx
      · exact L.KS₃2 hy hx
      · exact A.mode_mem_grade (D.K_grade hy) (D.S₃_grade hx) (by norm_num)
    · exact (h5 (by norm_num)).elim
    · exact (h5 (by norm_num)).elim

/-- `𝒩₃(K + S₂) ⊂ K₋₁S₂ + TS₂`. -/
theorem fullN₃_le : D.fullN₃ ≤ D.N₃ :=
  A.normalSpan_inf_grade_le (G := (D.K : Set V) ∪ D.S₂) D.piece₃ D.piece₃_grade
    ClosureData.vac_mem_grade_zero (fun _ hg => hg.elim (fun h => ⟨1, h⟩) fun h => ⟨2, h⟩)
    L.piece₃_T L.piece₃_prod 3

/-- `𝒩₄(K + S₂ + S₃) ⊂ K₋₁S₃ + TS₃ + (S₂)₋₁S₂`. -/
theorem fullN₄_le : D.fullN₄ ≤ D.N₄ :=
  A.normalSpan_inf_grade_le (G := (D.K : Set V) ∪ D.S₂ ∪ D.S₃) D.piece₄ D.piece₄_grade
    ClosureData.vac_mem_grade_zero
    (fun _ hg => hg.elim (fun h => h.elim (fun h => ⟨1, h⟩) fun h => ⟨2, h⟩) fun h => ⟨3, h⟩)
    L.piece₄_T L.piece₄_prod 4

theorem fullN₃_eq : D.fullN₃ = D.N₃ := le_antisymm L.fullN₃_le D.N₃_le_fullN₃

theorem fullN₄_eq : D.fullN₄ = D.N₄ := le_antisymm L.fullN₄_le D.N₄_le_fullN₄

/-- `P₄ ⊂ (S₂)₀S₃ + N₄` with the displayed `N₄`. -/
theorem P₄_prov' : D.P₄ ≤ A.zeroProd D.S₂ D.S₃ ⊔ D.N₄ :=
  L.P₄_prov.trans (sup_le_sup_left L.fullN₄_le _)

/-- A membership in `𝒩₄(K + S₂ + S₃) + P₄` is a membership in `W₄`. -/
theorem W₄_of_full {x : V} (hx : x ∈ D.fullN₄ ⊔ D.P₄) : x ∈ D.W₄ :=
  sup_le_sup_right L.fullN₄_le _ hx

end LowerCertificate

#print axioms VertexAlgebra.normalSpan_inf_grade_le
#print axioms LowerCertificate.fullN₃_eq
#print axioms LowerCertificate.fullN₄_eq

end HaagerupIzumi.C8
