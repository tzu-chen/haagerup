module

public import HaagerupIzumi.C8.MainProperness

@[expose] public section

/-!
# The graded-piece part of Corollary `cor:initial-grades`: `U₂ = S₂` and `U₃ = S₃`

Proof in the manuscript (lines 2599–2603): "A differential normal word of weight two uses only
`K` and `S₂`; its current descendants are already in `S₂`.  A word of weight three uses only
`K, S₂, S₃`, and the lower normal words lie in `N₃`.  Thus the strong-generation result proves
`U₂ = S₂` and `U₃ = S₃`."

Only the graded-piece assertions are formalized here; simplicity and unitarity (the PCT
certificate with CKLW Proposition 5.29), the central charge `8`, and the character coefficients
(`dim S₂ = 120`, `dim S₃ = 956`) are not.  The equalities are derived from `prop_mainproper` (`U = 𝒩(K, S₂, S₃, P₄)`), the graded description
`normalSpan ⊓ V_d = S_d ⊔ derivProdSpan d` of the normal span, and the certificate fields
`TK`, `KmK` (the 22 affine vacuum vectors lie in `S₂`), `N₃ ≤ S₃`, and the reordering
`(S₂)₍₋₁₎K ⊂ S₃` (`LowerCertificate.S₂mK`).
-/

namespace HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

open ClosureData

/-- Weight-one normal words of the closure family span `K`. -/
theorem wordSpan_family_one (D : ClosureData A) :
    A.toVertexAlgebra.wordSpan (⋃ e, (D.family e : Set V)) 1 = D.K := by
  rw [← A.toVertexAlgebra.normalSpan_inf_grade
    (A.toVertexAlgebra.homogeneous_iUnion D.family_grade) 1]
  exact A.toVertexAlgebra.normalSpan_iUnion_inf_grade_one D.family_grade

/-- A derivative/product word of weight `d` lies in `Z` once the derivatives and products of
lower-weight words do. -/
theorem derivProd_le (D : ClosureData A) {d : ℕ} {Z : Submodule k V}
    (hT : ∀ e, e + 1 = d → ∀ y ∈ A.toVertexAlgebra.wordSpan (⋃ e, (D.family e : Set V)) e,
      A.T y ∈ Z)
    (hP : ∀ i j, 0 < i → 0 < j → i + j = d →
      ∀ y ∈ A.toVertexAlgebra.wordSpan (⋃ e, (D.family e : Set V)) i,
      ∀ z ∈ A.toVertexAlgebra.wordSpan (⋃ e, (D.family e : Set V)) j, A.mode (-1) y z ∈ Z) :
    A.toVertexAlgebra.derivProdSpan (⋃ e, (D.family e : Set V)) d ≤ Z := by
  rw [VertexAlgebra.derivProdSpan, Submodule.span_le]
  intro x hx
  cases hx with
  | deriv hy => exact hT _ rfl _ hy
  | prod hi hj hy hz => exact hP _ _ hi hj rfl _ hy _ hz

/-- The weight-two normal span of the family is `S₂`. -/
theorem normalSpan_family_two (D : ClosureData A) (L : LowerCertificate D) :
    A.normalSpan (⋃ e, (D.family e : Set V)) ⊓ A.grade 2 = D.S₂ := by
  rw [A.toVertexAlgebra.normalSpan_iUnion_inf_grade D.family_grade (by norm_num : (2 : ℕ) ≠ 0)]
  refine le_antisymm (sup_le le_rfl ?_) le_sup_left
  apply derivProd_le D
  · intro e he y hy
    obtain rfl : e = 1 := by omega
    rw [wordSpan_family_one] at hy
    exact L.TK y hy
  · intro i j hi hj hij y hy z hz
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 1 := by omega
    rw [wordSpan_family_one] at hy hz
    exact L.KmK y hy z hz

theorem wordSpan_family_two (D : ClosureData A) (L : LowerCertificate D) :
    A.toVertexAlgebra.wordSpan (⋃ e, (D.family e : Set V)) 2 = D.S₂ := by
  rw [← A.toVertexAlgebra.normalSpan_inf_grade
    (A.toVertexAlgebra.homogeneous_iUnion D.family_grade) 2]
  exact normalSpan_family_two D L

/-- The weight-three normal span of the family is `S₃`. -/
theorem normalSpan_family_three (D : ClosureData A) (L : LowerCertificate D) :
    A.normalSpan (⋃ e, (D.family e : Set V)) ⊓ A.grade 3 = D.S₃ := by
  rw [A.toVertexAlgebra.normalSpan_iUnion_inf_grade D.family_grade (by norm_num : (3 : ℕ) ≠ 0)]
  refine le_antisymm (sup_le le_rfl ?_) le_sup_left
  apply derivProd_le D
  · intro e he y hy
    obtain rfl : e = 2 := by omega
    rw [wordSpan_family_two D L] at hy
    exact L.N₃_le_S₃ (D.N₃_of_T hy)
  · intro i j hi hj hij y hy z hz
    rcases (by omega : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [wordSpan_family_one] at hy
      rw [wordSpan_family_two D L] at hz
      exact L.N₃_le_S₃ (D.N₃_of_K_S₂ hy hz)
    · rw [wordSpan_family_two D L] at hy
      rw [wordSpan_family_one] at hz
      exact L.S₂mK hy hz

/-- **Corollary `cor:initial-grades`, graded pieces.**  If `U` is the normal span of `K, S₂, S₃, P₄` (as proved
in `prop_mainproper`), then `U₂ = S₂` and `U₃ = S₃`. -/
theorem cor_initial_grades (D : ClosureData A) (L : LowerCertificate D) (u : V)
    (hU : D.U u = A.normalSpan (⋃ d, (D.family d : Set V))) :
    D.U u ⊓ A.grade 2 = D.S₂ ∧ D.U u ⊓ A.grade 3 = D.S₃ := by
  rw [hU]
  exact ⟨normalSpan_family_two D L, normalSpan_family_three D L⟩

/-- The corollary under the hypotheses of `prop_mainproper`. -/
theorem cor_initial_grades_of_certificates (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (hnilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.eL) (A.mode 0 D.eR) w v = 0)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0)
    (u : V) (hω : A.ω ∈ D.S₂) (hu : u ∈ D.S₂) (hmin : D.S₂ ≤ D.U u) :
    D.U u ⊓ A.grade 1 = D.K ∧ D.U u ⊓ A.grade 2 = D.S₂ ∧ D.U u ⊓ A.grade 3 = D.S₃ := by
  obtain ⟨hU, h1⟩ := prop_mainproper D L G G5 hnilE hnilF u hω hu hmin
  exact ⟨h1, cor_initial_grades D L u hU⟩

#print axioms cor_initial_grades_of_certificates

end HaagerupIzumi.C8
