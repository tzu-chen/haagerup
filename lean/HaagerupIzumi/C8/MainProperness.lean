module

public import HaagerupIzumi.C8.Properness.Final
public import HaagerupIzumi.C8.VertexAlgebra.Recursive
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# Proposition `prop:mainproper`: strong generation, `U₁ = K`, and `U ⊊ B`

This file assembles the properness proof of the manuscript (lines 215–223 and 2578–2597 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) from

* the closure hypotheses (1), (2) for the family `K, S₂, S₃, P₄`
  (`closure_hypothesis_one`, `closure_hypothesis_two`, which derive Gates 4 and 5 from the
  finite certificates `LowerCertificate`, `Gate4Certificate`, `Gate5Certificate` and the
  nilpotence of raising/lowering words);
* the recursive strong-generation criterion `recursive_strong_generation`
  (Theorem `thm:recursive`, via Lemma `lem:filtered-wick`);
* the minimal-generation certificate (`hmin`: every vector of the saved `S₂` is an actual
  vector of `U = ⟨K, ω_B, u⟩`; ledger record `hi_cft_20260923_c8_minimal_generators.json`).

`A` is the lattice VOA `B = V_{E₆ ⊕ A₂}` presented through the interface
`VertexOperatorAlgebra` (its fields are derived from the Borcherds identity in
`VertexAlgebra/Borcherds.lean`).

Main results:
* `generated_eq_family`: `⟨K, ω, u⟩ = ⟨K ∪ S₂ ∪ S₃ ∪ P₄⟩`;
* `prop_mainproper`: `U` equals the differential normal span of `K, S₂, S₃, P₄` (strong
  generation by fields of weight at most four) and `U ∩ B₁ = K`;
* `prop_mainproper_proper`: with `dim K = 6` and `dim B₁ = 86`, `U ≠ B`.
-/

namespace HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

namespace ClosureData

variable (D : ClosureData A)

/-- The short generating set `K ∪ {ω_B, u}` of eq:U. -/
def gens (u : V) : Set V := D.currents ∪ {A.ω, u}

/-- The actual generated vertex algebra `U = ⟨𝒦, ω_B, u⟩ ⊂ B` (eq:U). -/
def U (u : V) : Submodule k V := A.toVertexAlgebra.generated (D.gens u)

end ClosureData

open ClosureData

/-- Every member of the closure family lies in `U`, given minimal generation. -/
theorem family_le_U (D : ClosureData A) (L : LowerCertificate D) (u : V)
    (hmin : D.S₂ ≤ D.U u) : ∀ d, D.family d ≤ D.U u := by
  have hsub := A.toVertexAlgebra.generated_isSubalgebra (D.gens u)
  have hK : D.K ≤ D.U u := Submodule.span_le.2 fun x hx =>
    A.toVertexAlgebra.subset_generated _ (Or.inl hx)
  -- the normal span of a family inside `U` lies in `U`
  have hN : ∀ X : Set V, X ⊆ (D.U u : Set V) → A.normalSpan X ≤ D.U u := fun X hX =>
    (A.toVertexAlgebra.normalSpan_le_generated X).trans (A.toVertexAlgebra.generated_le hsub hX)
  have hspan : ∀ P Q : Submodule k V, P ≤ D.U u → Q ≤ D.U u →
      Submodule.span k {x | ∃ a ∈ P, ∃ b ∈ Q, x = A.mode 0 a b} ≤ D.U u := by
    intro P Q hP hQ
    rw [Submodule.span_le]
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact hsub.2 0 a (hP ha) b (hQ hb)
  have h12 : D.family 1 ≤ D.U u ∧ D.family 2 ≤ D.U u := ⟨hK, hmin⟩
  have h3 : D.family 3 ≤ D.U u := by
    refine (closure_hypothesis_two D L 3 le_rfl (by norm_num)).trans (sup_le ?_ ?_)
    · exact hspan _ _ h12.2 h12.2
    · refine inf_le_left.trans (hN _ ?_)
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨e, he, hx⟩ := hx
      match e, he, hx with
      | 0, _, hx => exact ((Submodule.mem_bot k).1 hx) ▸ Submodule.zero_mem _
      | 1, _, hx => exact h12.1 hx
      | 2, _, hx => exact h12.2 hx
  have h4 : D.family 4 ≤ D.U u := by
    refine (closure_hypothesis_two D L 4 (by norm_num) le_rfl).trans (sup_le ?_ ?_)
    · exact hspan _ _ h12.2 h3
    · refine inf_le_left.trans (hN _ ?_)
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨e, he, hx⟩ := hx
      match e, he, hx with
      | 0, _, hx => exact ((Submodule.mem_bot k).1 hx) ▸ Submodule.zero_mem _
      | 1, _, hx => exact h12.1 hx
      | 2, _, hx => exact h12.2 hx
      | 3, _, hx => exact h3 hx
  intro d
  match d with
  | 0 => exact bot_le
  | 1 => exact h12.1
  | 2 => exact h12.2
  | 3 => exact h3
  | 4 => exact h4
  | _ + 5 => exact bot_le

/-- `⟨K, ω, u⟩ = ⟨K ∪ S₂ ∪ S₃ ∪ P₄⟩`. -/
theorem generated_eq_family (D : ClosureData A) (L : LowerCertificate D) (u : V)
    (hω : A.ω ∈ D.S₂) (hu : u ∈ D.S₂) (hmin : D.S₂ ≤ D.U u) :
    D.U u = A.toVertexAlgebra.generated (⋃ d, (D.family d : Set V)) := by
  apply le_antisymm
  · apply A.toVertexAlgebra.generated_le (A.toVertexAlgebra.generated_isSubalgebra _)
    rintro x (hx | hx)
    · exact A.toVertexAlgebra.subset_generated _
        (Set.mem_iUnion.2 ⟨1, Submodule.subset_span hx⟩)
    · rcases hx with rfl | rfl
      · exact A.toVertexAlgebra.subset_generated _ (Set.mem_iUnion.2 ⟨2, hω⟩)
      · exact A.toVertexAlgebra.subset_generated _ (Set.mem_iUnion.2 ⟨2, hu⟩)
  · apply A.toVertexAlgebra.generated_le (A.toVertexAlgebra.generated_isSubalgebra _)
    intro x hx
    obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hx
    exact family_le_U D L u hmin d hd

/-- **Proposition `prop:mainproper`** (strong generation and `U₁ = K`).  Under the finite
certificates, `U = ⟨K, ω_B, u⟩` is the differential normal span of the actual fields
`K, S₂, S₃, P₄` (weights `≤ 4`), and its weight-one space is `K = 𝔰𝔩₂ ⊕ 𝔰𝔩₂`. -/
theorem prop_mainproper (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (hnilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.eL) (A.mode 0 D.eR) w v = 0)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0)
    (u : V) (hω : A.ω ∈ D.S₂) (hu : u ∈ D.S₂) (hmin : D.S₂ ≤ D.U u) :
    D.U u = A.normalSpan (⋃ d, (D.family d : Set V)) ∧ D.U u ⊓ A.grade 1 = D.K := by
  obtain ⟨_, hgen, hone⟩ := A.toVertexAlgebra.recursive_strong_generation D.family 4
    (closure_family_grade D) (closure_family_top D)
    (closure_hypothesis_one D L G G5 hnilE hnilF) (closure_hypothesis_two D L)
  rw [generated_eq_family D L u hω hu hmin]
  exact ⟨hgen, hone⟩

/-- **Properness**: `U ⊊ B`, since `dim U₁ = dim K = 6` while `dim B₁ = 86`. -/
theorem prop_mainproper_proper (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (hnilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.eL) (A.mode 0 D.eR) w v = 0)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0)
    (u : V) (hω : A.ω ∈ D.S₂) (hu : u ∈ D.S₂) (hmin : D.S₂ ≤ D.U u)
    (hdimK : Module.finrank k D.K = 6) (hdimB : Module.finrank k (A.grade 1) = 86) :
    D.U u ≠ ⊤ := by
  intro htop
  have h1 := (prop_mainproper D L G G5 hnilE hnilF u hω hu hmin).2
  rw [htop, top_inf_eq] at h1
  have : Module.finrank k (A.grade 1) = Module.finrank k D.K := by rw [h1]
  omega

#print axioms prop_mainproper
#print axioms prop_mainproper_proper

end HaagerupIzumi.C8
