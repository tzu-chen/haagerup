module

public import HaagerupIzumi.C8.Properness.Gate5

@[expose] public section

/-! # The hypotheses of the recursive strong-generation criterion

Formalizes Section `sec:properness` of `c8_expanded_20260929/haagerup_c8_expanded.tex`
(lines 2578–2597): for the family `S 1 = K`, `S 2 = S₂`, `S 3 = S₃`, `S 4 = P₄` (zero
otherwise, `h = 4`) and `𝒩 = A.normalSpan (⋃ d, S d)`,

* `closure_hypothesis_one`: hypothesis 1 of Theorem `thm:recursive`, `x_(n) s ∈ 𝒩` for
  `x ∈ S 1 ∪ S 2`, `s ∈ S d`, `n ≥ 0`;
* `closure_hypothesis_two`: hypothesis 2, `S d ⊂ span{a₀b : a ∈ S 2, b ∈ S (d-1)} + 𝒩_d(S_{<d})`
  for `3 ≤ d ≤ 4`;
* `closure_family_grade`, `closure_family_top`: the grading hypotheses.

The statements match `HaagerupIzumi.C8.VertexAlgebra.recursive_strong_generation`
(`C8/VertexAlgebra/Recursive.lean`, owned by another agent) applied to `A.toVertexAlgebra`.

Inputs: `LowerCertificate D`, `Gate4Certificate D`, `Gate5Certificate D G` (finite exact
certificates, see their docstrings) and the two nilpotence statements `hnilE`, `hnilF`
(words of length 25 in the raising, resp. lowering, current zero modes vanish on `S₃`;
Lemma `lem:current-bounds`, lines 2224–2236 and 2289–2295).  Gates 4 and 5 are proved, not
assumed.  The positive modes on `P₄` are the four displayed identities of lines 2584–2588.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

namespace ClosureData

variable (D : ClosureData A)

/-- The generator family of Theorem `thm:recursive` with `h = 4`. -/
def family : ℕ → Submodule k V
  | 1 => D.K
  | 2 => D.S₂
  | 3 => D.S₃
  | 4 => D.P₄
  | _ => ⊥

theorem family_grade : ∀ d, D.family d ≤ A.grade d
  | 0 => bot_le
  | 1 => D.K_grade
  | 2 => D.S₂_grade
  | 3 => D.S₃_grade
  | 4 => D.P₄_grade
  | _ + 5 => bot_le

theorem family_top : ∀ d, 4 < d → D.family d = ⊥
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, h => absurd h (by omega)
  | 3, h => absurd h (by omega)
  | 4, h => absurd h (by omega)
  | _ + 5, _ => rfl

/-- The differential normal span `𝒩` of the family. -/
abbrev normal : Submodule k V := A.normalSpan (⋃ e, (D.family e : Set V))

theorem mem_normal {d : ℕ} {x : V} (hx : x ∈ D.family d) : x ∈ D.normal :=
  A.subset_normalSpan _ (Set.mem_iUnion.mpr ⟨d, hx⟩)

theorem grade_zero_le_normal : A.grade 0 ≤ D.normal := by
  intro x hx
  obtain ⟨r, rfl⟩ := A.exists_smul_vac hx
  exact Submodule.smul_mem _ r (A.vac_mem_normalSpan _)

/-- Normal words in elements of a normal span stay in it. -/
theorem negProd_le_normalSpan {G : Set V} {X Y : Submodule k V} (hX : X ≤ A.normalSpan G)
    (hY : Y ≤ A.normalSpan G) : A.negProd X Y ≤ A.normalSpan G :=
  VertexAlgebra.negProd_le fun _ hx _ hy => A.prod_mem_normalSpan (hX hx) (hY hy)

theorem map_T_le_normalSpan {G : Set V} {X : Submodule k V} (hX : X ≤ A.normalSpan G) :
    X.map A.T ≤ A.normalSpan G :=
  VertexAlgebra.map_T_le fun _ hx => A.T_mem_normalSpan (hX hx)

theorem K_le_normal : D.K ≤ D.normal := fun _ hx => D.mem_normal (d := 1) hx
theorem S₂_le_normal : D.S₂ ≤ D.normal := fun _ hx => D.mem_normal (d := 2) hx
theorem S₃_le_normal : D.S₃ ≤ D.normal := fun _ hx => D.mem_normal (d := 3) hx
theorem P₄_le_normal : D.P₄ ≤ D.normal := fun _ hx => D.mem_normal (d := 4) hx

theorem N₄_le_normal : D.N₄ ≤ D.normal :=
  sup_le (sup_le (negProd_le_normalSpan D.K_le_normal D.S₃_le_normal)
    (map_T_le_normalSpan D.S₃_le_normal)) (negProd_le_normalSpan D.S₂_le_normal D.S₂_le_normal)

theorem W₄_le_normal : D.W₄ ≤ D.normal := sup_le D.N₄_le_normal D.P₄_le_normal

theorem N₅_le_normal : D.N₅ ≤ D.normal :=
  sup_le (sup_le (negProd_le_normalSpan D.K_le_normal D.W₄_le_normal)
    (map_T_le_normalSpan D.W₄_le_normal)) (negProd_le_normalSpan D.S₂_le_normal D.S₃_le_normal)

theorem ladder_le_normal : ∀ d : ℕ, d ≤ 5 → D.ladder d ≤ D.normal
  | 0, _ => D.grade_zero_le_normal
  | 1, _ => D.K_le_normal
  | 2, _ => D.S₂_le_normal
  | 3, _ => D.S₃_le_normal
  | 4, _ => D.W₄_le_normal
  | 5, _ => D.N₅_le_normal
  | _ + 6, h => absurd h (by omega)

/-- If the singular products `x_(m) s` lie in the ladder at their weights, all nonnegative
modes `x_(n) s` lie in `𝒩`. -/
theorem modes_mem_normal {w e : ℕ} (hwe : w + e ≤ 6) {x s : V} (hx : x ∈ A.grade w)
    (hs : s ∈ A.grade e)
    (hsing : ∀ m : ℕ, m < w + e → A.mode (m : ℤ) x s ∈ D.ladder (w + e - m - 1)) :
    ∀ n : ℕ, A.mode (n : ℤ) x s ∈ D.normal := by
  intro n
  by_cases hn : n < w + e
  · exact D.ladder_le_normal _ (by omega) (hsing n hn)
  · rw [A.mode_trunc (n : ℤ) hx hs (by omega)]
    exact D.normal.zero_mem

end ClosureData

namespace LowerCertificate

variable {D : ClosureData A} (L : LowerCertificate D)
include L

section Positive

variable (hG4 : ∀ a ∈ D.S₂, ∀ s ∈ D.S₃, A.mode 0 a s ∈ D.W₄)
  (hG5 : ∀ a ∈ D.S₂, ∀ q ∈ D.P₄, A.mode 0 a q ∈ D.N₅)
include hG4 hG5

/-- `2 a₁p = L(1)(a₀p) - a₀L(1)p - (L(1)a)₀p ∈ W₄` (line 2584). -/
theorem S₂P₄1 {a q : V} (ha : a ∈ D.S₂) (hq : q ∈ D.P₄) : A.mode 1 a q ∈ D.W₄ := by
  have := A.L1_wt2_mem (X := D.W₄) (D.S₂_grade ha) (n := 0) (by norm_num)
    (L.L1N₅ hG4 _ (hG5 a ha q hq)) (hG4 a ha _ (L.L1W₄ q (D.P₄_le_W₄ hq)))
    (L.KW₄0 (L.L1_S₂ ha) q (D.P₄_le_W₄ hq))
  simpa using this

/-- `a₂p = L(1)(a₁p) - a₁L(1)p - (L(1)a)₁p ∈ S₃` (line 2585). -/
theorem S₂P₄2 {a q : V} (ha : a ∈ D.S₂) (hq : q ∈ D.P₄) : A.mode 2 a q ∈ D.S₃ := by
  have := A.L1_wt2_mem (X := D.S₃) (D.S₂_grade ha) (n := 1) (by norm_num)
    (L.L1W₄ _ (L.S₂P₄1 hG4 hG5 ha hq)) (L.S₂S₃1 hG4 ha (L.L1W₄ q (D.P₄_le_W₄ hq)))
    (L.KW₄1 hG4 (L.L1_S₂ ha) (D.P₄_le_W₄ hq))
  simpa [show (1 : ℤ) + 1 = 2 by norm_num] using this

/-- `2 a₃p = L(2)(a₁p) - a₁L(2)p - 3 (L(1)a)₂p ∈ S₂` (line 2586). -/
theorem S₂P₄3 {a q : V} (ha : a ∈ D.S₂) (hq : q ∈ D.P₄) : A.mode 3 a q ∈ D.S₂ := by
  have := A.L2_wt2_mem (X := D.S₂) (D.S₂_grade ha) (n := 1) (by norm_num)
    (L.L2W₄ _ (L.S₂P₄1 hG4 hG5 ha hq)) (L.S₂S₂1 a ha _ (L.L2W₄ q (D.P₄_le_W₄ hq)))
    (by rw [show (1 : ℤ) + 1 = 2 by norm_num]
        exact L.KW₄2 hG4 (L.L1_S₂ ha) (D.P₄_le_W₄ hq))
    (by rw [A.mode_grade_zero_left (L.L2_S₂_grade ha) (n := 1) (by norm_num)]
        exact Submodule.zero_mem _)
  simpa [show (1 : ℤ) + 2 = 3 by norm_num] using this

/-- `a₄p = L(2)(a₂p) - a₂L(2)p - 3 (L(1)a)₃p ∈ K` (line 2587). -/
theorem S₂P₄4 {a q : V} (ha : a ∈ D.S₂) (hq : q ∈ D.P₄) : A.mode 4 a q ∈ D.K := by
  have := A.L2_wt2_mem (X := D.K) (D.S₂_grade ha) (n := 2) (by norm_num)
    (L.L2S₃ _ (L.S₂P₄2 hG4 hG5 ha hq)) (L.S₂S₂2 a ha _ (L.L2W₄ q (D.P₄_le_W₄ hq)))
    (by rw [show (2 : ℤ) + 1 = 3 by norm_num]
        exact L.KW₄3 hG4 (L.L1_S₂ ha) (D.P₄_le_W₄ hq))
    (by rw [A.mode_grade_zero_left (L.L2_S₂_grade ha) (n := 2) (by norm_num)]
        exact Submodule.zero_mem _)
  simpa [show (2 : ℤ) + 2 = 4 by norm_num] using this

theorem S₂_P₄_sing {a q : V} (ha : a ∈ D.S₂) (hq : q ∈ D.P₄) :
    ∀ m : ℕ, m < 2 + 4 → A.mode (m : ℤ) a q ∈ D.ladder (2 + 4 - m - 1) := by
  intro m hm
  interval_cases m
  · exact hG5 a ha q hq
  · exact L.S₂P₄1 hG4 hG5 ha hq
  · exact L.S₂P₄2 hG4 hG5 ha hq
  · exact L.S₂P₄3 hG4 hG5 ha hq
  · exact L.S₂P₄4 hG4 hG5 ha hq
  · exact A.mode_mem_grade (D.S₂_grade ha) (D.P₄_grade hq) (by norm_num)

end Positive

theorem K_K_sing {x y : V} (hx : x ∈ D.K) (hy : y ∈ D.K) :
    ∀ m : ℕ, m < 1 + 1 → A.mode (m : ℤ) x y ∈ D.ladder (1 + 1 - m - 1) := by
  intro m hm
  interval_cases m
  · exact L.KK0 x hx y hy
  · exact A.mode_mem_grade (D.K_grade hx) (D.K_grade hy) (by norm_num)

theorem S₂_S₂_sing {a b : V} (ha : a ∈ D.S₂) (hb : b ∈ D.S₂) :
    ∀ m : ℕ, m < 2 + 2 → A.mode (m : ℤ) a b ∈ D.ladder (2 + 2 - m - 1) := by
  intro m hm
  interval_cases m
  · exact L.S₂S₂0 a ha b hb
  · exact L.S₂S₂1 a ha b hb
  · exact L.S₂S₂2 a ha b hb
  · exact A.mode_mem_grade (D.S₂_grade ha) (D.S₂_grade hb) (by norm_num)

end LowerCertificate

open ClosureData LowerCertificate

namespace LowerCertificate

variable {D : ClosureData A} (L : LowerCertificate D)
  (hG4 : ∀ a ∈ D.S₂, ∀ s ∈ D.S₃, A.mode 0 a s ∈ D.W₄)
  (hG5 : ∀ a ∈ D.S₂, ∀ q ∈ D.P₄, A.mode 0 a q ∈ D.N₅)
include L hG4 hG5

/-- Hypothesis 1 for a current `x ∈ K`. -/
theorem hyp_one_K {x : V} (hx : x ∈ D.K) :
    ∀ d, ∀ s ∈ D.family d, ∀ n : ℕ, A.mode (n : ℤ) x s ∈ D.normal
  | 1, _, hs, n => D.modes_mem_normal (by norm_num) (D.K_grade hx) (D.K_grade hs)
      (L.K_K_sing hx hs) n
  | 2, _, hs, n => D.modes_mem_normal (by norm_num) (D.K_grade hx) (D.S₂_grade hs)
      (L.K_S₂_sing hx hs) n
  | 3, _, hs, n => D.modes_mem_normal (by norm_num) (D.K_grade hx) (D.S₃_grade hs)
      (fun m hm => by
        rw [show 1 + 3 - m - 1 = 3 - m by omega]
        exact L.K_S₃_sing hx hs m hm) n
  | 4, _, hs, n => D.modes_mem_normal (by norm_num) (D.K_grade hx) (D.P₄_grade hs)
      (fun m hm => by
        rw [show 1 + 4 - m - 1 = 4 - m by omega]
        exact L.K_W₄_sing hG4 hx (D.P₄_le_W₄ hs) m hm) n
  | 0, _, hs, _ => by
      rw [(Submodule.mem_bot k).mp hs, map_zero]
      exact Submodule.zero_mem _
  | _ + 5, _, hs, _ => by
      rw [(Submodule.mem_bot k).mp hs, map_zero]
      exact Submodule.zero_mem _

/-- Hypothesis 1 for a field `x ∈ S₂`. -/
theorem hyp_one_S₂ {x : V} (hx : x ∈ D.S₂) :
    ∀ d, ∀ s ∈ D.family d, ∀ n : ℕ, A.mode (n : ℤ) x s ∈ D.normal
  | 1, s, hs, n => by
      have h := L.skew_ladder (D.K_grade hs) (D.S₂_grade hx) (L.K_S₂_sing hs hx) n
      by_cases hn : n < 1 + 2
      · exact D.ladder_le_normal _ (by omega) h
      · rw [A.mode_trunc (n : ℤ) (D.S₂_grade hx) (D.K_grade hs) (by push_cast; omega)]
        exact Submodule.zero_mem _
  | 2, _, hs, n => D.modes_mem_normal (by norm_num) (D.S₂_grade hx) (D.S₂_grade hs)
      (L.S₂_S₂_sing hx hs) n
  | 3, _, hs, n => D.modes_mem_normal (by norm_num) (D.S₂_grade hx) (D.S₃_grade hs)
      (L.S₂_S₃_sing hG4 hx hs) n
  | 4, _, hs, n => D.modes_mem_normal (by norm_num) (D.S₂_grade hx) (D.P₄_grade hs)
      (L.S₂_P₄_sing hG4 hG5 hx hs) n
  | 0, _, hs, _ => by
      rw [(Submodule.mem_bot k).mp hs, map_zero]
      exact Submodule.zero_mem _
  | _ + 5, _, hs, _ => by
      rw [(Submodule.mem_bot k).mp hs, map_zero]
      exact Submodule.zero_mem _

end LowerCertificate

/-- **Hypothesis 1 of Theorem `thm:recursive`** for `S 1 = K`, `S 2 = S₂`, `S 3 = S₃`,
`S 4 = P₄` (manuscript line 2592): all nonnegative modes of `K` and `S₂` on the generators lie
in their differential normal span.  Gates 4 and 5 are derived (`gate4`, `gate5`). -/
theorem closure_hypothesis_one (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (hnilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.eL) (A.mode 0 D.eR) w v = 0)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0) :
    ∀ x, x ∈ D.family 1 ∨ x ∈ D.family 2 → ∀ d, ∀ s ∈ D.family d, ∀ n : ℕ,
      A.mode n x s ∈ A.normalSpan (⋃ e, (D.family e : Set V)) := by
  have hG4 := L.gate4 G hnilE
  have hG5 := L.gate5 hG4 G G5 hnilF
  intro x hx
  rcases hx with hx | hx
  · exact L.hyp_one_K hG4 hG5 hx
  · exact L.hyp_one_S₂ hG4 hG5 hx

/-- **Hypothesis 2 of Theorem `thm:recursive`** for `h = 4` (manuscript line 2592):
`S₃ ⊂ (S₂)₀S₂ + 𝒩₃(K + S₂)` (provenance `S₃ = N₃ + Span{a₀b}`, Certificate
`cert:initial`) and `P₄ ⊂ (S₂)₀S₃ + 𝒩₄(K + S₂ + S₃)` (line 2222). -/
theorem closure_hypothesis_two (D : ClosureData A) (L : LowerCertificate D) :
    ∀ d, 3 ≤ d → d ≤ 4 →
      D.family d ≤ Submodule.span k {x | ∃ a ∈ D.family 2, ∃ b ∈ D.family (d - 1),
          x = A.mode 0 a b} ⊔
        (A.normalSpan (⋃ e, ⋃ (_ : e < d), (D.family e : Set V)) ⊓ A.grade d) := by
  intro d hd3 hd4
  obtain rfl | rfl : d = 3 ∨ d = 4 := by omega
  · -- `d = 3`
    have hK : D.K ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 3), (D.family e : Set V)) := fun x hx =>
      A.subset_normalSpan _ (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by norm_num, hx⟩⟩)
    have hS₂ : D.S₂ ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 3), (D.family e : Set V)) := fun x hx =>
      A.subset_normalSpan _ (Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨by norm_num, hx⟩⟩)
    have hN₃ : D.N₃ ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 3), (D.family e : Set V)) ⊓ A.grade 3 :=
      le_inf (sup_le (negProd_le_normalSpan hK hS₂) (map_T_le_normalSpan hS₂)) D.N₃_grade
    exact L.S₃_prov.trans (sup_le (le_sup_of_le_right hN₃) le_sup_left)
  · -- `d = 4`
    have hK : D.K ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 4), (D.family e : Set V)) := fun x hx =>
      A.subset_normalSpan _ (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by norm_num, hx⟩⟩)
    have hS₂ : D.S₂ ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 4), (D.family e : Set V)) := fun x hx =>
      A.subset_normalSpan _ (Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨by norm_num, hx⟩⟩)
    have hS₃ : D.S₃ ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 4), (D.family e : Set V)) := fun x hx =>
      A.subset_normalSpan _ (Set.mem_iUnion.mpr ⟨3, Set.mem_iUnion.mpr ⟨by norm_num, hx⟩⟩)
    have hN₄ : D.N₄ ≤ A.normalSpan (⋃ e, ⋃ (_ : e < 4), (D.family e : Set V)) ⊓ A.grade 4 :=
      le_inf (sup_le (sup_le (negProd_le_normalSpan hK hS₃) (map_T_le_normalSpan hS₃))
        (negProd_le_normalSpan hS₂ hS₂)) D.N₄_grade
    exact L.P₄_prov'.trans (sup_le le_sup_left (le_sup_of_le_right hN₄))

/-- The grading hypotheses of Theorem `thm:recursive` for the family. -/
theorem closure_family_grade (D : ClosureData A) : ∀ d, D.family d ≤ A.grade d :=
  D.family_grade

theorem closure_family_top (D : ClosureData A) : ∀ d, 4 < d → D.family d = ⊥ :=
  D.family_top

#print axioms closure_hypothesis_one
#print axioms closure_hypothesis_two
#print axioms closure_family_grade
#print axioms closure_family_top

end HaagerupIzumi.C8
