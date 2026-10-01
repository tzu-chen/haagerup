module

public import HaagerupIzumi.C8.Properness.Gate4
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-! # Lemma `lem:bootstrap` and Gate 5: `(S₂)₀P₄ ⊂ N₅`

Formalizes `c8_expanded_20260929/haagerup_c8_expanded.tex`, Section `sec:bootstrap`
(Lemma `lem:bootstrap`, lines 2344–2428) and Section `sec:gate5` (lines 2430–2576).

Throughout, `hG4` denotes the conclusion of Gate 4, *proved* in `Gate4.lean`
(`LowerCertificate.gate4`); it is a hypothesis of the lemmas here only so that this file can
be read independently.  The final theorems in `Final.lean` discharge it.

Bootstrap (Lemma `lem:bootstrap`): `(S₂)₁S₃ ⊂ S₃`, `(S₂)₂S₃ ⊂ S₂`, `(S₂)₃S₃ ⊂ K`
(eq. `eq:positive-S3`), `K₁W₄ ⊂ S₃`, `K₂W₄ ⊂ S₂`, `K₃W₄ ⊂ K` (eq. `eq:positive-W4`),
`L(1)N₅ ⊂ W₄`, `L(2)N₅ ⊂ S₃` (eq. `eq:positive-N5`).  The Virasoro commutators
`eq:L1-weight2`, `eq:L2-weight2` are used for *every* `a ∈ S₂`, keeping the terms
`(L(1)a)_(n)`, `(L(2)a)_(n)`; this makes the quasiprimarity of the primitive fields and the
separate treatment of the affine part of `S₂` (lines 2389–2401) unnecessary.

Gate 5: Lemma `lem:normal-controls` (`(S₂)₀N₄ ⊂ N₅`, `(N₃)₀S₃ ⊂ N₅`), Lemma `lem:jacobi`,
the charged families (bottom witnesses via `HaagerupIzumi.CFT.jacobi_bottom_witness`, the
weight argument `β(a_i, p_j) = 0`, raising, current covariance), the neutral family (via the
charged-span certificate and lowering saturation), and the affine part of `S₂`.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V} {D : ClosureData A}

namespace LowerCertificate

variable (L : LowerCertificate D)
include L

/-! ### Lemma `lem:bootstrap` -/

section Bootstrap

variable (hG4 : ∀ a ∈ D.S₂, ∀ s ∈ D.S₃, A.mode 0 a s ∈ D.W₄)
include hG4

/-- `(S₂)₁S₃ ⊂ S₃` (eq. `eq:positive-S3`). -/
theorem S₂S₃1 {a s : V} (ha : a ∈ D.S₂) (hs : s ∈ D.S₃) : A.mode 1 a s ∈ D.S₃ := by
  have := A.L1_wt2_mem (X := D.S₃) (D.S₂_grade ha) (n := 0) (by norm_num)
    (L.L1W₄ _ (hG4 a ha s hs)) (L.S₂S₂0 a ha _ (L.L1S₃ s hs)) (L.KS₃0 (L.L1_S₂ ha) s hs)
  simpa using this

/-- `(S₂)₂S₃ ⊂ S₂` (eq. `eq:positive-S3`). -/
theorem S₂S₃2 {a s : V} (ha : a ∈ D.S₂) (hs : s ∈ D.S₃) : A.mode 2 a s ∈ D.S₂ := by
  have := A.L1_wt2_mem (X := D.S₂) (D.S₂_grade ha) (n := 1) (by norm_num)
    (L.L1S₃ _ (L.S₂S₃1 hG4 ha hs)) (L.S₂S₂1 a ha _ (L.L1S₃ s hs)) (L.KS₃1 (L.L1_S₂ ha) s hs)
  simpa [show (1 : ℤ) + 1 = 2 by norm_num] using this

/-- `(S₂)₃S₃ ⊂ K` (eq. `eq:positive-S3`). -/
theorem S₂S₃3 {a s : V} (ha : a ∈ D.S₂) (hs : s ∈ D.S₃) : A.mode 3 a s ∈ D.K := by
  have := A.L2_wt2_mem (X := D.K) (D.S₂_grade ha) (n := 1) (by norm_num)
    (L.L2S₃ _ (L.S₂S₃1 hG4 ha hs)) (L.S₂K1 ha (L.L2S₃ s hs))
    (by rw [show (1 : ℤ) + 1 = 2 by norm_num]; exact L.KS₃2 (L.L1_S₂ ha) hs)
    (by rw [A.mode_grade_zero_left (L.L2_S₂_grade ha) (n := 1) (by norm_num)]
        exact Submodule.zero_mem _)
  simpa [show (1 : ℤ) + 2 = 3 by norm_num] using this

/-- The singular products `a_(m) s`, `a ∈ S₂`, `s ∈ S₃`, lie in the ladder. -/
theorem S₂_S₃_sing {a s : V} (ha : a ∈ D.S₂) (hs : s ∈ D.S₃) :
    ∀ m : ℕ, m < 2 + 3 → A.mode (m : ℤ) a s ∈ D.ladder (2 + 3 - m - 1) := by
  intro m hm
  interval_cases m
  · exact hG4 a ha s hs
  · exact L.S₂S₃1 hG4 ha hs
  · exact L.S₂S₃2 hG4 ha hs
  · exact L.S₂S₃3 hG4 ha hs
  · exact A.mode_mem_grade (D.S₂_grade ha) (D.S₃_grade hs) (by norm_num)

/-- `K₁P₄ ⊂ S₃`, from `P₄ ⊂ (S₂)₀S₃ + N₄` and eq. `eq:k1-provenance` (line 2405). -/
theorem KP₄1 {x : V} (hx : x ∈ D.K) {q : V} (hq : q ∈ D.P₄) : A.mode 1 x q ∈ D.S₃ := by
  refine (sup_le (VertexAlgebra.zeroProd_le (Z := D.S₃.comap (A.mode 1 x)) ?_)
    (fun v hv => L.KN₄1 hx v hv) : _ ≤ D.S₃.comap (A.mode 1 x)) (L.P₄_prov' hq)
  intro a ha s hs
  show A.mode 1 x (A.mode 0 a s) ∈ D.S₃
  rw [A.one_mode_comm (D.K_grade hx) (D.S₂_grade ha) (by norm_num),
    show (0 : ℤ) + 1 = 1 by norm_num]
  exact D.S₃.add_mem (D.S₃.add_mem (L.S₂S₂0 a ha _ (L.KS₃1 hx s hs))
    (L.S₂S₃1 hG4 (L.KS₂0 x hx a ha) hs)) (L.KS₃0 (L.KS₂1 x hx a ha) s hs)

/-- `K₁W₄ ⊂ S₃` (eq. `eq:positive-W4`). -/
theorem KW₄1 {x : V} (hx : x ∈ D.K) {w : V} (hw : w ∈ D.W₄) : A.mode 1 x w ∈ D.S₃ := by
  obtain ⟨n, hn, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact D.S₃.add_mem (L.KN₄1 hx n hn) (L.KP₄1 hG4 hx hq)

/-- `K₂W₄ ⊂ S₂` (eq. `eq:positive-W4`, via `[L(1), x₁] = -x₂`). -/
theorem KW₄2 {x : V} (hx : x ∈ D.K) {w : V} (hw : w ∈ D.W₄) : A.mode 2 x w ∈ D.S₂ := by
  have := A.L1_wt1_mem (X := D.S₂) (D.K_grade hx) (n := 1) (by norm_num)
    (L.L1S₃ _ (L.KW₄1 hG4 hx hw)) (L.KS₃1 hx _ (L.L1W₄ w hw))
    (by rw [A.mode_grade_zero_left (L.L1_K_grade hx) (n := 1) (by norm_num)]
        exact Submodule.zero_mem _)
  simpa [show (1 : ℤ) + 1 = 2 by norm_num] using this

/-- `K₃W₄ ⊂ K` (eq. `eq:positive-W4`, via `[L(2), x₁] = -x₃`). -/
theorem KW₄3 {x : V} (hx : x ∈ D.K) {w : V} (hw : w ∈ D.W₄) : A.mode 3 x w ∈ D.K := by
  have := A.L2_wt1_mem (X := D.K) (D.K_grade hx) (n := 1) (by norm_num)
    (L.L2S₃ _ (L.KW₄1 hG4 hx hw)) (L.KS₂1 x hx _ (L.L2W₄ w hw))
    (by rw [A.mode_grade_zero_left (L.L1_K_grade hx) (n := 1 + 1) (by norm_num)]
        exact Submodule.zero_mem _)
  simpa [show (1 : ℤ) + 2 = 3 by norm_num] using this

/-- The singular products `x_(m) w`, `x ∈ K`, `w ∈ W₄`, lie in the ladder. -/
theorem K_W₄_sing {x w : V} (hx : x ∈ D.K) (hw : w ∈ D.W₄) :
    ∀ m : ℕ, m < 1 + 4 → A.mode (m : ℤ) x w ∈ D.ladder (4 - m) := by
  intro m hm
  interval_cases m
  · exact L.KW₄0 hx w hw
  · exact L.KW₄1 hG4 hx hw
  · exact L.KW₄2 hG4 hx hw
  · exact L.KW₄3 hG4 hx hw
  · exact A.mode_mem_grade (D.K_grade hx) (D.W₄_grade hw) (by norm_num)

/-- `L(1)N₅ ⊂ W₄` (eq. `eq:positive-N5`). -/
theorem L1N₅ : ∀ v ∈ D.N₅, A.mode 2 A.ω v ∈ D.W₄ := by
  refine N₅_le_comap (A.mode 2 A.ω) ?_ ?_ ?_
  · intro y hy w hw
    rw [A.L1_comm_wt1 (D.K_grade hy) (-1) w, show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left (L.L1_K_grade hy) w
    rw [hr]
    exact D.W₄.add_mem (D.W₄.sub_mem (D.N₄_le_W₄ (D.N₄_of_K_S₃ hy (L.L1W₄ w hw)))
      (D.W₄.smul_mem _ (L.KW₄0 hy w hw))) (D.W₄.smul_mem r hw)
  · intro w hw
    rw [A.L1_T (D.W₄_grade hw)]
    exact D.W₄.add_mem (D.N₄_le_W₄ (D.N₄_of_T (L.L1W₄ w hw))) (D.W₄.smul_mem _ hw)
  · intro a ha s hs
    rw [A.L1_comm_wt2 (D.S₂_grade ha) (-1) s, show (-1 : ℤ) + 1 = 0 by norm_num]
    exact D.W₄.add_mem (D.W₄.add_mem (D.N₄_le_W₄ (D.N₄_of_S₂_S₂ ha (L.L1S₃ s hs)))
      (D.W₄.smul_mem _ (hG4 a ha s hs))) (D.N₄_le_W₄ (D.N₄_of_K_S₃ (L.L1_S₂ ha) hs))

/-- `L(2)N₅ ⊂ S₃` (eq. `eq:positive-N5`). -/
theorem L2N₅ : ∀ v ∈ D.N₅, A.mode 3 A.ω v ∈ D.S₃ := by
  refine N₅_le_comap (A.mode 3 A.ω) ?_ ?_ ?_
  · intro y hy w hw
    rw [A.L2_comm_wt1 (D.K_grade hy) (-1) w, show (-1 : ℤ) + 2 = 1 by norm_num,
      show (-1 : ℤ) + 1 = 0 by norm_num,
      A.mode_grade_zero_left (L.L1_K_grade hy) (n := 0) (by norm_num), smul_zero, add_zero]
    exact D.S₃.sub_mem (L.N₃_le_S₃ (D.N₃_of_K_S₂ hy (L.L2W₄ w hw)))
      (D.S₃.smul_mem _ (L.KW₄1 hG4 hy hw))
  · intro w hw
    rw [A.L2_T]
    exact D.S₃.add_mem (L.N₃_le_S₃ (D.N₃_of_T (L.L2W₄ w hw))) (D.S₃.smul_mem _ (L.L1W₄ w hw))
  · intro a ha s hs
    rw [A.L2_comm_wt2 (D.S₂_grade ha) (-1) s, show (-1 : ℤ) + 2 = 1 by norm_num,
      show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left (L.L2_S₂_grade ha) s
    rw [hr]
    exact D.S₃.add_mem (D.S₃.add_mem (D.S₃.add_mem (L.S₂mK ha (L.L2S₃ s hs))
      (D.S₃.smul_mem _ (L.S₂S₃1 hG4 ha hs))) (D.S₃.smul_mem _ (L.KS₃0 (L.L1_S₂ ha) s hs)))
      (D.S₃.smul_mem r hs)

/-! ### Lemma `lem:normal-controls` -/

/-- `(S₂)₀N₄ ⊂ N₅` (zero-mode derivation and skew reordering). -/
theorem S₂N₄0 {a : V} (ha : a ∈ D.S₂) : ∀ v ∈ D.N₄, A.mode 0 a v ∈ D.N₅ := by
  refine N₄_le_comap (A.mode 0 a) ?_ ?_ ?_
  · intro y hy s hs
    rw [A.zero_mode_comm (D.S₂_grade ha) (D.K_grade hy)]
    exact D.N₅.add_mem (D.N₅_of_K_W₄ hy (hG4 a ha s hs)) (D.N₅_of_S₂_S₃ (L.S₂K0 ha hy) hs)
  · intro s hs
    rw [A.zero_mode_T]
    exact D.N₅_of_T (hG4 a ha s hs)
  · intro b hb c hc
    rw [A.zero_mode_comm (D.S₂_grade ha) (D.S₂_grade hb)]
    refine D.N₅.add_mem (D.N₅_of_S₂_S₃ hb (L.S₂S₂0 a ha c hc)) ?_
    -- reorder `(a₀b)₋₁c` with `a₀b ∈ S₃`, `c ∈ S₂`
    exact L.reorder_mem (D.S₂_grade hc) (D.S₃_grade (L.S₂S₂0 a ha b hb))
      (D.N₅_of_S₂_S₃ hc (L.S₂S₂0 a ha b hb)) (L.S₂_S₃_sing hG4 hc (L.S₂S₂0 a ha b hb))

/-- `(x₋₁ a)₀ v` for `x ∈ K`, `a ∈ S₂` (iterate formula, eq. `eq:iterate`). -/
theorem KS₂_zero_mem {x a v : V} (hx : x ∈ D.K) (ha : a ∈ D.S₂) {e : ℕ}
    (hv : v ∈ A.grade e)
    (hsx : ∀ m : ℕ, m < 1 + e → A.mode (m : ℤ) x v ∈ D.ladder (e - m))
    (hsa : ∀ m : ℕ, m < 2 + e → A.mode (m : ℤ) a v ∈ D.ladder (e + 1 - m)) :
    A.mode 0 (A.mode (-1) x a) v ∈ D.ladder (e + 2) := by
  refine A.iterate_mem (D.K_grade hx) (D.S₂_grade ha) hv (-1) 0 (fun t _ => ?_)
    (fun t _ => ?_)
  · by_cases ht : t < 2 + e
    · have := L.neg_mode_K hx t (e + 1 - t) _ (hsa t ht)
      rw [show e + 1 - t + t + 1 = e + 2 by omega] at this
      rw [zero_add, show (-1 : ℤ) - t = -(t : ℤ) - 1 by ring]
      exact this
    · rw [zero_add, A.mode_trunc (t : ℤ) (D.S₂_grade ha) hv (by push_cast; omega), map_zero]
      exact Submodule.zero_mem _
  · by_cases ht : t < 1 + e
    · have := L.neg_mode_S₂ ha t (e - t) _ (hsx t ht)
      rw [show e - t + t + 2 = e + 2 by omega] at this
      rw [show (-1 : ℤ) + 0 - t = -(t : ℤ) - 1 by ring]
      exact this
    · rw [A.mode_trunc (t : ℤ) (D.K_grade hx) hv (by push_cast; omega), map_zero]
      exact Submodule.zero_mem _

/-- `(N₃)₀S₃ ⊂ N₅` (Lemma `lem:normal-controls`, second inclusion). -/
theorem N₃S₃0 {s : V} (hs : s ∈ D.S₃) : ∀ v ∈ D.N₃, A.mode 0 v s ∈ D.N₅ := by
  refine N₃_le_comap ((A.mode 0).flip s) ?_ ?_
  · intro x hx a ha
    show A.mode 0 (A.mode (-1) x a) s ∈ D.N₅
    have := L.KS₂_zero_mem hG4 hx ha (D.S₃_grade hs) (L.K_S₃_sing hx hs)
      (fun m hm => by
        rw [show 3 + 1 - m = 2 + 3 - m - 1 by omega]
        exact L.S₂_S₃_sing hG4 ha hs m hm)
    exact this
  · intro a _
    show A.mode 0 (A.T a) s ∈ D.N₅
    rw [A.mode_T_zero]
    exact D.N₅.zero_mem

/-- Lemma `lem:jacobi`: if `a₀b ∈ N₃` then `a₀(b₀p) - b₀(a₀p) ∈ N₅` for `p ∈ S₃`. -/
theorem jacobi {a b p : V} (ha : a ∈ D.S₂) (hb : b ∈ D.S₂) (hab : A.mode 0 a b ∈ D.N₃)
    (hp : p ∈ D.S₃) : A.mode 0 a (A.mode 0 b p) - A.mode 0 b (A.mode 0 a p) ∈ D.N₅ := by
  rw [A.zero_mode_comm (D.S₂_grade ha) (D.S₂_grade hb), add_sub_cancel_left]
  exact L.N₃S₃0 hG4 hp _ hab

/-- `(S₂)₀W₄ ⊂ N₅` for fields `a` with `a₀P₄ ⊂ N₅`. -/
theorem zero_W₄ {a : V} (ha : a ∈ D.S₂) (hP : ∀ q ∈ D.P₄, A.mode 0 a q ∈ D.N₅) :
    ∀ w ∈ D.W₄, A.mode 0 a w ∈ D.N₅ := by
  intro w hw
  obtain ⟨n, hn, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact D.N₅.add_mem (L.S₂N₄0 hG4 ha n hn) (hP q hq)

end Bootstrap

/-! ### The weight argument `β(a_i, p_j) = 0` -/

/-- The left Cartan current kills `P₄`, and `H_R (H_R - 2)(H_R + 2)` kills `P₄`
(from the 18 current-zero-mode identities). -/
theorem hL_P₄ : ∀ q ∈ D.P₄, A.mode 0 D.hL q = 0 := by
  intro q hq
  have : D.P₄ ≤ LinearMap.ker (A.mode 0 D.hL) :=
    Submodule.span_le.mpr fun q hq => L.hL_q q hq
  exact this hq

theorem hR_P₄ : ∀ q ∈ D.P₄,
    A.mode 0 D.hR (A.mode 0 D.hR (A.mode 0 D.hR q)) - (4 : k) • A.mode 0 D.hR q = 0 := by
  intro q hq
  let f : V →ₗ[k] V := A.mode 0 D.hR ∘ₗ A.mode 0 D.hR ∘ₗ A.mode 0 D.hR - (4 : k) • A.mode 0 D.hR
  have : D.P₄ ≤ LinearMap.ker f := by
    refine Submodule.span_le.mpr fun q hq => ?_
    simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    show f q = 0
    simp only [f, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rcases hq with rfl | rfl | rfl
    · simp only [L.hR_qp, map_smul, smul_smul]
      norm_num
    · simp only [L.hR_q0, map_zero, smul_zero, sub_zero]
    · simp only [L.hR_qm, map_smul, smul_smul]
      norm_num
  exact this hq

/-- Weight separation: a vector of `W₄` whose Cartan weight is not a weight of the triplet
`Q = W₄/N₄` lies in `N₄` (manuscript line 2527). -/
theorem weight_sep {w : V} (hw : w ∈ D.W₄) {μL μR : k}
    (hL : A.mode 0 D.hL w = μL • w) (hR : A.mode 0 D.hR w = μR • w)
    (hμ : μL ≠ 0 ∨ μR * (μR - 2) * (μR + 2) ≠ 0) : w ∈ D.N₄ := by
  obtain ⟨n, hn, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rcases hμ with hμ | hμ
  · have h1 : A.mode 0 D.hL (n + q) ∈ D.N₄ := by
      rw [map_add, L.hL_P₄ q hq, add_zero]
      exact L.KN₄0 D.hL_mem n hn
    rw [hL] at h1
    exact (D.N₄.smul_mem_iff hμ).mp h1
  · have hH : ∀ v ∈ D.N₄, A.mode 0 D.hR v ∈ D.N₄ := fun v hv => L.KN₄0 D.hR_mem v hv
    have e : A.mode 0 D.hR (A.mode 0 D.hR (A.mode 0 D.hR (n + q))) -
          (4 : k) • A.mode 0 D.hR (n + q) =
        (A.mode 0 D.hR (A.mode 0 D.hR (A.mode 0 D.hR n)) - (4 : k) • A.mode 0 D.hR n) +
          (A.mode 0 D.hR (A.mode 0 D.hR (A.mode 0 D.hR q)) - (4 : k) • A.mode 0 D.hR q) := by
      simp only [map_add, smul_add]
      abel
    have h1 : A.mode 0 D.hR (A.mode 0 D.hR (A.mode 0 D.hR (n + q))) -
        (4 : k) • A.mode 0 D.hR (n + q) ∈ D.N₄ := by
      rw [e, L.hR_P₄ q hq, add_zero]
      exact D.N₄.sub_mem (hH _ (hH _ (hH _ hn))) (D.N₄.smul_mem _ (hH _ hn))
    have e2 : A.mode 0 D.hR (A.mode 0 D.hR (A.mode 0 D.hR (n + q))) -
        (4 : k) • A.mode 0 D.hR (n + q) = (μR * (μR - 2) * (μR + 2)) • (n + q) := by
      simp only [hR, map_smul, smul_smul]
      rw [← sub_smul]
      congr 1
      ring
    rw [e2] at h1
    exact (D.N₄.smul_mem_iff hμ).mp h1

/-- The Cartan weight of `a₀p` is the sum of the weights (zero modes are derivations). -/
theorem weight_add {h a p : V} (hh : h ∈ D.K) (ha : a ∈ D.S₂) {μ ν : k}
    (hμ : A.mode 0 h a = μ • a) (hν : A.mode 0 h p = ν • p) :
    A.mode 0 h (A.mode 0 a p) = (μ + ν) • A.mode 0 a p := by
  rw [A.zero_mode_comm (D.K_grade hh) (D.S₂_grade ha), hν, hμ, map_smul, map_smul,
    LinearMap.smul_apply]
  module

end LowerCertificate

/-! ### Certificate inputs of Gate 5 -/

/-- The bottom data of one charged highest field `a = a_i` (manuscript lines 2494–2531, record
`hi_cft_20260923_c8two_gate5_verified.json`): a partner charged field `b = a_j`
(`j ∈ {3, 6}`) with `(a_i)₀a_j ∈ 𝒩₃(K + S₂)` (exact combination of lower relations, table at
line 2512), the bottom input `p = p_j` (`r3_000910` or `r3_000899`) with the exact relation
`β(a_j, p_j) = c_j q₋`, i.e. `(a_j)₀p_j = c_j q₋ + n` with `n ∈ 𝒩₄(K + S₂ + S₃)`, `c_j ≠ 0`
(final Jacobi
certificate), and the Cartan weights of `a_i` and `p_j`, whose sum is not a weight of the
triplet `Q` (column "Weight of `(a_i)₀p_j`" of the table). -/
def ChargedBottom (D : ClosureData A) (a : V) : Prop :=
  ∃ (b p n : V) (c μL μR νL νR : k),
    b ∈ D.S₂ ∧ p ∈ D.S₃ ∧ A.mode 0 a b ∈ D.fullN₃ ∧
    A.mode 0 b p = c • D.qm + n ∧ n ∈ D.fullN₄ ∧ c ≠ 0 ∧
    A.mode 0 D.hL a = μL • a ∧ A.mode 0 D.hR a = μR • a ∧
    A.mode 0 D.hL p = νL • p ∧ A.mode 0 D.hR p = νR • p ∧
    (μL + νL ≠ 0 ∨ (μR + νR) * ((μR + νR) - 2) * ((μR + νR) + 2) ≠ 0)

/-- Certificate inputs of Gate 5.

* `charged`, `e`: the eight charged highest fields and the retained neutral singlet; together
  they are the nine Gate 4 fields (`highest_sub`).
* `bottom`: the charged bottom data (`ChargedBottom`).
* `a₃, p₃, n₃, c₃`: the bottom relation `β(a₃, p₃) = c₃ q₋` (`n₃ ∈ 𝒩₄`), `c₃ ≠ 0`, used for the neutral
  family (manuscript lines 2503–2509, 2553–2571).
* `chargedSeeds`: the 28 charged seeds reconstructed from the exact lower relations as
  brackets of charged fields modulo `𝒩₃(K + S₂)`; `lowering_span`: with the 644 lowering images
  they span `S₃` modulo `N₃` (record `hi_cft_20260923_c8two_charged_span_verified.json`,
  rank 322). -/
structure Gate5Certificate (D : ClosureData A) (G : Gate4Certificate D) where
  e : V
  charged : Set V
  e_mem : e ∈ G.highest
  charged_sub : charged ⊆ G.highest
  highest_sub : G.highest ⊆ insert e charged
  bottom : ∀ a ∈ charged, ChargedBottom D a
  a₃ : V
  p₃ : V
  n₃ : V
  c₃ : k
  a₃_mem : a₃ ∈ charged
  p₃_mem : p₃ ∈ D.S₃
  bottom₃ : A.mode 0 a₃ p₃ = c₃ • D.qm + n₃
  n₃_mem : n₃ ∈ D.fullN₄
  c₃_ne : c₃ ≠ 0
  chargedSeeds : Set V
  chargedSeeds_S₃ : chargedSeeds ⊆ D.S₃
  chargedSeeds_mem : ∀ v ∈ chargedSeeds,
    v ∈ A.zeroProd (D.currentSpan charged) (D.currentSpan charged) ⊔ D.fullN₃
  lowering_span : D.S₃ ≤ D.S₃.map (A.mode 0 D.fL) ⊔ D.S₃.map (A.mode 0 D.fR) ⊔
    Submodule.span k chargedSeeds ⊔ D.N₃

namespace LowerCertificate

variable (L : LowerCertificate D)
include L

section Gate5

variable (hG4 : ∀ a ∈ D.S₂, ∀ s ∈ D.S₃, A.mode 0 a s ∈ D.W₄)
include hG4

/-- The charged bottom identity `F(a_i, q₋) = 0`, i.e. `(a_i)₀q₋ ∈ N₅`, from Lemma
`lem:jacobi`, the vanishing `β(a_i,p_j) = 0` and `c_j ≠ 0`, through
`HaagerupIzumi.CFT.jacobi_bottom_witness` on the quotients `B₄/N₄ → B₅/N₅`. -/
theorem charged_bottom {a : V} (ha : a ∈ D.S₂) (hbot : ChargedBottom D a) :
    A.mode 0 a D.qm ∈ D.N₅ := by
  obtain ⟨b, p, n, c, μL, μR, νL, νR, hb, hp, hab', hbp, hn', hc, haL, haR, hpL, hpR, hμ⟩ := hbot
  have hab : A.mode 0 a b ∈ D.N₃ := L.fullN₃_le hab'
  have hn : n ∈ D.N₄ := L.fullN₄_le hn'
  -- `β(a, p) = 0` by Gate 4 and the weight argument
  have hβ : A.mode 0 a p ∈ D.N₄ :=
    L.weight_sep (hG4 a ha p hp) (L.weight_add D.hL_mem ha haL hpL)
      (L.weight_add D.hR_mem ha haR hpR) hμ
  let f := D.N₄.mapQ D.N₅ (A.mode 0 a) (fun v hv => L.S₂N₄0 hG4 ha v hv)
  let g := D.N₄.mapQ D.N₅ (A.mode 0 b) (fun v hv => L.S₂N₄0 hG4 hb v hv)
  have key := CFT.jacobi_bottom_witness f g (D.N₄.mkQ (A.mode 0 a p))
    (D.N₄.mkQ (A.mode 0 b p)) (D.N₄.mkQ D.qm) c ?_ ?_ ?_ hc
  · have h : Submodule.Quotient.mk (A.mode 0 a D.qm) = (0 : V ⧸ D.N₅) := key
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · show Submodule.Quotient.mk (A.mode 0 a (A.mode 0 b p)) =
      (Submodule.Quotient.mk (A.mode 0 b (A.mode 0 a p)) : V ⧸ D.N₅)
    exact (Submodule.Quotient.eq _).mpr (L.jacobi hG4 ha hb hab hp)
  · exact (Submodule.Quotient.mk_eq_zero _).mpr hβ
  · show Submodule.Quotient.mk (A.mode 0 b p) = c • (Submodule.Quotient.mk D.qm : V ⧸ D.N₄)
    rw [hbp, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    simpa using hn

/-- Raising a bottom identity with `a` held highest gives the whole triplet. -/
theorem raise_triplet {a : V} (ha : a ∈ D.S₂) (heR : A.mode 0 D.eR a = 0)
    (hm : A.mode 0 a D.qm ∈ D.N₅) : ∀ q ∈ D.P₄, A.mode 0 a q ∈ D.N₅ := by
  have hcomm : ∀ v, A.mode 0 a (A.mode 0 D.eR v) = A.mode 0 D.eR (A.mode 0 a v) := by
    intro v
    have h := A.zero_mode_comm (D.K_grade D.eR_mem) (D.S₂_grade ha) 0 v
    rw [heR, map_zero, LinearMap.zero_apply, add_zero] at h
    exact h.symm
  have h0 : A.mode 0 a D.q0 ∈ D.N₅ := by
    have h : A.mode 0 a (A.mode 0 D.eR D.qm) ∈ D.N₅ := by
      rw [hcomm]; exact L.KN₅0 D.eR_mem _ hm
    rw [L.eR_qm, map_smul] at h
    exact (D.N₅.smul_mem_iff two_ne_zero).mp h
  have hp : A.mode 0 a D.qp ∈ D.N₅ := by
    have h : A.mode 0 a (A.mode 0 D.eR D.q0) ∈ D.N₅ := by
      rw [hcomm]; exact L.KN₅0 D.eR_mem _ h0
    rw [L.eR_q0, map_smul] at h
    exact (D.N₅.smul_mem_iff two_ne_zero).mp h
  intro q hq
  refine (Submodule.span_le.mpr ?_ : D.P₄ ≤ D.N₅.comap (A.mode 0 a)) hq
  intro q hq'
  simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq'
  rcases hq' with rfl | rfl | rfl
  exacts [hp, h0, hm]

/-- Current covariance for Gate 5: the fields of `S₂` with `a₀P₄ ⊂ N₅` form a current-stable
subspace. -/
theorem gate5_covariance : ∀ x ∈ D.K, ∀ v ∈ A.modeSpace 0 D.P₄ D.N₅ ⊓ D.S₂,
    A.mode 0 x v ∈ A.modeSpace 0 D.P₄ D.N₅ ⊓ D.S₂ := by
  rintro x hx v ⟨hvM, hvS⟩
  refine ⟨(A.mem_modeSpace).mpr fun q hq => ?_, L.KS₂0 x hx v hvS⟩
  have hvM' := (A.mem_modeSpace).mp hvM
  have h := A.zero_mode_comm (D.K_grade hx) (D.S₂_grade hvS) 0 q
  have h' : A.mode 0 (A.mode 0 x v) q =
      A.mode 0 x (A.mode 0 v q) - A.mode 0 v (A.mode 0 x q) := by
    rw [h]; abel
  rw [h']
  exact D.N₅.sub_mem (L.KN₅0 hx _ (hvM' q hq)) (hvM' _ (L.KP₄0 x hx q hq))

/-- Lowering saturation on `S₃` (the nilpotent-ideal argument of the neutral family, line 2546):
`S₃ ⊂ C + N₃` for the current span `C` of brackets of charged fields. -/
theorem charged_span {G : Gate4Certificate D} (G5 : Gate5Certificate D G)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0) :
    D.S₃ ≤ A.zeroProd (D.currentSpan G5.charged) (D.currentSpan G5.charged) ⊔ D.N₃ := by
  set Ch := D.currentSpan G5.charged
  have hChS : Ch ≤ D.S₂ := D.currentSpan_le
    (fun a ha => G.highest_S₂ (G5.charged_sub ha)) fun x hx v hv => L.KS₂0 x hx v hv
  let X : Submodule k V := A.zeroProd Ch Ch ⊔ D.N₃
  -- `X` is current-stable
  have hX : ∀ x ∈ D.K, ∀ v ∈ X, A.mode 0 x v ∈ X := by
    intro x hx v hv
    obtain ⟨y, hy, n, hn, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    refine X.add_mem ?_ (Submodule.mem_sup_right (L.KN₃0 hx n hn))
    refine Submodule.mem_sup_left ((VertexAlgebra.zeroProd_le
      (Z := (A.zeroProd Ch Ch).comap (A.mode 0 x)) ?_ : _ ≤ _) hy)
    intro b hb c hc
    show A.mode 0 x (A.mode 0 b c) ∈ A.zeroProd Ch Ch
    rw [A.zero_mode_comm (D.K_grade hx) (D.S₂_grade (hChS hb))]
    exact Submodule.add_mem _
      (VertexAlgebra.mem_zeroProd hb (D.currentSpan_stable _ hx hc))
      (VertexAlgebra.mem_zeroProd (D.currentSpan_stable _ hx hb) hc)
  have hEs : ∀ x ∈ D.S₃, A.mode 0 D.fL x ∈ D.S₃ := L.KS₃0 D.fL_mem
  have hFs : ∀ x ∈ D.S₃, A.mode 0 D.fR x ∈ D.S₃ := L.KS₃0 D.fR_mem
  let Cs : Submodule k D.S₃ := X.comap D.S₃.subtype
  have hE : ∀ x ∈ Cs, (A.mode 0 D.fL).restrict hEs x ∈ Cs := fun x hx =>
    hX _ D.fL_mem _ hx
  have hF : ∀ x ∈ Cs, (A.mode 0 D.fR).restrict hFs x ∈ Cs := fun x hx =>
    hX _ D.fR_mem _ hx
  have hspan' : ∀ v : D.S₃, ∃ x y c : D.S₃, c ∈ Cs ∧
      v = (A.mode 0 D.fL).restrict hEs x + (A.mode 0 D.fR).restrict hFs y + c := by
    intro v
    obtain ⟨y123, hy123, u₄, hu₄, hsum⟩ := Submodule.mem_sup.mp (G5.lowering_span v.2)
    obtain ⟨y12, hy12, u₃, hu₃, rfl⟩ := Submodule.mem_sup.mp hy123
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hy12
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hu₁
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hu₂
    have hu₃S : u₃ ∈ D.S₃ := (Submodule.span_le.mpr G5.chargedSeeds_S₃) hu₃
    have hu₄S : u₄ ∈ D.S₃ := L.N₃_le_S₃ hu₄
    have hu₃X : u₃ ∈ X :=
      (Submodule.span_le.mpr (fun v hv =>
        sup_le_sup_left L.fullN₃_le _ (G5.chargedSeeds_mem v hv)) : _ ≤ X) hu₃
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨u₃ + u₄, D.S₃.add_mem hu₃S hu₄S⟩, ?_, ?_⟩
    · show u₃ + u₄ ∈ X
      exact X.add_mem hu₃X (Submodule.mem_sup_right hu₄)
    · apply Subtype.ext
      show (v : V) = A.mode 0 D.fL x + A.mode 0 D.fR y + (u₃ + u₄)
      rw [← hsum]
      abel
  have hnil' : ∀ w : List Bool, w.length = 25 → ∀ v : D.S₃,
      CFT.raisingWord ((A.mode 0 D.fL).restrict hEs) ((A.mode 0 D.fR).restrict hFs) w v = 0 := by
    intro w hw v
    apply Subtype.ext
    rw [raisingWord_restrict, Submodule.coe_zero]
    exact hnilF w hw v v.2
  intro s hs
  exact CFT.nilpotent_raising_saturation Cs ((A.mode 0 D.fL).restrict hEs)
    ((A.mode 0 D.fR).restrict hFs) hE hF hspan' 25 hnil' ⟨s, hs⟩

/-- **Gate 5** (eq. `eq:gate5`): `(S₂)₀P₄ ⊂ N₅`. -/
theorem gate5 (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0) :
    ∀ a ∈ D.S₂, ∀ q ∈ D.P₄, A.mode 0 a q ∈ D.N₅ := by
  let M : Submodule k V := A.modeSpace 0 D.P₄ D.N₅
  -- the charged highest fields
  have hch : ∀ a ∈ G5.charged, a ∈ M ⊓ D.S₂ := by
    intro a ha
    have haS : a ∈ D.S₂ := G.highest_S₂ (G5.charged_sub ha)
    exact ⟨(A.mem_modeSpace).mpr (L.raise_triplet hG4 haS
      (G.highest_eR a (G5.charged_sub ha)) (L.charged_bottom hG4 haS (G5.bottom a ha))), haS⟩
  -- all charged fields (current covariance)
  have hChM : D.currentSpan G5.charged ≤ M ⊓ D.S₂ :=
    D.currentSpan_le hch (L.gate5_covariance hG4)
  -- the neutral field `e`
  have he : G5.e ∈ M ⊓ D.S₂ := by
    have heS : G5.e ∈ D.S₂ := G.highest_S₂ G5.e_mem
    have ha₃S : G5.a₃ ∈ D.S₂ := G.highest_S₂ (G5.charged_sub G5.a₃_mem)
    have ha₃M : ∀ w ∈ D.W₄, A.mode 0 G5.a₃ w ∈ D.N₅ :=
      L.zero_W₄ hG4 ha₃S ((A.mem_modeSpace).mp (hch _ G5.a₃_mem).1)
    -- `(e₀a₃)₀p₃ ∈ N₅`
    have h1 : A.mode 0 (A.mode 0 G5.e G5.a₃) G5.p₃ ∈ D.N₅ := by
      have hmem := L.charged_span hG4 G5 hnilF (L.S₂S₂0 _ heS _ ha₃S)
      obtain ⟨y, hy, n, hn, hyn⟩ := Submodule.mem_sup.mp hmem
      rw [← hyn, map_add, LinearMap.add_apply]
      refine D.N₅.add_mem ?_ (L.N₃S₃0 hG4 G5.p₃_mem n hn)
      refine (VertexAlgebra.zeroProd_le (Z := D.N₅.comap ((A.mode 0).flip G5.p₃)) ?_ :
        _ ≤ _) hy
      intro x hx z hz
      show A.mode 0 (A.mode 0 x z) G5.p₃ ∈ D.N₅
      have hxS := (hChM hx).2
      have hzS := (hChM hz).2
      rw [show A.mode 0 (A.mode 0 x z) G5.p₃ =
          A.mode 0 x (A.mode 0 z G5.p₃) - A.mode 0 z (A.mode 0 x G5.p₃) by
        rw [A.zero_mode_comm (D.S₂_grade hxS) (D.S₂_grade hzS)]; abel]
      exact D.N₅.sub_mem
        (L.zero_W₄ hG4 hxS ((A.mem_modeSpace).mp (hChM hx).1) _ (hG4 z hzS _ G5.p₃_mem))
        (L.zero_W₄ hG4 hzS ((A.mem_modeSpace).mp (hChM hz).1) _ (hG4 x hxS _ G5.p₃_mem))
    -- `e₀((a₃)₀p₃) ∈ N₅`
    have h2 : A.mode 0 G5.e (A.mode 0 G5.a₃ G5.p₃) ∈ D.N₅ := by
      rw [A.zero_mode_comm (D.S₂_grade heS) (D.S₂_grade ha₃S)]
      exact D.N₅.add_mem (ha₃M _ (hG4 _ heS _ G5.p₃_mem)) h1
    rw [G5.bottom₃, map_add, map_smul] at h2
    have h3 : G5.c₃ • A.mode 0 G5.e D.qm ∈ D.N₅ := by
      have := D.N₅.sub_mem h2 (L.S₂N₄0 hG4 heS _ (L.fullN₄_le G5.n₃_mem))
      rwa [add_sub_cancel_right] at this
    have hm : A.mode 0 G5.e D.qm ∈ D.N₅ := (D.N₅.smul_mem_iff G5.c₃_ne).mp h3
    exact ⟨(A.mem_modeSpace).mpr (L.raise_triplet hG4 heS (G.highest_eR _ G5.e_mem) hm), heS⟩
  -- the nine highest fields and their current modules
  have hcur : D.currentSpan G.highest ≤ M := by
    refine (D.currentSpan_le ?_ (L.gate5_covariance hG4)).trans inf_le_left
    intro a ha
    rcases G5.highest_sub ha with rfl | hac
    · exact he
    · exact hch a hac
  -- the affine vacuum vectors
  have hTK : D.K.map A.T ≤ M := VertexAlgebra.map_T_le fun x _ =>
    (A.mem_modeSpace).mpr fun q _ => by
      rw [A.mode_T_zero]
      exact D.N₅.zero_mem
  have hKK : A.negProd D.K D.K ≤ M := VertexAlgebra.negProd_le fun x hx y hy =>
    (A.mem_modeSpace).mpr fun q hq =>
      L.KK_zero_mem hx hy (D.P₄_grade hq) (L.K_W₄_sing hG4 hx (D.P₄_le_W₄ hq))
        (L.K_W₄_sing hG4 hy (D.P₄_le_W₄ hq))
  have hω : (k ∙ A.ω) ≤ M := by
    rw [Submodule.span_singleton_le_iff_mem]
    refine (A.mem_modeSpace).mpr fun q hq => ?_
    rw [A.Lm1]
    exact D.N₅_of_T (D.P₄_le_W₄ hq)
  intro a ha q hq
  have haM : a ∈ M := (sup_le (sup_le (sup_le hcur hTK) hKK) hω) (G.S₂_decomp ha)
  exact (A.mem_modeSpace).mp haM q hq

end Gate5

end LowerCertificate

#print axioms LowerCertificate.S₂S₃1
#print axioms LowerCertificate.L1N₅
#print axioms LowerCertificate.L2N₅
#print axioms LowerCertificate.charged_bottom
#print axioms LowerCertificate.gate5

end HaagerupIzumi.C8
