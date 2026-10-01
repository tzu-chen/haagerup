module

public import HaagerupIzumi.C8.Properness.Setup
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Consequences of the lower identities

Everything here is derived from `LowerCertificate` and general vertex-algebra identities;
it precedes Gate 4 in the manuscript (`haagerup_c8_expanded.tex`, lines 2209–2266 and the
first part of the proof of Lemma `lem:bootstrap`, lines 2363–2387).

* The *ladder* `ℂ1 ⊂ K, S₂, S₃, W₄, N₅` is stable under `T` and under `x_(-1)` for
  `x ∈ K` (raising the weight by one) and `a_(-1)` for `a ∈ S₂` (by two).  Consequently all
  negative modes `x_(-r)`, `a_(-r)` (proof of Lemma `lem:normal-controls`, line 2460) and
  the skew-symmetric reorderings needed below stay in the ladder.
* Current zero modes preserve `S₃, N₃, N₄, P₄, W₄, N₅`; `(S₂)₀N₃ ⊂ N₄`.
* `K₁S₃ ⊂ S₂`, `K₂S₃ ⊂ K`, `L(1)S₃ ⊂ S₂`, `L(2)S₃ ⊂ K` (line 2368, eq. `eq:k1-provenance`,
  and line 2381), and `L(1)N₄ ⊂ S₃`, `L(2)N₄ ⊂ S₂`, `K₁N₄ ⊂ S₃` (line 2383).
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace VertexAlgebra

variable (A : VertexAlgebra k V)

/-- `x₁ (T a) = T (x₁ a) + x₀ a`. -/
theorem one_mode_T (x a : V) : A.mode 1 x (A.T a) = A.T (A.mode 1 x a) + A.mode 0 x a := by
  have h := A.T_mode 1 x a
  rw [A.mode_T, show (1 : ℤ) - 1 = 0 by norm_num] at h
  rw [h]
  push_cast
  module

end VertexAlgebra

namespace VertexOperatorAlgebra

variable (A : VertexOperatorAlgebra k V) [CharZero k]

/-- Solved form of `[L(1), x_(n)]`, `x` of weight one. -/
theorem L1_wt1_mem {X : Submodule k V} {x c : V} (hx : x ∈ A.grade 1) {n : ℤ} (hn : n ≠ 0)
    (h1 : A.mode 2 A.ω (A.mode n x c) ∈ X) (h2 : A.mode n x (A.mode 2 A.ω c) ∈ X)
    (h3 : A.mode n (A.mode 2 A.ω x) c ∈ X) : A.mode (n + 1) x c ∈ X := by
  have h := A.L1_comm_wt1 hx n c
  have e : (n : k) • A.mode (n + 1) x c =
      A.mode n x (A.mode 2 A.ω c) + A.mode n (A.mode 2 A.ω x) c
        - A.mode 2 A.ω (A.mode n x c) := by
    rw [h]; abel
  have hm : (n : k) • A.mode (n + 1) x c ∈ X := by
    rw [e]; exact X.sub_mem (X.add_mem h2 h3) h1
  exact (X.smul_mem_iff (Int.cast_ne_zero.mpr hn)).mp hm

/-- Solved form of `[L(2), x_(n)]`, `x` of weight one. -/
theorem L2_wt1_mem {X : Submodule k V} {x c : V} (hx : x ∈ A.grade 1) {n : ℤ} (hn : n ≠ 0)
    (h1 : A.mode 3 A.ω (A.mode n x c) ∈ X) (h2 : A.mode n x (A.mode 3 A.ω c) ∈ X)
    (h3 : A.mode (n + 1) (A.mode 2 A.ω x) c ∈ X) : A.mode (n + 2) x c ∈ X := by
  have h := A.L2_comm_wt1 hx n c
  have e : (n : k) • A.mode (n + 2) x c =
      A.mode n x (A.mode 3 A.ω c) + (3 : k) • A.mode (n + 1) (A.mode 2 A.ω x) c
        - A.mode 3 A.ω (A.mode n x c) := by
    rw [h]; abel
  have hm : (n : k) • A.mode (n + 2) x c ∈ X := by
    rw [e]; exact X.sub_mem (X.add_mem h2 (X.smul_mem _ h3)) h1
  exact (X.smul_mem_iff (Int.cast_ne_zero.mpr hn)).mp hm

/-- Solved form of eq. `eq:L1-weight2`. -/
theorem L1_wt2_mem {X : Submodule k V} {a c : V} (ha : a ∈ A.grade 2) {n : ℤ} (hn : n ≠ 2)
    (h1 : A.mode 2 A.ω (A.mode n a c) ∈ X) (h2 : A.mode n a (A.mode 2 A.ω c) ∈ X)
    (h3 : A.mode n (A.mode 2 A.ω a) c ∈ X) : A.mode (n + 1) a c ∈ X := by
  have h := A.L1_comm_wt2 ha n c
  have e : ((2 : k) - n) • A.mode (n + 1) a c =
      A.mode 2 A.ω (A.mode n a c) - A.mode n a (A.mode 2 A.ω c)
        - A.mode n (A.mode 2 A.ω a) c := by
    rw [h]; abel
  have hne : ((2 : k) - n) ≠ 0 := by
    have : ((2 - n : ℤ) : k) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    push_cast at this
    exact this
  have hm : ((2 : k) - n) • A.mode (n + 1) a c ∈ X := by
    rw [e]; exact X.sub_mem (X.sub_mem h1 h2) h3
  exact (X.smul_mem_iff hne).mp hm

/-- Solved form of eq. `eq:L2-weight2`. -/
theorem L2_wt2_mem {X : Submodule k V} {a c : V} (ha : a ∈ A.grade 2) {n : ℤ} (hn : n ≠ 3)
    (h1 : A.mode 3 A.ω (A.mode n a c) ∈ X) (h2 : A.mode n a (A.mode 3 A.ω c) ∈ X)
    (h3 : A.mode (n + 1) (A.mode 2 A.ω a) c ∈ X) (h4 : A.mode n (A.mode 3 A.ω a) c ∈ X) :
    A.mode (n + 2) a c ∈ X := by
  have h := A.L2_comm_wt2 ha n c
  have e : ((3 : k) - n) • A.mode (n + 2) a c =
      A.mode 3 A.ω (A.mode n a c) - A.mode n a (A.mode 3 A.ω c)
        - (3 : k) • A.mode (n + 1) (A.mode 2 A.ω a) c - A.mode n (A.mode 3 A.ω a) c := by
    rw [h]; abel
  have hne : ((3 : k) - n) ≠ 0 := by
    have : ((3 - n : ℤ) : k) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    push_cast at this
    exact this
  have hm : ((3 : k) - n) • A.mode (n + 2) a c ∈ X := by
    rw [e]; exact X.sub_mem (X.sub_mem (X.sub_mem h1 h2) (X.smul_mem _ h3)) h4
  exact (X.smul_mem_iff hne).mp hm

end VertexOperatorAlgebra

namespace LowerCertificate

variable [CharZero k] {A : VertexOperatorAlgebra k V} {D : ClosureData A}
variable (L : LowerCertificate D)
include L

/-! ### Small weight facts -/

theorem L1_K_grade {x : V} (hx : x ∈ D.K) : A.mode 2 A.ω x ∈ A.grade 0 :=
  A.mode_mem_grade A.ω_mem (D.K_grade hx) (by norm_num)

theorem L2_S₂_grade {a : V} (ha : a ∈ D.S₂) : A.mode 3 A.ω a ∈ A.grade 0 :=
  A.mode_mem_grade A.ω_mem (D.S₂_grade ha) (by norm_num)

theorem L1_S₂ {a : V} (ha : a ∈ D.S₂) : A.mode 2 A.ω a ∈ D.K :=
  L.S₂S₂2 _ L.ω_mem a ha

/-! ### The ladder -/

theorem ladder_T : ∀ d : ℕ, ∀ x ∈ D.ladder d, A.T x ∈ D.ladder (d + 1)
  | 0, x, hx => by
      show A.T x ∈ D.K
      rw [A.T_grade_zero hx]
      exact Submodule.zero_mem _
  | 1, x, hx => L.TK x hx
  | 2, x, hx => L.N₃_le_S₃ (D.N₃_of_T hx)
  | 3, x, hx => D.N₄_le_W₄ (D.N₄_of_T hx)
  | 4, x, hx => D.N₅_of_T hx
  | _ + 5, _, _ => Submodule.mem_top

theorem T_pow_ladder : ∀ t d : ℕ, ∀ x ∈ D.ladder d, (A.T ^ t) x ∈ D.ladder (d + t)
  | 0, d, x, hx => by simpa using hx
  | t + 1, d, x, hx => by
      rw [pow_succ', Module.End.mul_apply]
      have := L.ladder_T (d + t) _ (T_pow_ladder t d x hx)
      rwa [show d + t + 1 = d + (t + 1) by omega] at this

theorem ladder_K : ∀ d : ℕ, ∀ x ∈ D.K, ∀ v ∈ D.ladder d, A.mode (-1) x v ∈ D.ladder (d + 1)
  | 0, x, hx, v, hv => by
      obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_right hv x
      show A.mode (-1) x v ∈ D.K
      rw [hr]
      exact D.K.smul_mem r hx
  | 1, x, hx, v, hv => L.KmK x hx v hv
  | 2, _, hx, _, hv => L.N₃_le_S₃ (D.N₃_of_K_S₂ hx hv)
  | 3, _, hx, _, hv => D.N₄_le_W₄ (D.N₄_of_K_S₃ hx hv)
  | 4, _, hx, _, hv => D.N₅_of_K_W₄ hx hv
  | _ + 5, _, _, _, _ => Submodule.mem_top

/-- Skew symmetry into the ladder, nonnegative modes: if all singular products `x_(m) y`
lie in the ladder at their weights, so do all `y_(n) x`. -/
theorem skew_ladder {w e : ℕ} {x y : V} (hx : x ∈ A.grade w) (hy : y ∈ A.grade e)
    (hsing : ∀ m : ℕ, m < w + e → A.mode (m : ℤ) x y ∈ D.ladder (w + e - m - 1))
    (n : ℕ) : A.mode (n : ℤ) y x ∈ D.ladder (w + e - n - 1) := by
  refine A.skew_mem hx hy n fun t _ => ?_
  by_cases hnt : n + t < w + e
  · have := L.T_pow_ladder t _ _ (hsing (n + t) hnt)
    rw [show w + e - (n + t) - 1 + t = w + e - n - 1 by omega] at this
    simpa using this
  · rw [A.mode_trunc ((n : ℤ) + t) hx hy (by omega), map_zero]
    exact Submodule.zero_mem _

/-- Skew symmetry into the ladder for the `(-1)`-product: reordering a normal product. -/
theorem reorder_mem {w e : ℕ} {x y : V} (hx : x ∈ A.grade w) (hy : y ∈ A.grade e)
    (h0 : A.mode (-1) x y ∈ D.ladder (w + e))
    (hsing : ∀ m : ℕ, m < w + e → A.mode (m : ℤ) x y ∈ D.ladder (w + e - m - 1)) :
    A.mode (-1) y x ∈ D.ladder (w + e) := by
  refine A.skew_mem hx hy (-1) fun t ht => ?_
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simpa using h0
  · have ht' : t ≤ w + e := by simp at ht; omega
    have := L.T_pow_ladder t _ _ (hsing (t - 1) (by omega))
    rw [show w + e - (t - 1) - 1 + t = w + e by omega] at this
    rw [show (-1 : ℤ) + t = ((t - 1 : ℕ) : ℤ) by omega]
    exact this

/-- The singular products `x_(m) a`, `x ∈ K`, `a ∈ S₂`, lie in the ladder. -/
theorem K_S₂_sing {x a : V} (hx : x ∈ D.K) (ha : a ∈ D.S₂) :
    ∀ m : ℕ, m < 1 + 2 → A.mode (m : ℤ) x a ∈ D.ladder (1 + 2 - m - 1) := by
  intro m hm
  interval_cases m
  · exact L.KS₂0 x hx a ha
  · exact L.KS₂1 x hx a ha
  · exact A.mode_mem_grade (D.K_grade hx) (D.S₂_grade ha) (by norm_num)

/-- `(S₂)₀K ⊂ S₂` (skew symmetry). -/
theorem S₂K0 {a x : V} (ha : a ∈ D.S₂) (hx : x ∈ D.K) : A.mode 0 a x ∈ D.S₂ :=
  L.skew_ladder (D.K_grade hx) (D.S₂_grade ha) (L.K_S₂_sing hx ha) 0

/-- `(S₂)₁K ⊂ K` (skew symmetry). -/
theorem S₂K1 {a x : V} (ha : a ∈ D.S₂) (hx : x ∈ D.K) : A.mode 1 a x ∈ D.K :=
  L.skew_ladder (D.K_grade hx) (D.S₂_grade ha) (L.K_S₂_sing hx ha) 1

/-- `(S₂)₋₁K ⊂ S₃` (skew symmetry). -/
theorem S₂mK {a x : V} (ha : a ∈ D.S₂) (hx : x ∈ D.K) : A.mode (-1) a x ∈ D.S₃ :=
  L.reorder_mem (D.K_grade hx) (D.S₂_grade ha) (L.N₃_le_S₃ (D.N₃_of_K_S₂ hx ha))
    (L.K_S₂_sing hx ha)

theorem ladder_S₂ :
    ∀ d : ℕ, ∀ a ∈ D.S₂, ∀ v ∈ D.ladder d, A.mode (-1) a v ∈ D.ladder (d + 2)
  | 0, a, ha, v, hv => by
      obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_right hv a
      show A.mode (-1) a v ∈ D.S₂
      rw [hr]
      exact D.S₂.smul_mem r ha
  | 1, _, ha, _, hv => L.S₂mK ha hv
  | 2, _, ha, _, hv => D.N₄_le_W₄ (D.N₄_of_S₂_S₂ ha hv)
  | 3, _, ha, _, hv => D.N₅_of_S₂_S₃ ha hv
  | _ + 4, _, _, _, _ => Submodule.mem_top

/-- Negative modes of currents climb the ladder: `x_(-r-1) (ladder d) ⊂ ladder (d+r+1)`. -/
theorem neg_mode_K {x : V} (hx : x ∈ D.K) :
    ∀ r d : ℕ, ∀ v ∈ D.ladder d, A.mode (-(r : ℤ) - 1) x v ∈ D.ladder (d + r + 1)
  | 0, d, v, hv => by simpa using L.ladder_K d x hx v hv
  | r + 1, d, v, hv => by
      rw [show (-((r + 1 : ℕ) : ℤ) - 1) = (-(r : ℤ) - 1) - 1 by push_cast; ring]
      refine A.mode_pred_mem (by omega) ?_ ?_
      · have := neg_mode_K hx r (d + 1) (A.T v) (L.ladder_T d v hv)
        rwa [show d + 1 + r + 1 = d + (r + 1) + 1 by omega] at this
      · have := L.ladder_T (d + r + 1) _ (neg_mode_K hx r d v hv)
        rwa [show d + r + 1 + 1 = d + (r + 1) + 1 by omega] at this

/-- Negative modes of `S₂`: `a_(-r-1) (ladder d) ⊂ ladder (d+r+2)`. -/
theorem neg_mode_S₂ {a : V} (ha : a ∈ D.S₂) :
    ∀ r d : ℕ, ∀ v ∈ D.ladder d, A.mode (-(r : ℤ) - 1) a v ∈ D.ladder (d + r + 2)
  | 0, d, v, hv => by simpa using L.ladder_S₂ d a ha v hv
  | r + 1, d, v, hv => by
      rw [show (-((r + 1 : ℕ) : ℤ) - 1) = (-(r : ℤ) - 1) - 1 by push_cast; ring]
      refine A.mode_pred_mem (by omega) ?_ ?_
      · have := neg_mode_S₂ ha r (d + 1) (A.T v) (L.ladder_T d v hv)
        rwa [show d + 1 + r + 2 = d + (r + 1) + 2 by omega] at this
      · have := L.ladder_T (d + r + 2) _ (neg_mode_S₂ ha r d v hv)
        rwa [show d + r + 2 + 1 = d + (r + 1) + 2 by omega] at this

/-! ### Generators of the spaces -/

theorem S₃_le_comap {X : Submodule k V} (f : V →ₗ[k] V)
    (h1 : ∀ x ∈ D.K, ∀ a ∈ D.S₂, f (A.mode (-1) x a) ∈ X)
    (h2 : ∀ a ∈ D.S₂, f (A.T a) ∈ X)
    (h3 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, f (A.mode 0 a b) ∈ X) :
    ∀ s ∈ D.S₃, f s ∈ X := fun _ hs =>
  (sup_le (sup_le (VertexAlgebra.negProd_le (Z := X.comap f) h1)
    (VertexAlgebra.map_T_le (Z := X.comap f) h2))
    (VertexAlgebra.zeroProd_le (Z := X.comap f) h3) : _ ≤ X.comap f) (L.S₃_prov hs)

omit L in
theorem N₃_le_comap {X : Submodule k V} (f : V →ₗ[k] V)
    (h1 : ∀ x ∈ D.K, ∀ a ∈ D.S₂, f (A.mode (-1) x a) ∈ X)
    (h2 : ∀ a ∈ D.S₂, f (A.T a) ∈ X) : ∀ v ∈ D.N₃, f v ∈ X := fun _ hv =>
  (sup_le (VertexAlgebra.negProd_le (Z := X.comap f) h1)
    (VertexAlgebra.map_T_le (Z := X.comap f) h2) : _ ≤ X.comap f) hv

omit L in
theorem N₄_le_comap {X : Submodule k V} (f : V →ₗ[k] V)
    (h1 : ∀ x ∈ D.K, ∀ s ∈ D.S₃, f (A.mode (-1) x s) ∈ X)
    (h2 : ∀ s ∈ D.S₃, f (A.T s) ∈ X)
    (h3 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, f (A.mode (-1) a b) ∈ X) : ∀ v ∈ D.N₄, f v ∈ X :=
  fun _ hv =>
  (sup_le (sup_le (VertexAlgebra.negProd_le (Z := X.comap f) h1)
    (VertexAlgebra.map_T_le (Z := X.comap f) h2))
    (VertexAlgebra.negProd_le (Z := X.comap f) h3) : _ ≤ X.comap f) hv

omit L in
theorem N₅_le_comap {X : Submodule k V} (f : V →ₗ[k] V)
    (h1 : ∀ x ∈ D.K, ∀ w ∈ D.W₄, f (A.mode (-1) x w) ∈ X)
    (h2 : ∀ w ∈ D.W₄, f (A.T w) ∈ X)
    (h3 : ∀ a ∈ D.S₂, ∀ s ∈ D.S₃, f (A.mode (-1) a s) ∈ X) : ∀ v ∈ D.N₅, f v ∈ X :=
  fun _ hv =>
  (sup_le (sup_le (VertexAlgebra.negProd_le (Z := X.comap f) h1)
    (VertexAlgebra.map_T_le (Z := X.comap f) h2))
    (VertexAlgebra.negProd_le (Z := X.comap f) h3) : _ ≤ X.comap f) hv

/-! ### Current zero modes -/

theorem KS₃0 {x : V} (hx : x ∈ D.K) : ∀ s ∈ D.S₃, A.mode 0 x s ∈ D.S₃ := by
  refine L.S₃_le_comap (A.mode 0 x) ?_ ?_ ?_
  · intro y hy a ha
    rw [A.zero_mode_comm (D.K_grade hx) (D.K_grade hy)]
    exact D.S₃.add_mem (L.N₃_le_S₃ (D.N₃_of_K_S₂ hy (L.KS₂0 x hx a ha)))
      (L.N₃_le_S₃ (D.N₃_of_K_S₂ (L.KK0 x hx y hy) ha))
  · intro a ha
    rw [A.zero_mode_T]
    exact L.N₃_le_S₃ (D.N₃_of_T (L.KS₂0 x hx a ha))
  · intro a ha b hb
    rw [A.zero_mode_comm (D.K_grade hx) (D.S₂_grade ha)]
    exact D.S₃.add_mem (L.S₂S₂0 a ha _ (L.KS₂0 x hx b hb)) (L.S₂S₂0 _ (L.KS₂0 x hx a ha) b hb)

theorem KN₃0 {x : V} (hx : x ∈ D.K) : ∀ v ∈ D.N₃, A.mode 0 x v ∈ D.N₃ := by
  refine N₃_le_comap (A.mode 0 x) ?_ ?_
  · intro y hy a ha
    rw [A.zero_mode_comm (D.K_grade hx) (D.K_grade hy)]
    exact D.N₃.add_mem (D.N₃_of_K_S₂ hy (L.KS₂0 x hx a ha)) (D.N₃_of_K_S₂ (L.KK0 x hx y hy) ha)
  · intro a ha
    rw [A.zero_mode_T]
    exact D.N₃_of_T (L.KS₂0 x hx a ha)

theorem KN₄0 {x : V} (hx : x ∈ D.K) : ∀ v ∈ D.N₄, A.mode 0 x v ∈ D.N₄ := by
  refine N₄_le_comap (A.mode 0 x) ?_ ?_ ?_
  · intro y hy s hs
    rw [A.zero_mode_comm (D.K_grade hx) (D.K_grade hy)]
    exact D.N₄.add_mem (D.N₄_of_K_S₃ hy (L.KS₃0 hx s hs)) (D.N₄_of_K_S₃ (L.KK0 x hx y hy) hs)
  · intro s hs
    rw [A.zero_mode_T]
    exact D.N₄_of_T (L.KS₃0 hx s hs)
  · intro a ha b hb
    rw [A.zero_mode_comm (D.K_grade hx) (D.S₂_grade ha)]
    exact D.N₄.add_mem (D.N₄_of_S₂_S₂ ha (L.KS₂0 x hx b hb))
      (D.N₄_of_S₂_S₂ (L.KS₂0 x hx a ha) hb)

/-- The 18 current-zero-mode identities make `P₄` current-stable. -/
theorem KP₄0 : ∀ x ∈ D.K, ∀ q ∈ D.P₄, A.mode 0 x q ∈ D.P₄ := by
  refine VertexAlgebra.mode_span_mem 0 ?_
  intro x hx q hq
  simp only [ClosureData.currents, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hq' := hq
  simp only [ClosureData.triplet, Set.mem_insert_iff, Set.mem_singleton_iff] at hq'
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [L.hL_q q hq]; exact Submodule.zero_mem _
  · rw [L.eL_q q hq]; exact Submodule.zero_mem _
  · rw [L.fL_q q hq]; exact Submodule.zero_mem _
  · rcases hq' with rfl | rfl | rfl
    · rw [L.hR_qp]; exact D.P₄.smul_mem _ D.qp_mem
    · rw [L.hR_q0]; exact Submodule.zero_mem _
    · rw [L.hR_qm]; exact D.P₄.smul_mem _ D.qm_mem
  · rcases hq' with rfl | rfl | rfl
    · rw [L.eR_qp]; exact Submodule.zero_mem _
    · rw [L.eR_q0]; exact D.P₄.smul_mem _ D.qp_mem
    · rw [L.eR_qm]; exact D.P₄.smul_mem _ D.q0_mem
  · rcases hq' with rfl | rfl | rfl
    · rw [L.fR_qp]; exact D.q0_mem
    · rw [L.fR_q0]; exact D.qm_mem
    · rw [L.fR_qm]; exact Submodule.zero_mem _

theorem KW₄0 {x : V} (hx : x ∈ D.K) : ∀ w ∈ D.W₄, A.mode 0 x w ∈ D.W₄ := by
  intro w hw
  obtain ⟨n, hn, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact D.W₄.add_mem (D.N₄_le_W₄ (L.KN₄0 hx n hn)) (D.P₄_le_W₄ (L.KP₄0 x hx q hq))

theorem KN₅0 {x : V} (hx : x ∈ D.K) : ∀ v ∈ D.N₅, A.mode 0 x v ∈ D.N₅ := by
  refine N₅_le_comap (A.mode 0 x) ?_ ?_ ?_
  · intro y hy w hw
    rw [A.zero_mode_comm (D.K_grade hx) (D.K_grade hy)]
    exact D.N₅.add_mem (D.N₅_of_K_W₄ hy (L.KW₄0 hx w hw)) (D.N₅_of_K_W₄ (L.KK0 x hx y hy) hw)
  · intro w hw
    rw [A.zero_mode_T]
    exact D.N₅_of_T (L.KW₄0 hx w hw)
  · intro a ha s hs
    rw [A.zero_mode_comm (D.K_grade hx) (D.S₂_grade ha)]
    exact D.N₅.add_mem (D.N₅_of_S₂_S₃ ha (L.KS₃0 hx s hs)) (D.N₅_of_S₂_S₃ (L.KS₂0 x hx a ha) hs)

/-- `(S₂)₀N₃ ⊂ N₄` (manuscript line 2274: "the lower relations give `a₀N₃ ⊂ N₄`"). -/
theorem S₂N₃0 {a : V} (ha : a ∈ D.S₂) : ∀ v ∈ D.N₃, A.mode 0 a v ∈ D.N₄ := by
  refine N₃_le_comap (A.mode 0 a) ?_ ?_
  · intro y hy b hb
    rw [A.zero_mode_comm (D.S₂_grade ha) (D.K_grade hy)]
    exact D.N₄.add_mem (D.N₄_of_K_S₃ hy (L.S₂S₂0 a ha b hb)) (D.N₄_of_S₂_S₂ (L.S₂K0 ha hy) hb)
  · intro b hb
    rw [A.zero_mode_T]
    exact D.N₄_of_T (L.S₂S₂0 a ha b hb)

/-! ### Positive modes on `S₃` and `N₄` before Gate 4 -/

/-- `K₁S₃ ⊂ S₂` (eq. `eq:k1-provenance` with `b ∈ S₂`). -/
theorem KS₃1 {x : V} (hx : x ∈ D.K) : ∀ s ∈ D.S₃, A.mode 1 x s ∈ D.S₂ := by
  refine L.S₃_le_comap (A.mode 1 x) ?_ ?_ ?_
  · intro y hy a ha
    rw [A.one_mode_comm (D.K_grade hx) (D.K_grade hy) (by norm_num),
      show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left
      (A.mode_mem_grade (D.K_grade hx) (D.K_grade hy) (n := 1) (d := 0) (by norm_num)) a
    rw [hr]
    exact D.S₂.add_mem (D.S₂.add_mem (L.KmK y hy _ (L.KS₂1 x hx a ha))
      (L.KS₂0 _ (L.KK0 x hx y hy) a ha)) (D.S₂.smul_mem r ha)
  · intro a ha
    rw [A.one_mode_T]
    exact D.S₂.add_mem (L.TK _ (L.KS₂1 x hx a ha)) (L.KS₂0 x hx a ha)
  · intro a ha b hb
    rw [A.one_mode_comm (D.K_grade hx) (D.S₂_grade ha) (by norm_num),
      show (0 : ℤ) + 1 = 1 by norm_num]
    exact D.S₂.add_mem (D.S₂.add_mem (L.S₂K0 ha (L.KS₂1 x hx b hb))
      (L.S₂S₂1 _ (L.KS₂0 x hx a ha) b hb)) (L.KS₂0 _ (L.KS₂1 x hx a ha) b hb)

/-- `L(1)S₃ ⊂ S₂` (line 2381). -/
theorem L1S₃ : ∀ s ∈ D.S₃, A.mode 2 A.ω s ∈ D.S₂ := by
  refine L.S₃_le_comap (A.mode 2 A.ω) ?_ ?_ ?_
  · intro y hy a ha
    rw [A.L1_comm_wt1 (D.K_grade hy) (-1) a, show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left (L.L1_K_grade hy) a
    rw [hr]
    exact D.S₂.add_mem (D.S₂.sub_mem (L.KmK y hy _ (L.L1_S₂ ha))
      (D.S₂.smul_mem _ (L.KS₂0 y hy a ha))) (D.S₂.smul_mem r ha)
  · intro a ha
    rw [A.L1_T (D.S₂_grade ha)]
    exact D.S₂.add_mem (L.TK _ (L.L1_S₂ ha)) (D.S₂.smul_mem _ ha)
  · intro a ha b hb
    rw [A.L1_comm_wt2 (D.S₂_grade ha) 0 b, show (0 : ℤ) + 1 = 1 by norm_num]
    exact D.S₂.add_mem (D.S₂.add_mem (L.S₂K0 ha (L.L1_S₂ hb))
      (D.S₂.smul_mem _ (L.S₂S₂1 a ha b hb))) (L.KS₂0 _ (L.L1_S₂ ha) b hb)

/-- `L(2)S₃ ⊂ K` (line 2381). -/
theorem L2S₃ : ∀ s ∈ D.S₃, A.mode 3 A.ω s ∈ D.K := by
  refine L.S₃_le_comap (A.mode 3 A.ω) ?_ ?_ ?_
  · intro y hy a ha
    rw [A.L2_comm_wt1 (D.K_grade hy) (-1) a, show (-1 : ℤ) + 2 = 1 by norm_num,
      show (-1 : ℤ) + 1 = 0 by norm_num,
      A.mode_grade_zero_left (L.L1_K_grade hy) (n := 0) (by norm_num)]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_right (L.L2_S₂_grade ha) y
    rw [hr, smul_zero, add_zero]
    exact D.K.sub_mem (D.K.smul_mem r hy) (D.K.smul_mem _ (L.KS₂1 y hy a ha))
  · intro a ha
    rw [A.L2_T, A.T_grade_zero (L.L2_S₂_grade ha), zero_add]
    exact D.K.smul_mem _ (L.L1_S₂ ha)
  · intro a ha b hb
    rw [A.L2_comm_wt2 (D.S₂_grade ha) 0 b, show (0 : ℤ) + 2 = 2 by norm_num,
      show (0 : ℤ) + 1 = 1 by norm_num,
      A.mode_grade_zero_left (L.L2_S₂_grade ha) (n := 0) (by norm_num)]
    obtain ⟨r, hr⟩ := A.exists_smul_vac (L.L2_S₂_grade hb)
    rw [hr, map_smul, A.mode_vac_nonneg 0 a le_rfl, smul_zero, zero_add, add_zero]
    exact D.K.add_mem (D.K.smul_mem _ (L.S₂S₂2 a ha b hb))
      (D.K.smul_mem _ (L.KS₂1 _ (L.L1_S₂ ha) b hb))

/-- `K₂S₃ ⊂ K`, from `[L(1), x₁] = -x₂` (line 2409). -/
theorem KS₃2 {x : V} (hx : x ∈ D.K) {s : V} (hs : s ∈ D.S₃) : A.mode 2 x s ∈ D.K := by
  have := A.L1_wt1_mem (X := D.K) (D.K_grade hx) (n := 1) (by norm_num)
    (L.L1_S₂ (L.KS₃1 hx s hs)) (L.KS₂1 x hx _ (L.L1S₃ s hs))
    (by rw [A.mode_grade_zero_left (L.L1_K_grade hx) (n := 1) (by norm_num)]
        exact Submodule.zero_mem _)
  simpa using this

/-- `L(1)N₄ ⊂ S₃` (line 2383). -/
theorem L1N₄ : ∀ v ∈ D.N₄, A.mode 2 A.ω v ∈ D.S₃ := by
  refine N₄_le_comap (A.mode 2 A.ω) ?_ ?_ ?_
  · intro y hy s hs
    rw [A.L1_comm_wt1 (D.K_grade hy) (-1) s, show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left (L.L1_K_grade hy) s
    rw [hr]
    exact D.S₃.add_mem (D.S₃.sub_mem (L.N₃_le_S₃ (D.N₃_of_K_S₂ hy (L.L1S₃ s hs)))
      (D.S₃.smul_mem _ (L.KS₃0 hy s hs))) (D.S₃.smul_mem r hs)
  · intro s hs
    rw [A.L1_T (D.S₃_grade hs)]
    exact D.S₃.add_mem (L.N₃_le_S₃ (D.N₃_of_T (L.L1S₃ s hs))) (D.S₃.smul_mem _ hs)
  · intro a ha b hb
    rw [A.L1_comm_wt2 (D.S₂_grade ha) (-1) b, show (-1 : ℤ) + 1 = 0 by norm_num]
    exact D.S₃.add_mem (D.S₃.add_mem (L.S₂mK ha (L.L1_S₂ hb))
      (D.S₃.smul_mem _ (L.S₂S₂0 a ha b hb))) (L.N₃_le_S₃ (D.N₃_of_K_S₂ (L.L1_S₂ ha) hb))

/-- `L(2)N₄ ⊂ S₂` (line 2383; the scalar term `(L(2)a)₋₁b` is kept). -/
theorem L2N₄ : ∀ v ∈ D.N₄, A.mode 3 A.ω v ∈ D.S₂ := by
  refine N₄_le_comap (A.mode 3 A.ω) ?_ ?_ ?_
  · intro y hy s hs
    rw [A.L2_comm_wt1 (D.K_grade hy) (-1) s, show (-1 : ℤ) + 2 = 1 by norm_num,
      show (-1 : ℤ) + 1 = 0 by norm_num,
      A.mode_grade_zero_left (L.L1_K_grade hy) (n := 0) (by norm_num), smul_zero, add_zero]
    exact D.S₂.sub_mem (L.KmK y hy _ (L.L2S₃ s hs)) (D.S₂.smul_mem _ (L.KS₃1 hy s hs))
  · intro s hs
    rw [A.L2_T]
    exact D.S₂.add_mem (L.TK _ (L.L2S₃ s hs)) (D.S₂.smul_mem _ (L.L1S₃ s hs))
  · intro a ha b hb
    rw [A.L2_comm_wt2 (D.S₂_grade ha) (-1) b, show (-1 : ℤ) + 2 = 1 by norm_num,
      show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_right (L.L2_S₂_grade hb) a
    obtain ⟨r', hr'⟩ := A.mode_neg_one_grade_zero_left (L.L2_S₂_grade ha) b
    rw [hr, hr']
    exact D.S₂.add_mem (D.S₂.add_mem (D.S₂.add_mem (D.S₂.smul_mem r ha)
      (D.S₂.smul_mem _ (L.S₂S₂1 a ha b hb)))
      (D.S₂.smul_mem _ (L.KS₂0 _ (L.L1_S₂ ha) b hb))) (D.S₂.smul_mem r' hb)

/-- `K₁N₄ ⊂ S₃` (line 2406: "the same inclusion for `N₄` follows on its normal
generators"). -/
theorem KN₄1 {x : V} (hx : x ∈ D.K) : ∀ v ∈ D.N₄, A.mode 1 x v ∈ D.S₃ := by
  refine N₄_le_comap (A.mode 1 x) ?_ ?_ ?_
  · intro y hy s hs
    rw [A.one_mode_comm (D.K_grade hx) (D.K_grade hy) (by norm_num),
      show (-1 : ℤ) + 1 = 0 by norm_num]
    obtain ⟨r, hr⟩ := A.mode_neg_one_grade_zero_left
      (A.mode_mem_grade (D.K_grade hx) (D.K_grade hy) (n := 1) (d := 0) (by norm_num)) s
    rw [hr]
    exact D.S₃.add_mem (D.S₃.add_mem (L.N₃_le_S₃ (D.N₃_of_K_S₂ hy (L.KS₃1 hx s hs)))
      (L.KS₃0 (L.KK0 x hx y hy) s hs)) (D.S₃.smul_mem r hs)
  · intro s hs
    rw [A.one_mode_T]
    exact D.S₃.add_mem (L.N₃_le_S₃ (D.N₃_of_T (L.KS₃1 hx s hs))) (L.KS₃0 hx s hs)
  · intro a ha b hb
    rw [A.one_mode_comm (D.K_grade hx) (D.S₂_grade ha) (by norm_num),
      show (-1 : ℤ) + 1 = 0 by norm_num]
    exact D.S₃.add_mem (D.S₃.add_mem (L.S₂mK ha (L.KS₂1 x hx b hb))
      (L.S₂S₂0 _ (L.KS₂0 x hx a ha) b hb)) (L.N₃_le_S₃ (D.N₃_of_K_S₂ (L.KS₂1 x hx a ha) hb))

/-- `L(1)W₄ ⊂ S₃`, using the three direct controls `L(1)P₄ ⊂ S₃`. -/
theorem L1W₄ : ∀ w ∈ D.W₄, A.mode 2 A.ω w ∈ D.S₃ := by
  intro w hw
  obtain ⟨n, hn, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  refine D.S₃.add_mem (L.L1N₄ n hn) ?_
  exact (Submodule.span_le.mpr fun q hq => L.L1_P₄ q hq :
    D.P₄ ≤ D.S₃.comap (A.mode 2 A.ω)) hq

/-- `L(2)W₄ ⊂ S₂`, using the three direct controls `L(2)P₄ ⊂ S₂`. -/
theorem L2W₄ : ∀ w ∈ D.W₄, A.mode 3 A.ω w ∈ D.S₂ := by
  intro w hw
  obtain ⟨n, hn, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  refine D.S₂.add_mem (L.L2N₄ n hn) ?_
  exact (Submodule.span_le.mpr fun q hq => L.L2_P₄ q hq :
    D.P₄ ≤ D.S₂.comap (A.mode 3 A.ω)) hq

end LowerCertificate

#print axioms LowerCertificate.reorder_mem
#print axioms LowerCertificate.neg_mode_K
#print axioms LowerCertificate.neg_mode_S₂
#print axioms LowerCertificate.KS₃1
#print axioms LowerCertificate.L1S₃
#print axioms LowerCertificate.L2S₃
#print axioms LowerCertificate.L1N₄
#print axioms LowerCertificate.L2N₄
#print axioms LowerCertificate.KN₄1
#print axioms LowerCertificate.S₂N₃0

end HaagerupIzumi.C8
