module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsFieldIterate

@[expose] public section

/-!
# Fields on a vector space and their `n`-th products

W3, item (1), route A groundwork (`Lattice/W3_PLAN.md`, section 2).  Abstract setting, no mode
algebra and no grading:

* `OpField k V`: an operator family `A_u ∈ End V` (`u ∈ ℤ`) with `A_u v = 0` for `u ≫ 0`
  (depending on `v`), i.e. a field `A(z) = ∑ A_u z^{-u-1}`;
* `OpField.prod n A B`: the **`n`-th product of fields**,
  `(A_(n) B)_s v = ∑_{t ≥ 0} (-1)^t (n choose t) (A_{n-t} B_{s+t} v - (-1)^n B_{n+s-t} A_t v)`,
  a finite sum on each `v` (`prodTerm_eventually_zero`), linear in `v`, and again a field
  (`prod`'s truncation);
* `prodMode_eq_sum`: the finite-sum representation with any large range;
* `prod_natCast_eq_dz`: for `n = N ≥ 0`, `(A_(N) B)_s = dz N [A, B] (0, s)`; hence
  `prod_eq_zero_of_local`: if `A, B` are local of order `N` then `A_(n) B = 0` for `n ≥ N`;
* `commutator_of_local_prod`: the commutator formula
  `[A_p, B_q] = ∑_{j<N} (p choose j) (A_(j) B)_{p+q-j}` for a local pair (from the decomposition
  theorem `eq_sum_of_dz_eq_zero`).

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-- A field on `V`: an operator family `A_u` with `A_u v = 0` for `u ≫ 0`. -/
structure OpField (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] where
  /-- The modes `A_u`. -/
  mode : ℤ → Module.End k V
  /-- Truncation: `A_u v = 0` for `u` large (depending on `v`). -/
  trunc : ∀ v : V, ∃ N : ℤ, ∀ u, N ≤ u → mode u v = 0

namespace OpField

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Uniform truncation on finitely many vectors. -/
theorem trunc_finite (B : OpField k V) (f : ℕ → V) (T : ℕ) :
    ∃ N : ℤ, ∀ t < T, ∀ u, N ≤ u → B.mode u (f t) = 0 := by
  induction T with
  | zero => exact ⟨0, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | succ T ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨N', hN'⟩ := B.trunc (f T)
    refine ⟨max N N', fun t ht u hu => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
    · exact hN t h u (le_of_max_le_left hu)
    · subst h
      exact hN' u (le_of_max_le_right hu)

/-- The summand of `(A_(n) B)_s v`. -/
def prodTerm (A B : OpField k V) (n s : ℤ) (v : V) (t : ℕ) : V :=
  ((-1 : k) ^ t * zbinom k n t) •
    (A.mode (n - t) (B.mode (s + t) v) - (-1 : k) ^ n • B.mode (n + s - t) (A.mode t v))

theorem prodTerm_eventually_zero (A B : OpField k V) (n s : ℤ) (v : V) :
    ∃ N₀ : ℕ, ∀ t, N₀ ≤ t → prodTerm A B n s v t = 0 := by
  obtain ⟨NA, hA⟩ := A.trunc v
  obtain ⟨NB, hB⟩ := B.trunc v
  refine ⟨NA.toNat + (NB - s).toNat, fun t ht => ?_⟩
  unfold prodTerm
  rw [hB (s + t) (by omega), hA t (by omega)]
  simp

theorem support_prodTerm_finite (A B : OpField k V) (n s : ℤ) (v : V) :
    (Function.support (prodTerm A B n s v)).Finite := by
  obtain ⟨N₀, h⟩ := prodTerm_eventually_zero A B n s v
  refine (Set.finite_Iio N₀).subset fun t ht => ?_
  rw [Set.mem_Iio]
  by_contra hc
  exact ht (h t (not_lt.1 hc))

theorem prodTerm_add (A B : OpField k V) (n s : ℤ) (v w : V) (t : ℕ) :
    prodTerm A B n s (v + w) t = prodTerm A B n s v t + prodTerm A B n s w t := by
  unfold prodTerm
  simp only [map_add]
  module

theorem prodTerm_smul (A B : OpField k V) (n s : ℤ) (μ : k) (v : V) (t : ℕ) :
    prodTerm A B n s (μ • v) t = μ • prodTerm A B n s v t := by
  unfold prodTerm
  simp only [map_smul]
  module

/-- The mode `(A_(n) B)_s` as a linear map. -/
noncomputable def prodMode (A B : OpField k V) (n s : ℤ) : Module.End k V where
  toFun v := ∑ᶠ t : ℕ, prodTerm A B n s v t
  map_add' v w := by
    rw [← finsum_add_distrib (support_prodTerm_finite A B n s v)
      (support_prodTerm_finite A B n s w)]
    exact finsum_congr fun t => prodTerm_add A B n s v w t
  map_smul' μ v := by
    rw [RingHom.id_apply, smul_finsum' μ (support_prodTerm_finite A B n s v)]
    exact finsum_congr fun t => prodTerm_smul A B n s μ v t

theorem prodMode_apply (A B : OpField k V) (n s : ℤ) (v : V) :
    prodMode A B n s v = ∑ᶠ t : ℕ, prodTerm A B n s v t := rfl

/-- The finite-sum representation of `(A_(n) B)_s v`. -/
theorem prodMode_eq_sum (A B : OpField k V) (n s : ℤ) (v : V) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → prodMode A B n s v = ∑ t ∈ Finset.range N, prodTerm A B n s v t := by
  obtain ⟨N₀, h⟩ := prodTerm_eventually_zero A B n s v
  refine ⟨N₀, fun N hN => finsum_eq_sum_of_support_subset _ fun t ht => ?_⟩
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact ht (h t (by omega))

/-- **The `n`-th product of two fields** is a field. -/
noncomputable def prod (n : ℤ) (A B : OpField k V) : OpField k V where
  mode s := prodMode A B n s
  trunc v := by
    obtain ⟨NA, hA⟩ := A.trunc v
    obtain ⟨NB, hB⟩ := B.trunc v
    obtain ⟨N', hN'⟩ := B.trunc_finite (fun t => A.mode t v) NA.toNat
    refine ⟨max NB (N' + NA.toNat - n), fun s hs => ?_⟩
    rw [prodMode_apply]
    refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
    unfold prodTerm
    rw [hB (s + t) (by omega)]
    rcases lt_or_ge t NA.toNat with ht | ht
    · rw [hN' t ht (n + s - t) (by omega)]
      simp
    · rw [hA t (by omega)]
      simp

theorem prod_mode (n : ℤ) (A B : OpField k V) (s : ℤ) : (prod n A B).mode s = prodMode A B n s :=
  rfl

/-- For `n = N ≥ 0`: `(A_(N) B)_s = dz N [A, B] (0, s)`. -/
theorem prod_natCast_eq_dz (A B : OpField k V) (N : ℕ) (s : ℤ) :
    (prod N A B).mode s = dz k N (opComm A.mode B.mode) 0 s := by
  refine LinearMap.ext fun v => ?_
  rw [prod_mode, prodMode_apply, dz_linearMap_apply,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_]
  · -- reflect the `B A` part
    have hs : dz k N (fun u w => B.mode w (A.mode u v)) 0 s =
        (-1 : k) ^ N • ∑ t ∈ Finset.range (N + 1), ((-1 : k) ^ t * (N.choose t : k)) •
          B.mode (s + N - t) (A.mode (0 + t) v) := by
      have h := dz_swap k N (fun u w => B.mode w (A.mode u v)) 0 s
      have h2 : dz k N (fun u w => B.mode w (A.mode u v)) 0 s =
          (-1 : k) ^ N • dz k N (fun u w => B.mode u (A.mode w v)) s 0 := by
        rw [h, smul_smul, neg_one_pow_mul_self, one_smul]
      rw [h2]
      rfl
    have hsplit : dz k N (fun u w => opComm A.mode B.mode u w v) 0 s =
        dz k N (fun u w => A.mode u (B.mode w v)) 0 s -
          dz k N (fun u w => B.mode w (A.mode u v)) 0 s := by
      rw [← dz_sub_fun]
      rfl
    rw [hsplit, hs]
    unfold dz prodTerm
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [zbinom_natCast, zpow_natCast, zero_add]
    rw [show s + (N : ℤ) - (t : ℤ) = (N : ℤ) + s - t by ring]
    module
  · intro t ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply ht
    show prodTerm A B N s v t = 0
    unfold prodTerm
    rw [zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul]

/-- For a local pair of order `N`, `A_(n) B = 0` for every `n ≥ N`. -/
theorem prod_eq_zero_of_local (A B : OpField k V) (N : ℕ)
    (hloc : ∀ p q, dz k N (opComm A.mode B.mode) p q = 0) (n : ℕ) (hn : N ≤ n) (s : ℤ) :
    (prod n A B).mode s = 0 := by
  rw [prod_natCast_eq_dz]
  exact dz_mono k _ hloc hn 0 s

/-- **The commutator formula for a local pair of fields**:
`[A_p, B_q] = ∑_{j<N} (p choose j) (A_(j) B)_{p+q-j}`. -/
theorem commutator_of_local_prod (A B : OpField k V) (N : ℕ)
    (hloc : ∀ p q, dz k N (opComm A.mode B.mode) p q = 0) (p q : ℤ) :
    A.mode p * B.mode q - B.mode q * A.mode p =
      ∑ j ∈ Finset.range N, zbinom k p j • (prod j A B).mode (p + q - j) := by
  rw [commutator_of_local A.mode B.mode N hloc p q]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prod_natCast_eq_dz]

end OpField

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.OpField.prod
#print axioms HaagerupIzumi.C8.OpField.prodMode_eq_sum
#print axioms HaagerupIzumi.C8.OpField.prod_natCast_eq_dz
#print axioms HaagerupIzumi.C8.OpField.prod_eq_zero_of_local
#print axioms HaagerupIzumi.C8.OpField.commutator_of_local_prod
