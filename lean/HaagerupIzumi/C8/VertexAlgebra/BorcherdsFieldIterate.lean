module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsDong

@[expose] public section

/-!
# Groundwork for the field iterate identity: the decomposition theorem for local families

W3, item (1), route A (`Lattice/W3_PLAN.md`, section 2).  Abstract two-variable families
`F : ℤ → ℤ → W` (coefficients of `F(z₁, z₂) = ∑ F(p, q) z₁^{-p-1} z₂^{-q-1}`), no mode algebra.

* `dz_one`: `(z₁ - z₂) F` has coefficients `F(p+1, q) - F(p, q+1)`;
* `deltaFam j c (p, q) = (p choose j) c(p + q - j)`: the coefficients of
  `c(z₂) ∂_{z₂}^{(j)} δ(z₁ - z₂)`; `dz_deltaFam_le`, `dz_deltaFam_gt`:
  `(z₁ - z₂)^i ∂^{(j)} δ = ∂^{(j-i)} δ` for `i ≤ j` and `= 0` for `i > j`;
  `res_deltaFam`: `Res_{z₁} (z₁ - z₂)^i ∂^{(j)} δ(z₁ - z₂) c(z₂) = δ_{ij} c(z₂)`;
* `eq_zero_of_dz_res` (**uniqueness**): if `(z₁ - z₂)^N H = 0` and all residues
  `Res_{z₁} (z₁ - z₂)^i H` (`i < N`) vanish, then `H = 0`;
* **`eq_sum_of_dz_eq_zero`** (the **decomposition theorem**, Kac, *Vertex algebras for
  beginners*, 2nd ed., Theorem 2.3, numbering from memory): if `(z₁ - z₂)^N F = 0` then
  `F(p, q) = ∑_{j < N} (p choose j) c_j(p + q - j)` with `c_j(s) = dz j F (0, s)`, the residue
  `Res_{z₁} (z₁ - z₂)^j F(z₁, z₂)`.

For `F(p, q) = [A_p, B_q]` with `A, B` local of order `N` this is the commutator formula
`[A_p, B_q] = ∑_{j<N} (p choose j) (A_(j) B)_{p+q-j}` with the field products
`(A_(j) B)_s = dz j [A, B] (0, s)` (`j ≥ 0`); see `commutator_of_local`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

section Decomposition

variable (k : Type*) [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem dz_one (F : ℤ → ℤ → W) (p q : ℤ) : dz k 1 F p q = F (p + 1) q - F p (q + 1) := by
  rw [dz_succ, dz_zero, dz_zero]

theorem dz_sum_pi {ι : Type*} (S : Finset ι) (R : ℕ) (F : ι → ℤ → ℤ → W) (p q : ℤ) :
    dz k R (∑ j ∈ S, F j) p q = ∑ j ∈ S, dz k R (F j) p q := by
  unfold dz
  simp only [Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem dz_sub_pi (R : ℕ) (F G : ℤ → ℤ → W) (p q : ℤ) :
    dz k R (F - G) p q = dz k R F p q - dz k R G p q :=
  dz_sub_fun k R F G p q

/-- The coefficients of `c(z₂) ∂_{z₂}^{(j)} δ(z₁ - z₂)`: `(p choose j) c(p + q - j)`. -/
def deltaFam (j : ℕ) (c : ℤ → W) : ℤ → ℤ → W := fun p q => zbinom k p j • c (p + q - j)

theorem dz_one_deltaFam_succ (j : ℕ) (c : ℤ → W) (p q : ℤ) :
    dz k 1 (deltaFam k (j + 1) c) p q = deltaFam k j c p q := by
  rw [dz_one]
  unfold deltaFam
  rw [zbinom_succ_succ, add_smul,
    show p + 1 + q - ((j + 1 : ℕ) : ℤ) = p + q - (j : ℤ) by push_cast; ring,
    show p + (q + 1) - ((j + 1 : ℕ) : ℤ) = p + q - (j : ℤ) by push_cast; ring]
  abel

theorem dz_one_deltaFam_zero (c : ℤ → W) (p q : ℤ) : dz k 1 (deltaFam k 0 c) p q = 0 := by
  rw [dz_one]
  unfold deltaFam
  rw [zbinom_zero_right, zbinom_zero_right, show p + 1 + q - ((0 : ℕ) : ℤ) = p + (q + 1) - 0 by
    push_cast; ring]
  simp

/-- `(z₁ - z₂)^i ∂^{(j)} δ = ∂^{(j-i)} δ` for `i ≤ j`. -/
theorem dz_deltaFam_le (c : ℤ → W) (i : ℕ) :
    ∀ j, i ≤ j → ∀ p q, dz k i (deltaFam k j c) p q = deltaFam k (j - i) c p q := by
  induction i with
  | zero => intro j _ p q; rw [dz_zero, Nat.sub_zero]
  | succ i ih =>
    intro j hj p q
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h1 : dz k 1 (deltaFam k (j' + 1) c) = deltaFam k j' c :=
      funext fun p => funext fun q => dz_one_deltaFam_succ k j' c p q
    rw [show i + 1 = 1 + i by ring, dz_add, h1, ih j' (by omega),
      show j' + 1 - (1 + i) = j' - i by omega]

/-- `(z₁ - z₂)^i ∂^{(j)} δ = 0` for `i > j`. -/
theorem dz_deltaFam_gt (c : ℤ → W) (i j : ℕ) (h : j < i) (p q : ℤ) :
    dz k i (deltaFam k j c) p q = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, i = j + 1 + e := ⟨i - j - 1, by omega⟩
  have h1 : dz k j (deltaFam k j c) = deltaFam k 0 c :=
    funext fun p => funext fun q => by rw [dz_deltaFam_le k c j j le_rfl, Nat.sub_self]
  have h3 : dz k (j + 1) (deltaFam k j c) = fun _ _ => (0 : W) :=
    funext fun p => funext fun q => by
      rw [dz_add k j 1, h1, dz_one_deltaFam_zero]
  rw [dz_add k (j + 1) e, h3, dz_zero_fun]

/-- `Res_{z₁} (z₁ - z₂)^i ∂^{(j)} δ(z₁ - z₂) c(z₂) = δ_{ij} c(z₂)`. -/
theorem res_deltaFam (c : ℤ → W) (i j : ℕ) (s : ℤ) :
    dz k i (deltaFam k j c) 0 s = if i = j then c s else 0 := by
  rcases lt_or_ge j i with h | h
  · rw [dz_deltaFam_gt k c i j h, if_neg (by omega)]
  · rw [dz_deltaFam_le k c i j h]
    unfold deltaFam
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      rw [Nat.sub_self, zbinom_zero_right, one_smul, if_pos rfl, Nat.cast_zero, zero_add,
        sub_zero]
    · rw [if_neg (by omega), zbinom_zero_left_of_pos k (by omega), zero_smul]

/-- **Uniqueness**: `(z₁ - z₂)^N H = 0` and vanishing residues force `H = 0`. -/
theorem eq_zero_of_dz_res (N : ℕ) (H : ℤ → ℤ → W) (hN : ∀ p q, dz k N H p q = 0)
    (hres : ∀ i < N, ∀ s, dz k i H 0 s = 0) : ∀ p q, H p q = 0 := by
  -- if `(z₁ - z₂) G = 0` then `G(p, q) = G(0, p + q)`
  have shift : ∀ G : ℤ → ℤ → W, (∀ p q, G (p + 1) q = G p (q + 1)) →
      ∀ p q, G p q = G 0 (p + q) := by
    intro G hG p
    induction p using Int.induction_on with
    | zero => intro q; rw [zero_add]
    | succ p ih => intro q; rw [hG, ih, show p + (q + 1) = (p : ℤ) + 1 + q by ring]
    | pred p ih =>
      intro q
      have := hG (-(p : ℤ) - 1) (q - 1)
      rw [show -(p : ℤ) - 1 + 1 = -(p : ℤ) by ring, show q - 1 + 1 = q by ring] at this
      rw [← this, ih, show -(p : ℤ) + (q - 1) = -(p : ℤ) - 1 + q by ring]
  have key : ∀ d : ℕ, d ≤ N → ∀ p q, dz k (N - d) H p q = 0 := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.sub_zero]; exact hN
    | succ d ih =>
      intro hd p q
      have hG : ∀ p q, dz k (N - (d + 1)) H (p + 1) q = dz k (N - (d + 1)) H p (q + 1) := by
        intro p q
        have h := ih (by omega) p q
        rw [show N - d = N - (d + 1) + 1 by omega, dz_succ] at h
        exact sub_eq_zero.1 h
      rw [shift _ hG p q]
      exact hres _ (by omega) _
  intro p q
  have := key N le_rfl p q
  rwa [Nat.sub_self, dz_zero] at this

/-- **The decomposition theorem**: if `(z₁ - z₂)^N F = 0` then
`F(p, q) = ∑_{j<N} (p choose j) c_j(p + q - j)` with `c_j(s) = dz j F (0, s)`. -/
theorem eq_sum_of_dz_eq_zero (N : ℕ) (F : ℤ → ℤ → W) (h : ∀ p q, dz k N F p q = 0)
    (p q : ℤ) :
    F p q = ∑ j ∈ Finset.range N, zbinom k p j • dz k j F 0 (p + q - j) := by
  have hH : ∀ p q,
      (F - ∑ j ∈ Finset.range N, deltaFam k j (fun s => dz k j F 0 s)) p q = 0 := by
    refine eq_zero_of_dz_res k N _ (fun p q => ?_) (fun i hi s => ?_)
    · rw [dz_sub_pi, dz_sum_pi, h, Finset.sum_eq_zero fun j hj =>
        dz_deltaFam_gt k _ N j (Finset.mem_range.1 hj) p q, sub_zero]
    · rw [dz_sub_pi, dz_sum_pi]
      simp only [res_deltaFam]
      rw [Finset.sum_ite_eq (Finset.range N) i, if_pos (Finset.mem_range.2 hi), sub_self]
  have := hH p q
  simp only [Pi.sub_apply, Finset.sum_apply, sub_eq_zero] at this
  rw [this]
  rfl

end Decomposition

/-! ## The commutator formula for local operator families -/

section Commutator

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **The commutator formula for a local pair**: if `A, B` are local of order `N`, then
`[A_p, B_q] = ∑_{j<N} (p choose j) (A_(j) B)_{p+q-j}` with `(A_(j) B)_s = dz j [A, B] (0, s)`. -/
theorem commutator_of_local (A B : ℤ → Module.End k V) (N : ℕ)
    (hloc : ∀ p q, dz k N (opComm A B) p q = 0) (p q : ℤ) :
    A p * B q - B q * A p =
      ∑ j ∈ Finset.range N, zbinom k p j • dz k j (opComm A B) 0 (p + q - j) :=
  eq_sum_of_dz_eq_zero k N (opComm A B) hloc p q

end Commutator

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.res_deltaFam
#print axioms HaagerupIzumi.C8.eq_zero_of_dz_res
#print axioms HaagerupIzumi.C8.eq_sum_of_dz_eq_zero
#print axioms HaagerupIzumi.C8.commutator_of_local
