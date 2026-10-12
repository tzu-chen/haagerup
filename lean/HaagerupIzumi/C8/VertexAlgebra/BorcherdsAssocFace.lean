module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsProduct

@[expose] public section

/-!
# `Good` from locality and associativity at a single `p`

W3, item (1), for the induction route to `IterClosed` (`Lattice/W3_PLAN.md`, section 2).  A fourth
reduction of the Borcherds identity, besides `bD_eq_zero_of_comm_iter`, `bD_eq_zero_of_weak` and
`bD_eq_zero_of_local_iter`:

* `eq_zero_of_pascal_shift_face`: a function on `ℤ³` with the Pascal recursion vanishes as soon
  as it vanishes on a locality face `r ≥ R` and on **one** plane `p = P₀`;
* `assoc_face`: for `P ≥ e + l` the defect at `p = P` is the weak-associativity defect
  `∑_t (P choose t) (x_(r+t) b)_(P+q-t) c - ∑_t (-1)^t (r choose t) x_(P+r-t) b_(q+t) c`
  (the `b x c` terms vanish);
* `good_of_local_assoc`: `Good x` from locality with every homogeneous `b` and **weak
  associativity at the single value `p = e + l`**;
* `AssocClosed`, `productClosedHom_of_assocClosed`: closure under `n`-th products from weak
  associativity of the products at `p = e + l` (Dong's lemma supplies locality);
* `AssocStep`, `good_mode_of_assocStep`, `productClosedHom_of_assocStep`: the **downward
  induction on `n`** (for `n ≥ i + m` the product `a_(n) w` vanishes): closure follows from the
  induction step `AssocStep`, weak associativity of `a_(n) w` at `p = e + l` given that all
  `a_(n+t) w`, `t ≥ 1`, are `Good`.  `AssocStep` is the open part of item (1) on this route.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-- **Reduction to a locality face and one plane `p = P₀`.** -/
theorem eq_zero_of_pascal_shift_face {W : Type*} [AddCommGroup W] (f : ℤ → ℤ → ℤ → W)
    (hpas : ∀ p q r, f (p + 1) q r = f p (q + 1) r + f p q (r + 1)) (R P₀ : ℤ)
    (hR : ∀ p q r, R ≤ r → f p q r = 0) (hP : ∀ q r, f P₀ q r = 0) :
    ∀ p q r, f p q r = 0 := by
  have h := eq_zero_of_pascal_iter_face (fun p q r => f (p + P₀) q r)
    (fun p q r => by
      show f (p + 1 + P₀) q r = f (p + P₀) (q + 1) r + f (p + P₀) q (r + 1)
      rw [show p + 1 + P₀ = p + P₀ + 1 by ring]
      exact hpas (p + P₀) q r)
    R (fun p q r hr => hR _ q r hr) (fun q r => by
      show f (0 + P₀) q r = 0
      rw [zero_add]
      exact hP q r)
  intro p q r
  have := h (p - P₀) q r
  rwa [sub_add_cancel] at this

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-- On the associativity face `P ≥ e + l` the `b x c` part of the right side vanishes. -/
theorem assoc_face {e j l : ℕ} {x b c : V} (hx : x ∈ M.grade e) (hc : c ∈ M.grade l) {P : ℤ} (hP : (e : ℤ) + l ≤ P) (q r : ℤ) :
    M.bD e j l x b c P q r =
      M.bL x b c P q r (bN e j l P q r) -
        ∑ t ∈ Finset.range (bN e j l P q r), ((-1 : k) ^ t * zbinom k r t) •
          M.mode (P + r - t) x (M.mode (q + t) b c) := by
  unfold bD bR
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [M.mode_trunc (P + (t : ℤ)) hx hc (by omega), map_zero, smul_zero, sub_zero]

/-- **`Good` from locality and weak associativity at `p = e + l`.** -/
theorem good_of_local_assoc {e : ℕ} {x : V} (hx : x ∈ M.grade e)
    (hloc : ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∃ R : ℕ, ∀ p q, dz k R (M.comm x b c) p q = 0)
    (hassoc : ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∀ q r, M.bD e j l x b c ((e : ℤ) + l) q r = 0) : M.Good x :=
  (M.good_iff_bD hx).2 fun {j l b c} hb hc p q r => by
    obtain ⟨R, hR⟩ := hloc hb hc
    refine eq_zero_of_pascal_shift_face (fun p q r => M.bD e j l x b c p q r)
      (M.bD_pascal hx hb hc) (((e + j + R : ℕ)) : ℤ) ((e : ℤ) + l) (fun p q r hr => ?_)
      (hassoc hb hc) p q r
    obtain ⟨S, hS⟩ : ∃ S : ℕ, r = (S : ℤ) := ⟨r.toNat, by omega⟩
    subst hS
    show M.bL x b c p q S _ - M.bR x b c p q S _ = 0
    rw [M.bL_eq_zero_of_le hx hb c p q S (by push_cast at hr; omega),
      M.bR_eq_dz x b c p q S (by unfold bN; simp only [Int.natAbs_natCast]; omega),
      dz_mono k (M.comm x b c) hR (by push_cast at hr; omega) p q, sub_zero]

/-- Weak associativity at `p = e + l` for products of homogeneous `Good` vectors. -/
def AssocClosed : Prop :=
  ∀ {i m e : ℕ} {a w : V}, a ∈ M.grade i → M.Good a → w ∈ M.grade m → M.Good w → ∀ n : ℤ,
    M.mode n a w ∈ M.grade e → ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∀ q r : ℤ, M.bD e j l (M.mode n a w) b c ((e : ℤ) + l) q r = 0

/-- **Closure under `n`-th products from weak associativity** (Dong's lemma supplies
locality). -/
theorem productClosedHom_of_assocClosed (h : M.AssocClosed) : M.ProductClosedHom := by
  intro i m a w ha hga hw hgw n
  obtain ⟨e, he⟩ := M.mode_mem_some_grade ha hw n
  exact M.good_of_local_assoc he
    (fun {j _ _ c} hb _ => ⟨dongOrder i m j n, fun p q => M.dong_of_good ha hga hw hgw hb n p q c⟩)
    (h ha hga hw hgw n he)

/-- **The induction step** of the downward induction on `n` (the open part of item (1), induction
route): for homogeneous `Good a`, `Good w` and `x = a_(n) w ∈ V_e`, if every `a_(n+t) w`
(`t ≥ 1`) is `Good`, then `x` satisfies weak associativity at `p = e + l`. -/
def AssocStep : Prop :=
  ∀ {i m e : ℕ} {a w : V}, a ∈ M.grade i → M.Good a → w ∈ M.grade m → M.Good w → ∀ n : ℤ,
    (∀ t : ℕ, 1 ≤ t → M.Good (M.mode (n + t) a w)) → M.mode n a w ∈ M.grade e →
      ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
        ∀ q r : ℤ, M.bD e j l (M.mode n a w) b c ((e : ℤ) + l) q r = 0

theorem assocStep_of_assocClosed (h : M.AssocClosed) : M.AssocStep :=
  fun ha hga hw hgw n _ he _ _ _ _ hb hc q r => h ha hga hw hgw n he hb hc q r

/-- **Downward induction on `n`**: from the induction step, every `a_(n) w` is `Good` (for
`n ≥ i + m` the product vanishes). -/
theorem good_mode_of_assocStep (h : M.AssocStep) {i m : ℕ} {a w : V} (ha : a ∈ M.grade i)
    (hga : M.Good a) (hw : w ∈ M.grade m) (hgw : M.Good w) : ∀ n : ℤ, M.Good (M.mode n a w) := by
  have hzero : ∀ n : ℤ, (i : ℤ) + m ≤ n → M.Good (M.mode n a w) := fun n hn => by
    rw [M.mode_trunc n ha hw hn]
    exact M.goodSub.zero_mem
  have step : ∀ n : ℤ, (∀ t : ℕ, 1 ≤ t → M.Good (M.mode (n + t) a w)) →
      M.Good (M.mode n a w) := fun n hih => by
    obtain ⟨e, he⟩ := M.mode_mem_some_grade ha hw n
    exact M.good_of_local_assoc he
      (fun {j _ _ c} hb _ =>
        ⟨dongOrder i m j n, fun p q => M.dong_of_good ha hga hw hgw hb n p q c⟩)
      (h ha hga hw hgw n hih he)
  have key : ∀ d : ℕ, ∀ d' : ℕ, d' ≤ d → M.Good (M.mode ((i : ℤ) + m - d') a w) := by
    intro d
    induction d with
    | zero =>
      intro d' hd'
      exact hzero _ (by omega)
    | succ d ih =>
      intro d' hd'
      rcases Nat.lt_or_ge d' (d + 1) with h' | h'
      · exact ih d' (by omega)
      · refine step _ fun t ht => ?_
        by_cases htd : t ≤ d'
        · have e1 : (i : ℤ) + m - d' + t = (i : ℤ) + m - ((d' - t : ℕ) : ℤ) := by
            rw [Nat.cast_sub htd]; ring
          rw [e1]
          exact ih (d' - t) (by omega)
        · exact hzero _ (by omega)
  intro n
  rcases le_or_gt ((i : ℤ) + m) n with hn | hn
  · exact hzero n hn
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = (i : ℤ) + m - d := ⟨((i : ℤ) + m - n).toNat, by omega⟩
    exact key d d le_rfl

/-- **Closure under `n`-th products from the induction step.** -/
theorem productClosedHom_of_assocStep (h : M.AssocStep) : M.ProductClosedHom :=
  fun ha hga hw hgw n => M.good_mode_of_assocStep h ha hga hw hgw n

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.eq_zero_of_pascal_shift_face
#print axioms HaagerupIzumi.C8.ModeAlgebra.assoc_face
#print axioms HaagerupIzumi.C8.ModeAlgebra.good_of_local_assoc
#print axioms HaagerupIzumi.C8.ModeAlgebra.productClosedHom_of_assocClosed
#print axioms HaagerupIzumi.C8.ModeAlgebra.good_mode_of_assocStep
#print axioms HaagerupIzumi.C8.ModeAlgebra.productClosedHom_of_assocStep
