module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsDongNeg

@[expose] public section

/-!
# Dong's lemma for `Good` vectors, all `n`

W3, item (1), step (iii) of `Lattice/W3_PLAN.md`.  For a `ModeAlgebra`, homogeneous `Good`
vectors `a ∈ V_i`, `w ∈ V_m`, any homogeneous `b ∈ V_j` and any `n ∈ ℤ`:

* `comm_mode_eq_dong`: on homogeneous `c`, `[(a_(n) w)_(s), b_(q)] c = ePlus n Φ⁺ - eMinus n Φ⁻`
  with `Φ⁺(u, v, q) = a_(u) w_(v) b_(q) c - b_(q) a_(u) w_(v) c` and
  `Φ⁻(u, v, q) = w_(v) a_(u) b_(q) c - b_(q) w_(v) a_(u) c` (the iterate formula of `a`,
  `iterate_of_good`, applied to `c` and to `b_(q) c`);
* `dong_h12`, `dong_h3p`, `dong_h3m`: the hypotheses of `dong_general`, from the localities of
  `(a, w)`, `(a, b)`, `(w, b)` (`locality_of_good`);
* **`dong_of_good`** (Dong's lemma): `a_(n) w` is local with `b` of order
  `dongOrder i m j n = (2 (i + m + j) - n)⁺ + (i + m + j)`, on all of `V`;
* **`good_mode_of_iter`**: `Good (a_(n) w)` follows from the **iterate family** of the
  Borcherds identity for `(a_(n) w, b, c)` alone (via `good_of_local_iter`).  This is the one
  remaining input of closure under `n`-th products (item (1)); see `Lattice/W3_PLAN.md`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-- `Φ⁺(u, v, q) = a_(u) w_(v) b_(q) c - b_(q) a_(u) w_(v) c`. -/
def dongP (a w b c : V) : ℤ → ℤ → ℤ → V := fun u v q =>
  M.mode u a (M.mode v w (M.mode q b c)) - M.mode q b (M.mode u a (M.mode v w c))

/-- `Φ⁻(u, v, q) = w_(v) a_(u) b_(q) c - b_(q) w_(v) a_(u) c`. -/
def dongM (a w b c : V) : ℤ → ℤ → ℤ → V := fun u v q =>
  M.mode v w (M.mode u a (M.mode q b c)) - M.mode q b (M.mode v w (M.mode u a c))

theorem dongP_mem {m j l : ℕ} {w b c : V} (a : V) (hw : w ∈ M.grade m) (hb : b ∈ M.grade j)
    (hc : c ∈ M.grade l) : M.dongP a w b c ∈ T2 k V := by
  refine mem_T2.2 fun q => ?_
  obtain ⟨e, he⟩ := M.mode_mem_some_grade hb hc q
  refine ⟨(m : ℤ) + e + l, fun u v hv => ?_⟩
  show M.mode u a (M.mode v w (M.mode q b c)) - M.mode q b (M.mode u a (M.mode v w c)) = 0
  rw [M.mode_trunc v hw he (by omega), M.mode_trunc v hw hc (by omega)]
  simp

theorem dongM_mem {i j l : ℕ} {a b c : V} (w : V) (ha : a ∈ M.grade i) (hb : b ∈ M.grade j)
    (hc : c ∈ M.grade l) : M.dongM a w b c ∈ T1 k V := by
  refine mem_T1.2 fun q => ?_
  obtain ⟨e, he⟩ := M.mode_mem_some_grade hb hc q
  refine ⟨(i : ℤ) + e + l, fun u v hu => ?_⟩
  show M.mode v w (M.mode u a (M.mode q b c)) - M.mode q b (M.mode v w (M.mode u a c)) = 0
  rw [M.mode_trunc u ha he (by omega), M.mode_trunc u ha hc (by omega)]
  simp

theorem dong_h12 {i m : ℕ} {a w : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (b c : V) {r : ℕ} (hr : i + m ≤ r) :
    ((d12 k V) ^ r) (M.dongP a w b c - M.dongM a w b c) = 0 := by
  funext u v q
  rw [d12_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
  have e : (fun p' q' => (M.dongP a w b c - M.dongM a w b c) p' q' q) =
      fun p' q' => M.comm a w (M.mode q b c) p' q' - M.mode q b (M.comm a w c p' q') := by
    funext p' q'
    simp only [Pi.sub_apply, dongP, dongM, comm, map_sub]
    abel
  rw [e, dz_sub_fun, ← dz_map k (M.mode q b) r (M.comm a w c) u v,
    M.locality_of_good ha hga hw hr u v (M.mode q b c), M.locality_of_good ha hga hw hr u v c,
    map_zero, sub_zero]

theorem dong_h3p {i m j : ℕ} {a w b : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (hgw : M.Good w) (hb : b ∈ M.grade j) (c : V) {r : ℕ}
    (hr1 : i + j ≤ r) (hr2 : m + j ≤ r) :
    ((d13 k V) ^ r) (((d23 k V) ^ r) (M.dongP a w b c)) = 0 := by
  let Θ1 : ℤ → ℤ → ℤ → V := fun u v q => M.mode u a (M.comm w b c v q)
  let Θ2 : ℤ → ℤ → ℤ → V := fun u v q => M.comm a b (M.mode v w c) u q
  have hsplit : M.dongP a w b c = Θ1 + Θ2 := by
    funext u v q
    simp only [Θ1, Θ2, dongP, comm, Pi.add_apply, map_sub]
    abel
  have h1 : ((d23 k V) ^ r) Θ1 = 0 := by
    funext u v q
    rw [d23_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p' q' => M.mode u a (M.comm w b c p' q')) v q = 0
    rw [← dz_map k (M.mode u a) r (M.comm w b c) v q, M.locality_of_good hw hgw hb hr2 v q c,
      map_zero]
  have h2 : ((d13 k V) ^ r) Θ2 = 0 := by
    funext u v q
    rw [d13_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    exact M.locality_of_good ha hga hb hr1 u q (M.mode v w c)
  rw [hsplit, map_add, map_add, h1, map_zero, zero_add,
    comm_apply ((commute_d13_d23 (k := k) (W := V)).pow_pow r r), h2, map_zero]

theorem dong_h3m {i m j : ℕ} {a w b : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (hgw : M.Good w) (hb : b ∈ M.grade j) (c : V) {r : ℕ}
    (hr1 : i + j ≤ r) (hr2 : m + j ≤ r) :
    ((d13 k V) ^ r) (((d23 k V) ^ r) (M.dongM a w b c)) = 0 := by
  let Θ3 : ℤ → ℤ → ℤ → V := fun u v q => M.mode v w (M.comm a b c u q)
  let Θ4 : ℤ → ℤ → ℤ → V := fun u v q => M.comm w b (M.mode u a c) v q
  have hsplit : M.dongM a w b c = Θ3 + Θ4 := by
    funext u v q
    simp only [Θ3, Θ4, dongM, comm, Pi.add_apply, map_sub]
    abel
  have h3 : ((d13 k V) ^ r) Θ3 = 0 := by
    funext u v q
    rw [d13_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p' q' => M.mode v w (M.comm a b c p' q')) u q = 0
    rw [← dz_map k (M.mode v w) r (M.comm a b c) u q, M.locality_of_good ha hga hb hr1 u q c,
      map_zero]
  have h4 : ((d23 k V) ^ r) Θ4 = 0 := by
    funext u v q
    rw [d23_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    exact M.locality_of_good hw hgw hb hr2 v q (M.mode u a c)
  rw [hsplit, map_add, map_add, h4, map_zero, add_zero,
    comm_apply ((commute_d13_d23 (k := k) (W := V)).pow_pow r r), h3, map_zero]

/-- On homogeneous `c`: `[(a_(n) w)_(s), b_(q)] c = ePlus n Φ⁺ (s, q) - eMinus n Φ⁻ (s, q)`. -/
theorem comm_mode_eq_dong {i m j l : ℕ} {a w b c : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (hb : b ∈ M.grade j) (hc : c ∈ M.grade l) (n s q : ℤ) :
    M.comm (M.mode n a w) b c s q =
      ePlus k n (M.dongP a w b c) s q - eMinus k n (M.dongM a w b c) s q := by
  obtain ⟨e, he⟩ := M.mode_mem_some_grade hb hc q
  obtain ⟨N₁, h₁⟩ := ePlus_eq_sum (M.dongP_mem a hw hb hc) n s q
  obtain ⟨N₂, h₂⟩ := eMinus_eq_sum (M.dongM_mem w ha hb hc) n s q
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ : ∃ N : ℕ, N₁ ≤ N ∧ N₂ ≤ N ∧ i + m + e + s.natAbs ≤ N ∧
      i + m + l + s.natAbs ≤ N :=
    ⟨N₁ + N₂ + (i + m + e + s.natAbs) + (i + m + l + s.natAbs), by omega, by omega, by omega,
      by omega⟩
  unfold comm
  rw [M.iterate_of_good ha hga hw he s n hN3, M.iterate_of_good ha hga hw hc s n hN4,
    h₁ N hN1, h₂ N hN2, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [dongP, dongM, map_smul, map_sub]
  rw [show n + s - (t : ℤ) = s + n - t by ring]
  module

/-- The locality order in Dong's lemma. -/
def dongOrder (i m j : ℕ) (n : ℤ) : ℕ := (2 * ((i + m + j : ℕ) : ℤ) - n).toNat + (i + m + j)

/-- **Dong's lemma for `Good` vectors**: for homogeneous `Good a ∈ V_i`, `Good w ∈ V_m`, any
homogeneous `b ∈ V_j` and any `n`, `a_(n) w` is local with `b` of order `dongOrder i m j n`. -/
theorem dong_of_good {i m j : ℕ} {a w b : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (hgw : M.Good w) (hb : b ∈ M.grade j) (n p q : ℤ) (c : V) :
    dz k (dongOrder i m j n) (M.comm (M.mode n a w) b c) p q = 0 := by
  have hhom : ∀ l (c : V), c ∈ M.grade l → ∀ p q,
      dz k (dongOrder i m j n) (M.comm (M.mode n a w) b c) p q = 0 := by
    intro l c hc p q
    have e : M.comm (M.mode n a w) b c =
        fun s q => ePlus k n (M.dongP a w b c) s q - eMinus k n (M.dongM a w b c) s q :=
      funext fun s => funext fun q => M.comm_mode_eq_dong ha hga hw hb hc n s q
    rw [e]
    exact dong_general (i + m + j) (2 * ((i + m + j : ℕ) : ℤ) - n).toNat n (by omega) _ _
      (M.dongP_mem a hw hb hc) (M.dongM_mem w ha hb hc) (M.dong_h12 ha hga hw b c (by omega))
      (M.dong_h3p ha hga hw hgw hb c (by omega) (by omega))
      (M.dong_h3m ha hga hw hgw hb c (by omega) (by omega)) p q
  have key : dz k (dongOrder i m j n)
      (opComm (fun u => M.mode u (M.mode n a w)) (fun v => M.mode v b)) p q = 0 :=
    M.ext_grade fun l c hc => by
      rw [dz_linearMap_apply, LinearMap.zero_apply]
      exact hhom l c hc p q
  have h := LinearMap.congr_fun key c
  rw [dz_linearMap_apply, LinearMap.zero_apply] at h
  exact h

/-- **Closure modulo the iterate family**: for homogeneous `Good a`, `Good w`, the product
`a_(n) w ∈ V_e` is `Good` as soon as the iterate family of the Borcherds identity holds for
`(a_(n) w, b, c)` (all homogeneous `b, c`). -/
theorem good_mode_of_iter {i m : ℕ} {a w : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (hgw : M.Good w) (n : ℤ) {e : ℕ} (hx : M.mode n a w ∈ M.grade e)
    (hiter : ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∀ q r, M.bD e j l (M.mode n a w) b c 0 q r = 0) :
    M.Good (M.mode n a w) :=
  M.good_of_local_iter hx
    (fun {j _ _ c} hb _ => ⟨dongOrder i m j n, fun p q => M.dong_of_good ha hga hw hgw hb n p q c⟩)
    hiter

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ModeAlgebra.comm_mode_eq_dong
#print axioms HaagerupIzumi.C8.ModeAlgebra.dong_of_good
#print axioms HaagerupIzumi.C8.ModeAlgebra.good_mode_of_iter
