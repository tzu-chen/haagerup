module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsIterate
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Dong's lemma for non-negative products

W3, item (1), step (iii) of `Lattice/W3_PLAN.md`, for `n ≥ 0`.  Three-variable families
`Φ : ℤ → ℤ → ℤ → W` (coefficients of `Φ(z₁, z₂, z₃)`) carry the commuting operators

* `d12 Φ (u, v, w) = Φ(u+1, v, w) - Φ(u, v+1, w)` (multiplication by `z₁ - z₂`),
* `d13 Φ (u, v, w) = Φ(u+1, v, w) - Φ(u, v, w+1)` (by `z₁ - z₃`),
* `d23 Φ (u, v, w) = Φ(u, v+1, w) - Φ(u, v, w+1)` (by `z₂ - z₃`),

with `d23 = d13 - d12` and `dᵢⱼ^R` given by the two-variable locality operator `dz`
(`d12_pow_apply`, `d13_pow_apply`, `d23_pow_apply`).

* `d23_pow_eq_zero` (**Dong's lemma, abstract form**): if `d12^r Φ = 0` and `Φ = Φ₁ + Φ₂` with
  `d23^r Φ₁ = 0`, `d13^r Φ₂ = 0`, then `d23^{3r} Φ = 0`.  Proof: `d23^{3r} = d23^{2r} d23^r` and
  `d23^{2r} = ∑_s (2r choose s) d13^s (-d12)^{2r-s}`; the terms with `s ≤ r` die by `d12^r Φ = 0`,
  those with `s ≥ r` by `d13^s d23^r Φ = d23^r d13^s Φ₂ = 0`.  (This is the argument of Kac,
  *Vertex algebras for beginners*, 2nd ed., proof of Dong's lemma, Lemma 3.2; numbering checked
  only against citations in the literature.)
* `dong_natCast` (operator families): if `A, B, C : ℤ → End V` are pairwise local of order `r`,
  then the field `X_s = dz n [A, B] (0, s)` (the `n`-th product `A_(n) B` for `n ≥ 0`) is local
  with `C` of order `3r`.  Here `Φ = [[A, B], C] = (A [B, C] - [B, C] A) + ([A, C] B - B [A, C])`.
* `ModeAlgebra.mode_mode_natCast_eq_dz`: for `Good a`, `(a_(n) w)_(s) = dz n [a, w] (0, s)` for
  `n ≥ 0` (the iterate formula, `iterate_of_good`);
* **`ModeAlgebra.dong_of_good_natCast`**: for homogeneous `Good a ∈ V_i`, `Good w ∈ V_m` and any
  homogeneous `b ∈ V_j`, `a_(n) w` is local of order `3 (i + m + j)` with `b`, for `n ≥ 0`.

The case `n < 0` (needed for normally ordered products, where the `n`-th product is a locally
finite infinite sum) is proved in `VertexAlgebra/BorcherdsDongNeg.lean` (`dong_general`) and
`VertexAlgebra/BorcherdsDongModes.lean` (`ModeAlgebra.dong_of_good`, all `n ∈ ℤ`).

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

section ThreeVar

variable (k : Type*) [Field k] (W : Type*) [AddCommGroup W] [Module k W]

/-- Multiplication by `z₁ - z₂` on three-variable families. -/
def d12 : Module.End k (ℤ → ℤ → ℤ → W) where
  toFun Φ := fun u v w => Φ (u + 1) v w - Φ u (v + 1) w
  map_add' Φ Ψ := by funext u v w; simp only [Pi.add_apply]; abel
  map_smul' μ Φ := by funext u v w; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

/-- Multiplication by `z₁ - z₃`. -/
def d13 : Module.End k (ℤ → ℤ → ℤ → W) where
  toFun Φ := fun u v w => Φ (u + 1) v w - Φ u v (w + 1)
  map_add' Φ Ψ := by funext u v w; simp only [Pi.add_apply]; abel
  map_smul' μ Φ := by funext u v w; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

/-- Multiplication by `z₂ - z₃`. -/
def d23 : Module.End k (ℤ → ℤ → ℤ → W) where
  toFun Φ := fun u v w => Φ u (v + 1) w - Φ u v (w + 1)
  map_add' Φ Ψ := by funext u v w; simp only [Pi.add_apply]; abel
  map_smul' μ Φ := by funext u v w; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

variable {k W}

theorem d12_apply (Φ : ℤ → ℤ → ℤ → W) (u v w : ℤ) :
    d12 k W Φ u v w = Φ (u + 1) v w - Φ u (v + 1) w := rfl

theorem d13_apply (Φ : ℤ → ℤ → ℤ → W) (u v w : ℤ) :
    d13 k W Φ u v w = Φ (u + 1) v w - Φ u v (w + 1) := rfl

theorem d23_apply (Φ : ℤ → ℤ → ℤ → W) (u v w : ℤ) :
    d23 k W Φ u v w = Φ u (v + 1) w - Φ u v (w + 1) := rfl

/-- `z₂ - z₃ = (z₁ - z₃) - (z₁ - z₂)`. -/
theorem d23_eq : d23 k W = d13 k W + -d12 k W := by
  refine LinearMap.ext fun Φ => funext fun u => funext fun v => funext fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.neg_apply, Pi.add_apply, Pi.neg_apply, d12_apply,
    d13_apply, d23_apply]
  abel

theorem commute_d13_d12 : Commute (d13 k W) (d12 k W) := by
  show d13 k W * d12 k W = d12 k W * d13 k W
  refine LinearMap.ext fun Φ => funext fun u => funext fun v => funext fun w => ?_
  simp only [Module.End.mul_apply, d12_apply, d13_apply]
  abel

theorem commute_d23_d12 : Commute (d23 k W) (d12 k W) := by
  rw [d23_eq]
  exact (commute_d13_d12 (k := k) (W := W)).add_left (Commute.refl (d12 k W)).neg_left

theorem commute_d13_d23 : Commute (d13 k W) (d23 k W) := by
  rw [d23_eq]
  exact (Commute.refl (d13 k W)).add_right (commute_d13_d12 (k := k) (W := W)).neg_right

theorem d12_pow_apply (R : ℕ) (Φ : ℤ → ℤ → ℤ → W) :
    ∀ u v w, ((d12 k W) ^ R) Φ u v w = dz k R (fun p q => Φ p q w) u v := by
  induction R with
  | zero => intro u v w; rw [pow_zero, Module.End.one_apply, dz_zero]
  | succ R ih => intro u v w; rw [pow_succ', Module.End.mul_apply, d12_apply, ih, ih, dz_succ]

theorem d13_pow_apply (R : ℕ) (Φ : ℤ → ℤ → ℤ → W) :
    ∀ u v w, ((d13 k W) ^ R) Φ u v w = dz k R (fun p q => Φ p v q) u w := by
  induction R with
  | zero => intro u v w; rw [pow_zero, Module.End.one_apply, dz_zero]
  | succ R ih => intro u v w; rw [pow_succ', Module.End.mul_apply, d13_apply, ih, ih, dz_succ]

theorem d23_pow_apply (R : ℕ) (Φ : ℤ → ℤ → ℤ → W) :
    ∀ u v w, ((d23 k W) ^ R) Φ u v w = dz k R (fun p q => Φ u p q) v w := by
  induction R with
  | zero => intro u v w; rw [pow_zero, Module.End.one_apply, dz_zero]
  | succ R ih => intro u v w; rw [pow_succ', Module.End.mul_apply, d23_apply, ih, ih, dz_succ]

theorem pow_apply_eq_zero_of_le {M' : Type*} [AddCommGroup M'] [Module k M']
    {f : Module.End k M'} {x : M'} {r R : ℕ} (h : (f ^ r) x = 0) (hR : r ≤ R) :
    (f ^ R) x = 0 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hR
  rw [add_comm, pow_add, Module.End.mul_apply, h, map_zero]

theorem neg_pow_apply {M' : Type*} [AddCommGroup M'] [Module k M'] (f : Module.End k M')
    (n : ℕ) (x : M') : ((-f) ^ n) x = ((-1 : k) ^ n) • (f ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (-f) n, Module.End.mul_apply, ih, LinearMap.neg_apply, map_smul,
      pow_succ' f n, Module.End.mul_apply, pow_succ (-1 : k) n, mul_smul, neg_one_smul, smul_neg]

/-- **Dong's lemma, abstract form.** -/
theorem d23_pow_eq_zero (r : ℕ) (Φ Φ₁ Φ₂ : ℤ → ℤ → ℤ → W)
    (h12 : ((d12 k W) ^ r) Φ = 0) (hΦ : Φ = Φ₁ + Φ₂)
    (h1 : ((d23 k W) ^ r) Φ₁ = 0) (h2 : ((d13 k W) ^ r) Φ₂ = 0) :
    ((d23 k W) ^ (2 * r + r)) Φ = 0 := by
  have hΨ : ((d23 k W) ^ r) Φ = ((d23 k W) ^ r) Φ₂ := by rw [hΦ, map_add, h1, zero_add]
  have hexp : (d23 k W) ^ (2 * r) = ∑ s ∈ Finset.range (2 * r + 1),
      (d13 k W) ^ s * (-d12 k W) ^ (2 * r - s) * ((2 * r).choose s : Module.End k _) := by
    rw [d23_eq]
    exact ((commute_d13_d12 (k := k) (W := W)).neg_right).add_pow _
  rw [pow_add, Module.End.mul_apply, hexp, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul]
  by_cases hs : s ≤ r
  · -- `(-d12)^(2r-s)` kills `Φ`
    have hc : Commute ((-d12 k W) ^ (2 * r - s)) ((d23 k W) ^ r) :=
      ((commute_d23_d12 (k := k) (W := W)).neg_right.symm).pow_pow _ _
    rw [← Module.End.mul_apply ((-d12 k W) ^ (2 * r - s)), hc.eq, Module.End.mul_apply,
      neg_pow_apply, pow_apply_eq_zero_of_le h12 (by omega), smul_zero, map_zero, map_zero,
      smul_zero]
  · -- `d13^s d23^r` kills `Φ₂`
    have hc1 : Commute ((d13 k W) ^ s) ((-d12 k W) ^ (2 * r - s)) :=
      ((commute_d13_d12 (k := k) (W := W)).neg_right).pow_pow _ _
    have hc2 : Commute ((d13 k W) ^ s) ((d23 k W) ^ r) :=
      (commute_d13_d23 (k := k) (W := W)).pow_pow _ _
    rw [hΨ, ← Module.End.mul_apply ((d13 k W) ^ s), hc1.eq, Module.End.mul_apply,
      ← Module.End.mul_apply ((d13 k W) ^ s), hc2.eq, Module.End.mul_apply,
      pow_apply_eq_zero_of_le h2 (by omega), map_zero, map_zero, smul_zero]

end ThreeVar

/-! ## Dong's lemma for operator families -/

section Fields

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The commutator family `[A_u, B_v]` of two operator families. -/
def opComm (A B : ℤ → Module.End k V) : ℤ → ℤ → Module.End k V :=
  fun u v => A u * B v - B v * A u

theorem dz_mul_right (R : ℕ) (F : ℤ → ℤ → Module.End k V) (Y : Module.End k V) (p q : ℤ) :
    dz k R (fun u v => F u v * Y) p q = dz k R F p q * Y := by
  simp only [dz, Finset.sum_mul, smul_mul_assoc]

theorem dz_mul_left (R : ℕ) (F : ℤ → ℤ → Module.End k V) (Y : Module.End k V) (p q : ℤ) :
    dz k R (fun u v => Y * F u v) p q = Y * dz k R F p q := by
  simp only [dz, Finset.mul_sum, mul_smul_comm]

/-- **Dong's lemma for `n ≥ 0`**: if `A, B, C` are pairwise local of order `r`, the `n`-th
product `X_s = dz n [A, B] (0, s)` is local with `C` of order `3r`. -/
theorem dong_natCast (A B C : ℤ → Module.End k V) (r : ℕ)
    (hAB : ∀ p q, dz k r (opComm A B) p q = 0) (hAC : ∀ p q, dz k r (opComm A C) p q = 0)
    (hBC : ∀ p q, dz k r (opComm B C) p q = 0) (n : ℕ) :
    ∀ p q, dz k (2 * r + r) (opComm (fun s => dz k n (opComm A B) 0 s) C) p q = 0 := by
  let Φ : ℤ → ℤ → ℤ → Module.End k V :=
    fun u v w => opComm A B u v * C w - C w * opComm A B u v
  let Φ₁ : ℤ → ℤ → ℤ → Module.End k V :=
    fun u v w => A u * opComm B C v w - opComm B C v w * A u
  let Φ₂ : ℤ → ℤ → ℤ → Module.End k V :=
    fun u v w => opComm A C u w * B v - B v * opComm A C u w
  have hΦ : Φ = Φ₁ + Φ₂ := by
    funext u v w
    simp only [Φ, Φ₁, Φ₂, opComm, Pi.add_apply, mul_sub, sub_mul, mul_assoc]
    abel
  have h12 : ((d12 k _) ^ r) Φ = 0 := by
    funext u v w
    rw [d12_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p q => opComm A B p q * C w - C w * opComm A B p q) u v = 0
    rw [dz_sub_fun, dz_mul_right, dz_mul_left, hAB, zero_mul, mul_zero, sub_zero]
  have h1 : ((d23 k _) ^ r) Φ₁ = 0 := by
    funext u v w
    rw [d23_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p q => A u * opComm B C p q - opComm B C p q * A u) v w = 0
    rw [dz_sub_fun, dz_mul_right, dz_mul_left, hBC, zero_mul, mul_zero, sub_zero]
  have h2 : ((d13 k _) ^ r) Φ₂ = 0 := by
    funext u v w
    rw [d13_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p q => opComm A C p q * B v - B v * opComm A C p q) u w = 0
    rw [dz_sub_fun, dz_mul_right, dz_mul_left, hAC, zero_mul, mul_zero, sub_zero]
  have hD := d23_pow_eq_zero r Φ Φ₁ Φ₂ h12 hΦ h1 h2
  have hX : opComm (fun s => dz k n (opComm A B) 0 s) C =
      fun s w => ((d12 k _ ^ n) Φ) 0 s w := by
    funext s w
    rw [d12_pow_apply]
    show dz k n (opComm A B) 0 s * C w - C w * dz k n (opComm A B) 0 s =
      dz k n (fun p q => opComm A B p q * C w - C w * opComm A B p q) 0 s
    rw [dz_sub_fun, dz_mul_right, dz_mul_left]
  intro p q
  rw [hX, ← d23_pow_apply, ← Module.End.mul_apply,
    ((commute_d23_d12 (k := k) (W := Module.End k V)).pow_pow _ _).eq,
    Module.End.mul_apply, hD, map_zero]
  rfl

end Fields

/-! ## Dong's lemma for `Good` vectors, `n ≥ 0` -/

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-- Locality of a `Good` vector in operator form. -/
theorem opLocal_of_good {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) {R : ℕ} (hR : i + j ≤ R) (p q : ℤ) :
    dz k R (opComm (fun u => M.mode u a) (fun v => M.mode v b)) p q = 0 := by
  refine LinearMap.ext fun c => ?_
  rw [dz_linearMap_apply, LinearMap.zero_apply]
  exact M.locality_of_good ha hgood hb hR p q c

/-- For `Good a` and `n ≥ 0`: `(a_(n) w)_(s) = dz n [a(·), w(·)] (0, s)`. -/
theorem mode_mode_natCast_eq_dz {i m : ℕ} {a w : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hw : w ∈ M.grade m) (n : ℕ) (s : ℤ) :
    M.mode s (M.mode n a w) = dz k n (opComm (fun u => M.mode u a) (fun v => M.mode v w)) 0 s :=
  M.ext_grade fun l c hc => by
    rw [dz_linearMap_apply, M.iterate_of_good ha hgood hw hc s n
      (N := max (i + m + l + s.natAbs) (n + 1)) (le_max_left _ _)]
    have h := M.bR_eq_dz a w c 0 s n (N := max (i + m + l + s.natAbs) (n + 1))
      (le_max_right _ _)
    unfold bR at h
    simp only [zero_add] at h
    exact h

/-- **Dong's lemma for `Good` vectors and `n ≥ 0`**: `a_(n) w` is local with every homogeneous
`b` (order `3 (i + m + j)`). -/
theorem dong_of_good_natCast {i m j : ℕ} {a w b : V} (ha : a ∈ M.grade i) (hga : M.Good a)
    (hw : w ∈ M.grade m) (hgw : M.Good w) (hb : b ∈ M.grade j) (n : ℕ) (p q : ℤ) (c : V) :
    dz k (2 * (i + m + j) + (i + m + j)) (M.comm (M.mode n a w) b c) p q = 0 := by
  have hD := dong_natCast (fun u => M.mode u a) (fun v => M.mode v w) (fun v => M.mode v b)
    (i + m + j) (M.opLocal_of_good ha hga hw (by omega)) (M.opLocal_of_good ha hga hb (by omega))
    (M.opLocal_of_good hw hgw hb (by omega)) n p q
  have hX : (fun s => dz k n (opComm (fun u => M.mode u a) (fun v => M.mode v w)) 0 s) =
      fun s => M.mode s (M.mode n a w) :=
    funext fun s => (M.mode_mode_natCast_eq_dz ha hga hw n s).symm
  rw [hX] at hD
  have h := LinearMap.congr_fun hD c
  rw [dz_linearMap_apply, LinearMap.zero_apply] at h
  exact h

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.d23_pow_eq_zero
#print axioms HaagerupIzumi.C8.dong_natCast
#print axioms HaagerupIzumi.C8.ModeAlgebra.mode_mode_natCast_eq_dz
#print axioms HaagerupIzumi.C8.ModeAlgebra.dong_of_good_natCast
