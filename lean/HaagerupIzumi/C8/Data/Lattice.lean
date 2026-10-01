module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The lattice `E₆ ⊕ A₂` and the finite arithmetic of the construction

This file formalizes the finite lattice data of Appendix A
(`sec:construction`, lines 1872–2019 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).

* `gram`: the Gram matrix of line 1874 (diagonal `2`, `-1` on the six listed
  edges; `gram_apply_edges`).  It is the Cartan matrix of `E₆ ⊕ A₂` after the
  relabeling `cartanIndex` (`gram_eq_cartan`, against Mathlib's
  `CartanMatrix.E₆` and `CartanMatrix.A 2`), it is positive definite
  (`form_self_pos`, via the explicit sum-of-squares certificate
  `four_mul_form_self`), and `det G = 9 = 3 · 3` (`det_gram`, via an explicit
  triangular certificate).
* `alphaL`, `coeffR`, `hR`: the vectors of line 1910 and the arithmetic of
  Lemma `lem:levels` (line 1929): `alphaL_norm`, `alphaL_orthogonal`,
  `hR_pairing`, `hR_norm`, `alphaL_hR`, levels `1` and `39`
  (`level_alphaL`, `level_hR`), and the scalar part of the double poles
  `(E_L)_1 F_L = 1`, `(E_R)_1 F_R = 39` (`leftCurrent_doublePole`,
  `rightCurrent_doublePole`).
* `cocycleExp`, `epsilon`: the cocycle `eq:cocycle` (line 1880) and the two
  identities of line 1895, both as exact integer identities of the exponent
  (`cocycleExp_add_swap`, `two_mul_cocycleExp_neg`), modulo two
  (`cocycleExp_sub_swap_zmod`, `cocycleExp_neg_zmod`) and for the signs in
  `ℤˣ` (`epsilon_mul_inv_swap`, `epsilon_neg_self`).
* `uMomentum`: the three momenta of `u` (eq:u, line 1964) have squared norm
  four and Cartan weight `(1,13)` (line 1997).
* Central charges (lines 2018, 2060): `c(A_{1,k}) = 3k/(k+2)` gives `1` and
  `117/41`, and `1 + 117/41 + 2400/1271 + 70/31 = 8`.
* `formR`: the same bilinear form with coefficients in any commutative ring
  (`L ⊗ R`), positive semidefinite over ordered rings (`formR_self_nonneg`) and positive
  definite over ordered fields (`formR_self_pos`).

Nothing here constructs the lattice vertex algebra; all statements are
kernel-checked facts about integers and rationals with no hypotheses.
-/

namespace HaagerupIzumi.C8
namespace Lattice

open Matrix

/-! ## The Gram matrix -/

/-- The six off-diagonal entries `-1` of the Gram matrix (line 1877). -/
def edges : List (Fin 8 × Fin 8) := [(0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (6, 7)]

/-- The Gram matrix `G` of `L = E₆ ⊕ A₂` in the manuscript's labeling
(line 1874). -/
def gram : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0, -1,  0,  0;
      0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2,  0,  0,  0;
      0,  0, -1,  0,  0,  2,  0,  0;
      0,  0,  0,  0,  0,  0,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

/-- The matrix literal is exactly the description of line 1874: diagonal two,
`-1` on the listed edges (symmetrized), zero elsewhere. -/
theorem gram_apply_edges (i j : Fin 8) :
    gram i j = if i = j then 2 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then -1 else 0 := by
  have h : ∀ p : Fin 8 × Fin 8, gram p.1 p.2 =
      if p.1 = p.2 then 2 else if (p.1, p.2) ∈ edges ∨ (p.2, p.1) ∈ edges then -1 else 0 := by
    decide
  exact h (i, j)

theorem gram_transpose : gramᵀ = gram := by decide

/-- Relabeling of the manuscript's simple roots into Bourbaki's labels of
`E₆` (Mathlib's `CartanMatrix.E₆`) followed by `A₂`. -/
def cartanIndex : Fin 8 → Fin 6 ⊕ Fin 2 :=
  ![.inl 0, .inl 2, .inl 3, .inl 4, .inl 5, .inl 1, .inr 0, .inr 1]

theorem cartanIndex_injective : Function.Injective cartanIndex := by decide

/-- `G` is the Cartan matrix of `E₆ ⊕ A₂`. -/
theorem gram_eq_cartan :
    gram = (fromBlocks CartanMatrix.E₆ 0 0 (CartanMatrix.A 2)).submatrix
      cartanIndex cartanIndex := by
  decide

/-! ## The bilinear form -/

/-- The lattice bilinear form `(a,b) = aᵀ G b` on coordinate vectors with
respect to the simple roots. -/
def form (a b : Fin 8 → ℤ) : ℤ := a ⬝ᵥ (gram *ᵥ b)

/-- The form as an explicit polynomial. -/
theorem form_apply (x y : Fin 8 → ℤ) :
    form x y =
      2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5
        + x 6 * y 6 + x 7 * y 7)
      - (x 0 * y 1 + x 1 * y 0) - (x 1 * y 2 + x 2 * y 1) - (x 2 * y 3 + x 3 * y 2)
      - (x 3 * y 4 + x 4 * y 3) - (x 2 * y 5 + x 5 * y 2) - (x 6 * y 7 + x 7 * y 6) := by
  simp only [form, dotProduct, mulVec, Fin.sum_univ_eight, gram, Matrix.of_apply,
    Matrix.cons_val]
  ring

theorem form_comm (a b : Fin 8 → ℤ) : form a b = form b a := by
  rw [form_apply, form_apply]; ring

theorem form_add_left (a b c : Fin 8 → ℤ) : form (a + b) c = form a c + form b c := by
  simp only [form_apply, Pi.add_apply]; ring

theorem form_add_right (a b c : Fin 8 → ℤ) : form a (b + c) = form a b + form a c := by
  simp only [form_apply, Pi.add_apply]; ring

theorem form_smul_left (n : ℤ) (a b : Fin 8 → ℤ) : form (n • a) b = n * form a b := by
  simp only [form_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem form_smul_right (n : ℤ) (a b : Fin 8 → ℤ) : form a (n • b) = n * form a b := by
  simp only [form_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem form_neg_left (a b : Fin 8 → ℤ) : form (-a) b = -form a b := by
  simp only [form_apply, Pi.neg_apply]; ring

theorem form_neg_right (a b : Fin 8 → ℤ) : form a (-b) = -form a b := by
  simp only [form_apply, Pi.neg_apply]; ring

/-- `L` is even: `(x,x) = 2 · q(x)` with an explicit integral quadratic form. -/
theorem form_self_eq_two_mul (x : Fin 8 → ℤ) :
    form x x = 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2
      + x 7 ^ 2 - x 0 * x 1 - x 1 * x 2 - x 2 * x 3 - x 3 * x 4 - x 2 * x 5 - x 6 * x 7) := by
  rw [form_apply]; ring

/-! ## Positive definiteness and the determinant -/

/-- Sum-of-squares certificate: `4 (x,x)` is a sum of squares of integral linear
forms (the first six come from the standard embedding `E₆ ⊂ E₈ ⊂ (½ℤ)⁸`, the
last from `A₂`). -/
theorem four_mul_form_self (x : Fin 8 → ℤ) :
    4 * form x x = (x 0 - 2 * x 1 + 2 * x 5) ^ 2 + (-x 0 + 2 * x 1 - 2 * x 2 + 2 * x 5) ^ 2
      + (-x 0 + 2 * x 2 - 2 * x 3) ^ 2 + (-x 0 + 2 * x 3 - 2 * x 4) ^ 2 + (-x 0 + 2 * x 4) ^ 2
      + 3 * x 0 ^ 2 + 4 * (x 6 ^ 2 + x 7 ^ 2 + (x 6 - x 7) ^ 2) := by
  rw [form_apply]; ring

theorem form_self_nonneg (x : Fin 8 → ℤ) : 0 ≤ form x x := by
  have h := four_mul_form_self x
  have h4 : 0 ≤ 4 * form x x := by rw [h]; positivity
  linarith

/-- The lattice form is positive definite. -/
theorem form_self_pos {x : Fin 8 → ℤ} (hx : x ≠ 0) : 0 < form x x := by
  rcases (form_self_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have h4 := four_mul_form_self x
    rw [← h, mul_zero] at h4
    have s1 := sq_nonneg (x 0 - 2 * x 1 + 2 * x 5)
    have s2 := sq_nonneg (-x 0 + 2 * x 1 - 2 * x 2 + 2 * x 5)
    have s3 := sq_nonneg (-x 0 + 2 * x 2 - 2 * x 3)
    have s4 := sq_nonneg (-x 0 + 2 * x 3 - 2 * x 4)
    have s5 := sq_nonneg (-x 0 + 2 * x 4)
    have s6 := sq_nonneg (x 0)
    have s7 := sq_nonneg (x 6)
    have s8 := sq_nonneg (x 7)
    have s9 := sq_nonneg (x 6 - x 7)
    have e1 : x 0 - 2 * x 1 + 2 * x 5 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e2 : -x 0 + 2 * x 1 - 2 * x 2 + 2 * x 5 = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e3 : -x 0 + 2 * x 2 - 2 * x 3 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e4 : -x 0 + 2 * x 3 - 2 * x 4 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e5 : -x 0 + 2 * x 4 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e6 : x 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e7 : x 6 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e8 : x 7 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have h0 : x 0 = 0 := e6
    have h4' : x 4 = 0 := by omega
    have h3 : x 3 = 0 := by omega
    have h2 : x 2 = 0 := by omega
    have h1 : x 1 = 0 := by omega
    have h5 : x 5 = 0 := by omega
    funext i
    fin_cases i
    exacts [h0, h1, h2, h3, h4', h5, e7, e8]

/-- Left factor of the triangular determinant certificate (lower triangular,
diagonal product `480`). -/
def detCertP : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     1, 2, 0, 0, 0, 0, 0, 0;
     1, 2, 3, 0, 0, 0, 0, 0;
     1, 2, 3, 4, 0, 0, 0, 0;
     1, 2, 3, 4, 5, 0, 0, 0;
     1, 2, 3, 2, 1, 2, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 2]

/-- Right side of the certificate (upper triangular, diagonal product `4320`). -/
def detCertU : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
     0, 3, -2, 0, 0, 0, 0, 0;
     0, 0, 4, -3, 0, -3, 0, 0;
     0, 0, 0, 5, -4, -3, 0, 0;
     0, 0, 0, 0, 6, -3, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 2, -1;
     0, 0, 0, 0, 0, 0, 0, 3]

theorem detCert_mul : detCertP * gram = detCertU := by decide

/-- `det G = 9 = 3 · 3`: the discriminant group `L^*/L` has order nine. -/
theorem det_gram : gram.det = 9 := by
  have hPl : ∀ p : Fin 8 × Fin 8, p.1.val < p.2.val → detCertP p.1 p.2 = 0 := by decide
  have hUu : ∀ p : Fin 8 × Fin 8, p.2.val < p.1.val → detCertU p.1 p.2 = 0 := by decide
  have hP : detCertP.det = 480 := by
    rw [Matrix.det_of_isLowerTriangular detCertP
      (fun i j hij => hPl (i, j) (OrderDual.toDual_lt_toDual.mp hij))]
    decide
  have hU : detCertU.det = 4320 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hUu (i, j) hij)]
    decide
  have h := congrArg Matrix.det detCert_mul
  rw [Matrix.det_mul, hP, hU] at h
  omega

theorem det_A2 : (CartanMatrix.A 2).det = 3 := by
  rw [Matrix.det_fin_two]; decide

theorem det_gram_eq_mul : gram.det = CartanMatrix.E₆.det * (CartanMatrix.A 2).det := by
  rw [det_gram, CartanMatrix.E₆_det, det_A2]; rfl

/-! ## The current data of Lemma `lem:levels` -/

/-- Simple root `α_i` as a coordinate vector. -/
def simpleRoot (i : Fin 8) : Fin 8 → ℤ := Pi.single i 1

/-- `α_L = (-1,-2,-3,-2,-1,-2,0,0)` (line 1911); it is minus the highest root
of `E₆`. -/
def alphaL : Fin 8 → ℤ := ![-1, -2, -3, -2, -1, -2, 0, 0]

/-- The coefficients `c = (5,8,9,8,5,0,2,2)` (line 1913). -/
def coeffR : Fin 8 → ℤ := ![5, 8, 9, 8, 5, 0, 2, 2]

/-- `h_R = ∑ c_i α_i` (line 1914). -/
def hR : Fin 8 → ℤ := ∑ i, coeffR i • simpleRoot i

theorem hR_eq_coeffR : hR = coeffR := by decide

theorem simpleRoot_norm : ∀ i : Fin 8, form (simpleRoot i) (simpleRoot i) = 2 := by decide

/-- `(α_L, α_L) = 2`. -/
theorem alphaL_norm : form alphaL alphaL = 2 := by decide

/-- `(α_L, α_i) = 0` whenever `c_i ≠ 0`. -/
theorem alphaL_orthogonal : ∀ i : Fin 8, coeffR i ≠ 0 → form alphaL (simpleRoot i) = 0 := by
  decide

/-- `(h_R, α_i) = 2` for every `c_i ≠ 0`. -/
theorem hR_pairing : ∀ i : Fin 8, coeffR i ≠ 0 → form hR (simpleRoot i) = 2 := by decide

/-- `(h_R, h_R) = 78`. -/
theorem hR_norm : form hR hR = 78 := by decide

/-- The two Cartan directions are orthogonal: `(α_L, h_R) = 0`. -/
theorem alphaL_hR : form alphaL hR = 0 := by decide

/-- The level of an `sl₂` with Cartan element `h(-1)𝟙` is `(h,h)/2`. -/
def level (h : Fin 8 → ℤ) : ℤ := form h h / 2

theorem level_alphaL : level alphaL = 1 := by decide

theorem level_hR : level hR = 39 := by decide

theorem coeffR_sum : ∑ i, coeffR i = 39 := by decide

/-- For `i ≠ j` the pole order `(α_i, -α_j)` is nonnegative, so
`(e^{α_i})_1 e^{-α_j} = 0`; only the diagonal terms contribute to
`(E_R)_1 F_R`. -/
theorem simpleRoot_offDiag_pairing :
    ∀ p : Fin 8 × Fin 8, p.1 ≠ p.2 → 0 ≤ form (simpleRoot p.1) (-simpleRoot p.2) := by
  decide

/-! ## The cocycle -/

/-- Exponent of the cocycle `eq:cocycle`:
`ε(a,b) = (-1)^{∑_i a_i b_i + ∑_{i>j} a_i b_j G_ij}`. -/
def cocycleExp (a b : Fin 8 → ℤ) : ℤ :=
  ∑ i, a i * b i + ∑ i, ∑ j, if j < i then a i * b j * gram i j else 0

theorem cocycleExp_apply (a b : Fin 8 → ℤ) :
    cocycleExp a b =
      (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 + a 4 * b 4 + a 5 * b 5 + a 6 * b 6
        + a 7 * b 7)
      - (a 1 * b 0 + a 2 * b 1 + a 3 * b 2 + a 4 * b 3 + a 5 * b 2 + a 7 * b 6) := by
  simp [cocycleExp, Fin.sum_univ_eight, gram, Matrix.cons_val]
  ring

/-- `ε(a,b) ε(b,a)⁻¹ = (-1)^{(a,b)}`, at the level of exponents: their sum is
exactly the form. -/
theorem cocycleExp_add_swap (a b : Fin 8 → ℤ) :
    cocycleExp a b + cocycleExp b a = form a b := by
  rw [cocycleExp_apply, cocycleExp_apply, form_apply]; ring

/-- `ε(a,-a) = (-1)^{(a,a)/2}`, at the level of exponents. -/
theorem two_mul_cocycleExp_neg (a : Fin 8 → ℤ) : 2 * cocycleExp a (-a) = -form a a := by
  rw [cocycleExp_apply, form_apply]; simp only [Pi.neg_apply]; ring

theorem cocycleExp_neg_eq (a : Fin 8 → ℤ) : cocycleExp a (-a) = -(form a a / 2) := by
  have h := two_mul_cocycleExp_neg a
  omega

/-- The exponent identity modulo two: `e(a,b) - e(b,a) ≡ (a,b)`. -/
theorem cocycleExp_sub_swap_zmod (a b : Fin 8 → ℤ) :
    ((cocycleExp a b - cocycleExp b a : ℤ) : ZMod 2) = ((form a b : ℤ) : ZMod 2) := by
  rw [ZMod.intCast_eq_intCast_iff']
  have h := cocycleExp_add_swap a b
  push_cast
  omega

/-- The exponent identity modulo two: `e(a,-a) ≡ (a,a)/2`. -/
theorem cocycleExp_neg_zmod (a : Fin 8 → ℤ) :
    ((cocycleExp a (-a) : ℤ) : ZMod 2) = ((form a a / 2 : ℤ) : ZMod 2) := by
  rw [ZMod.intCast_eq_intCast_iff']
  have h := cocycleExp_neg_eq a
  push_cast
  omega

/-- The cocycle sign `ε(a,b) ∈ {±1}`. -/
def epsilon (a b : Fin 8 → ℤ) : ℤˣ := (cocycleExp a b).negOnePow

/-- `ε(α,β) / ε(β,α) = (-1)^{(α,β)}` (line 1895). -/
theorem epsilon_mul_inv_swap (a b : Fin 8 → ℤ) :
    epsilon a b * (epsilon b a)⁻¹ = (form a b).negOnePow := by
  rw [Int.units_inv_eq_self, epsilon, epsilon, ← Int.negOnePow_add, cocycleExp_add_swap]

/-- `ε(α,-α) = (-1)^{(α,α)/2}` (line 1897). -/
theorem epsilon_neg_self (a : Fin 8 → ℤ) : epsilon a (-a) = (form a a / 2).negOnePow := by
  rw [epsilon, cocycleExp_neg_eq, Int.negOnePow_neg]

/-- For a root (`(α,α) = 2`), `ε(α,-α) = -1`; this fixes the sign
`e^α_0 e^{-α} = -α(-1)𝟙`. -/
theorem epsilon_root {a : Fin 8 → ℤ} (ha : form a a = 2) : epsilon a (-a) = -1 := by
  rw [epsilon_neg_self, ha]; rfl

/-- Scalar part of `(E_L)_1 F_L = 𝟙`: with `F_L = -e^{-α_L}`,
`(E_L)_1 F_L = -ε(α_L,-α_L) 𝟙`. -/
theorem leftCurrent_doublePole : -((epsilon alphaL (-alphaL) : ℤˣ) : ℤ) = 1 := by
  rw [epsilon_root alphaL_norm]; rfl

/-- Scalar part of `(E_R)_1 F_R = 39 𝟙`: with `E_R = ∑_{c_i ≠ 0} e^{α_i}` and
`F_R = -∑ c_i e^{-α_i}`, only diagonal terms contribute
(`simpleRoot_offDiag_pairing`), each giving `-c_i ε(α_i,-α_i)`. -/
theorem rightCurrent_doublePole :
    ∑ i, coeffR i * -((epsilon (simpleRoot i) (-simpleRoot i) : ℤˣ) : ℤ) = 39 := by
  have h : ∀ i, epsilon (simpleRoot i) (-simpleRoot i) = -1 :=
    fun i => epsilon_root (simpleRoot_norm i)
  simp only [h, Units.val_neg, Units.val_one, neg_neg, mul_one]
  exact coeffR_sum

/-! ## The momenta of `u` -/

/-- The three momenta in `eq:u`. -/
def uMomentum : Fin 3 → Fin 8 → ℤ :=
  ![![0, 0, 0, 0, 0, -1, 1, 1], ![0, 0, 0, 1, 1, -1, 0, 0], ![1, 1, 0, 0, 0, -1, 0, 0]]

/-- All three momenta have squared norm four (so `e^α` has weight two). -/
theorem uMomentum_norm : ∀ k : Fin 3, form (uMomentum k) (uMomentum k) = 4 := by decide

/-- All three momenta have Cartan weight `(1,13)`. -/
theorem uMomentum_cartanWeight :
    ∀ k : Fin 3, form alphaL (uMomentum k) = 1 ∧ form hR (uMomentum k) = 13 := by
  decide

/-! ## Central charges -/

/-- The Sugawara central charge `3k/(k+2)` of `A_{1,k}`. -/
def affineCentralCharge (k : ℚ) : ℚ := 3 * k / (k + 2)

theorem affineCentralCharge_one : affineCentralCharge 1 = 1 := by
  norm_num [affineCentralCharge]

theorem affineCentralCharge_39 : affineCentralCharge 39 = 117 / 41 := by
  norm_num [affineCentralCharge]

/-- The central charges of the two neutral fields `e, f` (eq:two-coset-stresses). -/
def centralChargeE : ℚ := 2400 / 1271

def centralChargeF : ℚ := 70 / 31

/-- `1 + 117/41 + 2400/1271 + 70/31 = 8 = rank L`. -/
theorem centralCharge_sum :
    affineCentralCharge 1 + affineCentralCharge 39 + centralChargeE + centralChargeF = 8 := by
  norm_num [affineCentralCharge, centralChargeE, centralChargeF]

/-- The affine central charges sum to `1 + 117/41 < 8` (line 2019). -/
theorem affineCentralCharge_sum_lt :
    affineCentralCharge 1 + affineCentralCharge 39 = 1 + 117 / 41 ∧
      affineCentralCharge 1 + affineCentralCharge 39 < 8 := by
  norm_num [affineCentralCharge]

/-! ## The form with coefficients in a ring (`L ⊗ R`) -/

/-- The lattice form extended to `R`-coefficients. -/
def formR {R : Type*} [CommRing R] (x y : Fin 8 → R) : R :=
  x ⬝ᵥ (gram.map (Int.cast : ℤ → R) *ᵥ y)

theorem formR_apply {R : Type*} [CommRing R] (x y : Fin 8 → R) :
    formR x y =
      2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5
        + x 6 * y 6 + x 7 * y 7)
      - (x 0 * y 1 + x 1 * y 0) - (x 1 * y 2 + x 2 * y 1) - (x 2 * y 3 + x 3 * y 2)
      - (x 3 * y 4 + x 4 * y 3) - (x 2 * y 5 + x 5 * y 2) - (x 6 * y 7 + x 7 * y 6) := by
  simp only [formR, dotProduct, mulVec, Fin.sum_univ_eight, Matrix.map_apply, gram,
    Matrix.of_apply, Matrix.cons_val, Int.cast_ofNat, Int.cast_neg, Int.cast_one,
    Int.cast_zero]
  ring

theorem formR_intCast {R : Type*} [CommRing R] (a b : Fin 8 → ℤ) :
    formR (fun i => (a i : R)) (fun i => (b i : R)) = ((form a b : ℤ) : R) := by
  rw [formR_apply, form_apply]; push_cast; ring

theorem formR_comm {R : Type*} [CommRing R] (x y : Fin 8 → R) : formR x y = formR y x := by
  rw [formR_apply, formR_apply]; ring

/-- The quadratic expansion of `formR` (bilinearity and symmetry). -/
theorem formR_expand {R : Type*} [CommRing R] (s t : R) (x y : Fin 8 → R) :
    formR (s • x + t • y) (s • x + t • y) =
      s ^ 2 * formR x x + 2 * s * t * formR x y + t ^ 2 * formR y y := by
  simp only [formR_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem four_mul_formR_self {R : Type*} [CommRing R] (x : Fin 8 → R) :
    4 * formR x x = (x 0 - 2 * x 1 + 2 * x 5) ^ 2 + (-x 0 + 2 * x 1 - 2 * x 2 + 2 * x 5) ^ 2
      + (-x 0 + 2 * x 2 - 2 * x 3) ^ 2 + (-x 0 + 2 * x 3 - 2 * x 4) ^ 2 + (-x 0 + 2 * x 4) ^ 2
      + 3 * x 0 ^ 2 + 4 * (x 6 ^ 2 + x 7 ^ 2 + (x 6 - x 7) ^ 2) := by
  rw [formR_apply]; ring

/-- Positive semidefiniteness over any ordered ring (e.g. `L ⊗ ℝ`). -/
theorem formR_self_nonneg {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : Fin 8 → R) : 0 ≤ formR x x := by
  have h := four_mul_formR_self x
  have h4 : 0 ≤ 4 * formR x x := by rw [h]; positivity
  linarith

/-- Positive definiteness over any ordered field (e.g. `L ⊗ ℚ`, `L ⊗ ℝ`). -/
theorem formR_self_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {x : Fin 8 → R} (hx : x ≠ 0) : 0 < formR x x := by
  rcases (formR_self_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have h4 := four_mul_formR_self x
    rw [← h, mul_zero] at h4
    have s1 := sq_nonneg (x 0 - 2 * x 1 + 2 * x 5)
    have s2 := sq_nonneg (-x 0 + 2 * x 1 - 2 * x 2 + 2 * x 5)
    have s3 := sq_nonneg (-x 0 + 2 * x 2 - 2 * x 3)
    have s4 := sq_nonneg (-x 0 + 2 * x 3 - 2 * x 4)
    have s5 := sq_nonneg (-x 0 + 2 * x 4)
    have s6 := sq_nonneg (x 0)
    have s7 := sq_nonneg (x 6)
    have s8 := sq_nonneg (x 7)
    have s9 := sq_nonneg (x 6 - x 7)
    have e1 : x 0 - 2 * x 1 + 2 * x 5 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e2 : -x 0 + 2 * x 1 - 2 * x 2 + 2 * x 5 = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e3 : -x 0 + 2 * x 2 - 2 * x 3 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e4 : -x 0 + 2 * x 3 - 2 * x 4 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e5 : -x 0 + 2 * x 4 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e6 : x 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e7 : x 6 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have e8 : x 7 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
    have h4' : x 4 = 0 := by linarith
    have h3 : x 3 = 0 := by linarith
    have h2 : x 2 = 0 := by linarith
    have h1 : x 1 = 0 := by linarith
    have h5 : x 5 = 0 := by linarith
    funext i
    fin_cases i
    exacts [e6, h1, h2, h3, h4', h5, e7, e8]

#print axioms gram_apply_edges
#print axioms gram_eq_cartan
#print axioms form_self_pos
#print axioms det_gram
#print axioms det_gram_eq_mul
#print axioms alphaL_norm
#print axioms alphaL_orthogonal
#print axioms hR_pairing
#print axioms hR_norm
#print axioms alphaL_hR
#print axioms level_alphaL
#print axioms level_hR
#print axioms rightCurrent_doublePole
#print axioms leftCurrent_doublePole
#print axioms cocycleExp_add_swap
#print axioms cocycleExp_sub_swap_zmod
#print axioms cocycleExp_neg_zmod
#print axioms epsilon_mul_inv_swap
#print axioms epsilon_neg_self
#print axioms uMomentum_norm
#print axioms uMomentum_cartanWeight
#print axioms centralCharge_sum
#print axioms affineCentralCharge_sum_lt
#print axioms formR_self_nonneg
#print axioms formR_self_pos

end Lattice
end HaagerupIzumi.C8
