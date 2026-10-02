module

public import HaagerupIzumi.C8.Lattice.Semantic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Coefficients in `ℚ(√13, √-3)`

Work item W2 (option (c)), `C8/ROADMAP.md`.  The certificates of the c=8 construction have
coefficients in `ℚ(s, t)`, `s² = 13`, `t² = -3`, written in the basis `1, s, t, st`
(`hi_cft_20260923_c8_exact.py`, class `A`).

* `QA`: computable elements `a + b s + c t + d st` with the multiplication table of
  `A.__mul__` (`QA.mul`) and the inverse `QA.inv` (product of the three conjugates over the
  norm, as `A.inv`).
* `QA.toC`: the embedding into `ℂ` with `s ↦ √13`, `t ↦ √3 i` (`sC`, `tC`); it is additive and
  multiplicative (`QA.toC_add`, `QA.toC_mul`), so kernel computations in `QA` are computations
  in `ℂ`; `QA.toC_ne_zero_of_mul_eq_one` turns a kernel-checked inverse into `toC x ≠ 0`.
* `Vec4`: a vector with coefficients in `ℚ(s, t)` as four rational sparse vectors (the
  components along `1, s, t, st`).  All list arithmetic is the rational arithmetic of
  `Lattice/Fock.lean`; `Vec4.smulQA` and `Vec4.mode` apply the multiplication table to the
  components (the modes of the lattice vertex algebra have rational structure constants, so a
  mode of `Vec4`s is a combination of sixteen rational modes).

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## The number field -/

/-- An element `a + b s + c t + d st` of `ℚ(s, t)`, `s² = 13`, `t² = -3`. -/
structure QA where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

namespace QA

def zero : QA := ⟨0, 0, 0, 0⟩

def one : QA := ⟨1, 0, 0, 0⟩

/-- A rational number. -/
def ofRat (q : ℚ) : QA := ⟨q, 0, 0, 0⟩

def add (x y : QA) : QA := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

def neg (x : QA) : QA := ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- Multiplication: `s² = 13`, `t² = -3`, `(st)² = -39`, `s·st = 13t`, `t·st = -3s`. -/
def mul (x y : QA) : QA :=
  ⟨x.a * y.a + 13 * (x.b * y.b) - 3 * (x.c * y.c) - 39 * (x.d * y.d),
   x.a * y.b + x.b * y.a - 3 * (x.c * y.d + x.d * y.c),
   x.a * y.c + x.c * y.a + 13 * (x.b * y.d + x.d * y.b),
   x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩

/-- The conjugate flipping the signs of the components selected by `mask` (`A.conj`). -/
def conj1 (x : QA) : QA := ⟨x.a, -x.b, x.c, -x.d⟩

def conj2 (x : QA) : QA := ⟨x.a, x.b, -x.c, -x.d⟩

def conj3 (x : QA) : QA := ⟨x.a, -x.b, -x.c, x.d⟩

/-- The inverse `(σ₁x σ₂x σ₃x) / N(x)` (`A.inv`); `QA.mul x (QA.inv x) = QA.one` is checked by
kernel evaluation where it is used. -/
def inv (x : QA) : QA :=
  let num := mul (mul (conj1 x) (conj2 x)) (conj3 x)
  let n := (mul x num).a
  ⟨num.a / n, num.b / n, num.c / n, num.d / n⟩

end QA

/-! ## The embedding into `ℂ` -/

/-- `s ↦ √13`. -/
noncomputable def sC : ℂ := (Real.sqrt 13 : ℂ)

/-- `t ↦ √3 i`. -/
noncomputable def tC : ℂ := (Real.sqrt 3 : ℂ) * Complex.I

theorem sC_mul_self : sC * sC = 13 := by
  rw [sC, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem tC_mul_self : tC * tC = -3 := by
  have h3 : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  calc tC * tC = ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (Complex.I * Complex.I) := by
        unfold tC
        ring
    _ = -3 := by
        rw [h3, Complex.I_mul_I]
        ring

namespace QA

/-- The value in `ℂ`. -/
noncomputable def toC (x : QA) : ℂ := (x.a : ℂ) + (x.b : ℂ) * sC + (x.c : ℂ) * tC + (x.d : ℂ) * (sC * tC)

theorem toC_zero : zero.toC = 0 := by
  simp [toC, zero]

theorem toC_one : one.toC = 1 := by
  simp [toC, one]

theorem toC_ofRat (q : ℚ) : (ofRat q).toC = (q : ℂ) := by
  simp [toC, ofRat]

theorem toC_add (x y : QA) : (add x y).toC = x.toC + y.toC := by
  simp only [toC, add]
  push_cast
  ring

theorem toC_neg (x : QA) : (neg x).toC = -x.toC := by
  simp only [toC, neg]
  push_cast
  ring

theorem toC_mul (x y : QA) : (mul x y).toC = x.toC * y.toC := by
  simp only [toC, mul]
  push_cast
  linear_combination
    (-((x.b : ℂ) * y.b + ((x.b : ℂ) * y.d + (x.d : ℂ) * y.b) * tC + (x.d : ℂ) * y.d * (tC * tC))) *
      sC_mul_self +
    (-((x.c : ℂ) * y.c + ((x.c : ℂ) * y.d + (x.d : ℂ) * y.c) * sC + 13 * ((x.d : ℂ) * y.d))) *
      tC_mul_self

theorem toC_ne_zero_of_mul_eq_one {x y : QA} (h : mul x y = one) : x.toC ≠ 0 := by
  intro h0
  have := congrArg toC h
  rw [toC_mul, toC_one, h0, zero_mul] at this
  exact zero_ne_one this

end QA

/-! ## Vectors over `ℚ(s, t)` -/

/-- A sparse vector `v₀ + s v₁ + t v₂ + st v₃` with rational sparse vectors `vᵢ`. -/
structure Vec4 where
  c0 : Vec
  c1 : Vec
  c2 : Vec
  c3 : Vec
  deriving DecidableEq

namespace Vec4

def zero : Vec4 := ⟨[], [], [], []⟩

/-- A rational vector. -/
def ofVec (v : Vec) : Vec4 := ⟨v, [], [], []⟩

def add (x y : Vec4) : Vec4 :=
  ⟨addVec x.c0 y.c0, addVec x.c1 y.c1, addVec x.c2 y.c2, addVec x.c3 y.c3⟩

/-- The rational vector `p v₀ + q v₁ + r v₂ + w v₃` (four scalings and three merges). -/
def comb (p q r w : ℚ) (v0 v1 v2 v3 : Vec) : Vec :=
  addVec (smul p v0) (addVec (smul q v1) (addVec (smul r v2) (smul w v3)))

/-- Multiplication by `a + b s + c t + d st` (the table of `QA.mul`). -/
def smulQA (z : QA) (x : Vec4) : Vec4 :=
  ⟨comb z.a (13 * z.b) (-3 * z.c) (-39 * z.d) x.c0 x.c1 x.c2 x.c3,
   comb z.b z.a (-3 * z.d) (-3 * z.c) x.c0 x.c1 x.c2 x.c3,
   comb z.c (13 * z.d) z.a (13 * z.b) x.c0 x.c1 x.c2 x.c3,
   comb z.d z.c z.b z.a x.c0 x.c1 x.c2 x.c3⟩

/-- The mode `x_(m) y`: sixteen rational modes combined with the multiplication table. -/
def mode (x : Vec4) (m : ℤ) (y : Vec4) : Vec4 :=
  ⟨addVec (LatticeVOA.mode x.c0 m y.c0) (addVec (smul 13 (LatticeVOA.mode x.c1 m y.c1))
      (addVec (smul (-3) (LatticeVOA.mode x.c2 m y.c2)) (smul (-39) (LatticeVOA.mode x.c3 m y.c3)))),
   addVec (LatticeVOA.mode x.c0 m y.c1) (addVec (LatticeVOA.mode x.c1 m y.c0)
      (smul (-3) (addVec (LatticeVOA.mode x.c2 m y.c3) (LatticeVOA.mode x.c3 m y.c2)))),
   addVec (LatticeVOA.mode x.c0 m y.c2) (addVec (LatticeVOA.mode x.c2 m y.c0)
      (smul 13 (addVec (LatticeVOA.mode x.c1 m y.c3) (LatticeVOA.mode x.c3 m y.c1)))),
   addVec (LatticeVOA.mode x.c0 m y.c3) (addVec (LatticeVOA.mode x.c3 m y.c0)
      (addVec (LatticeVOA.mode x.c1 m y.c2) (LatticeVOA.mode x.c2 m y.c1)))⟩

/-- All states of all components satisfy `P`. -/
def AllStates (P : State → Prop) (x : Vec4) : Prop :=
  (∀ p ∈ x.c0, P p.1) ∧ (∀ p ∈ x.c1, P p.1) ∧ (∀ p ∈ x.c2, P p.1) ∧ (∀ p ∈ x.c3, P p.1)

instance (P : State → Prop) [DecidablePred P] (x : Vec4) : Decidable (AllStates P x) :=
  inferInstanceAs (Decidable ((∀ p ∈ x.c0, P p.1) ∧ (∀ p ∈ x.c1, P p.1) ∧ (∀ p ∈ x.c2, P p.1) ∧
    (∀ p ∈ x.c3, P p.1)))

/-- The coefficient (in `ℚ(s, t)`) of a state. -/
def coeff (x : Vec4) (s : State) : QA :=
  ⟨coeffOf x.c0 s, coeffOf x.c1 s, coeffOf x.c2 s, coeffOf x.c3 s⟩

end Vec4

/-- Decode a `Vec4` from four lists of term rows (`decVec`). -/
def decVec4 (l0 l1 l2 l3 : List (List ℕ)) : Vec4 := ⟨decVec l0, decVec l1, decVec l2, decVec l3⟩

/-- Decode a coefficient `[zz a₁, a₂, zz b₁, b₂, zz c₁, c₂, zz d₁, d₂]` (`aᵢ` numerator and
denominator of each component). -/
def decQA : List ℕ → QA
  | a1 :: a2 :: b1 :: b2 :: c1 :: c2 :: d1 :: d2 :: _ =>
    ⟨(unzig a1 : ℚ) / (a2 : ℚ), (unzig b1 : ℚ) / (b2 : ℚ), (unzig c1 : ℚ) / (c2 : ℚ),
      (unzig d1 : ℚ) / (d2 : ℚ)⟩
  | _ => QA.zero

/-! ## Checks -/

example : QA.mul ⟨1, 1, 1, 1⟩ ⟨1, 1, 1, 1⟩ = ⟨1 + 13 - 3 - 39, 2 - 6, 2 + 26, 4⟩ := by
  decide +kernel

example : QA.mul ⟨1 / 2, 1 / 3, 1 / 5, 1 / 7⟩ (QA.inv ⟨1 / 2, 1 / 3, 1 / 5, 1 / 7⟩) = QA.one := by
  decide +kernel

#print axioms QA.toC_mul
#print axioms QA.toC_ne_zero_of_mul_eq_one

end LatticeVOA
end HaagerupIzumi.C8
