module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Abelian 3-cocycles on `ℤ/3`: trivial twists force the trivial class

The Tannakian step for `L₋` in the proof of `L_untwisted` (manuscript
`haagerup_c8_expanded.tex`, lines 3335–3337: "The pointed subcategory on `L₋` is symmetric with
trivial twists, hence Tannakian; as a tensor category it is the untwisted `Vec_{ℤ/3}`"), at the
level of cocycles (Eilenberg–MacLane).

**Definitions** (for an additive group `A` and a multiplicative commutative group `G`, e.g.
`G = 𝕜ˣ`).  `AbelianCocycle A G`: a pair `(ω, c)`, `ω : A → A → A → G`, `c : A → A → G`, with
* the pentagon `ω(w,x,y) ω(w,x+y,z) ω(x,y,z) = ω(w+x,y,z) ω(w,x,y+z)`;
* the hexagons `ω(x,y,z) c(x,y+z) ω(y,z,x) = c(x,y) ω(y,x,z) c(x,z)` and
  `ω(x,y,z)⁻¹ c(x+y,z) ω(z,x,y)⁻¹ = c(y,z) ω(x,z,y)⁻¹ c(x,z)`;
* normalization `ω(0,y,z) = ω(x,0,z) = ω(x,y,0) = 1`.
These are exactly the pentagon and the two hexagon axioms (Mathlib's `hexagon_forward`,
`hexagon_reverse`) of the skeletal category `Vec_A` with associator `ω` and braiding `c`.
`AbelianCocycle.Cohomologous Z Z'`: `Z' = Z · ∂f` for some `f : A → A → G`, where
`ω'(x,y,z) f(y,z) f(x,y+z) = ω(x,y,z) f(x,y) f(x+y,z)` and `c'(x,y) f(y,x) = c(x,y) f(x,y)`: this
says that the identity functor with tensorator `f` is a braided monoidal equivalence
`(Vec_A, ω, c) ≃ (Vec_A, ω', c')`.  `IsTrivial Z`: cohomologous to `(1, 1)`.

**Results** (`A = ℤ/3`, any commutative group `G`; no field hypotheses are needed).
* `invariant_eq`: `ω(1,1,1) ω(1,2,1) = c(1,1)³` (the class of `ω` in `H³(ℤ/3, G)` is the cube of
  the twist `q(1) = c(1,1)`).
* `isTrivial_of_trace_eq_one`: **if `c(x,x) = 1` for all `x` (trivial twists), then `(ω, c)` is
  cohomologous to `(1, 1)`**; explicitly with `f(1,2) = ω(1,1,2)`, `f(2,1) = ω(2,2,1)` and
  `f = 1` elsewhere.  `trace_eq_one_of_isTrivial`: the converse, so `isTrivial_iff`.
* `trace_eq_of_cohomologous`: the twist `c(x,x)` is a cohomology invariant.

**The bridge.**  A pointed braided fusion category whose simple objects form the group `A` is
braided equivalent to `Vec_A` with associator `ω` and braiding `c` for an abelian 3-cocycle
`(ω, c)`, unique up to cohomology (skeletalization; see EGNO, Chapters 2 and 8, and
Joyal–Street, *Braided tensor categories*, 1993).  Its twists are `θ_x = c(x,x)`; this uses that
the invertible objects have dimension `d_x = 1`.  The direction needed here (from the category
to the cocycle) is formalized for the objects `S (a, -a)` in `Category/PointedCocycle.lean`
(`pointedCocycle`, well defined up to `Cohomologous`), and with trivial twists
`isTrivial_of_trace_eq_one` gives `Lminus_untwisted_symmetric`.

Status of the Tannakian step for `L₋` (4 October 2026): the abelian 3-cocycle of the pointed
braided category on the invertibles `S (a, -a)` is constructed in `Category/PointedCocycle.lean`
(`pentagon_scalar`, `hexagon_forward_scalar`, `hexagon_reverse_scalar`) and trivialized in
`Category/PointedCocycleZ3.lean` (`Lminus_untwisted_symmetric`); the resulting braided monoidal
functor from the symmetric discrete `ℤ/3` is `Lminus_braided_vec`
(`Category/LminusBraidedVec.lean`), and into `LminusClosure S` with its own monoidal structure
and inherited braiding it is `Lminus_closure_braided_functor`
(`Category/LminusClosureFunctor.lean`); `LminusClosure S` is symmetric and equivalent, as a
category, to the additive envelope of its simples (`Category/LminusEnvelope.lean`).  Remaining
external: `hθ` (the self-braiding of each invertible of `L₋` in `Rep(B)` is trivial).  The monoidal comparison on general graded objects is
`GrMat.Lminus_graded_braided_equivalence` and `Lminus_vec_braided_equivalence`
(`Category/GradedMat.lean`, `Category/GradedMatMonoidal.lean`).  Composed with free induction it is
`untwisted_vec_equivalence_of_separable` (`Category/UntwistedVecEquivalence.lean`). -/

namespace HaagerupIzumi.C8

namespace AbelianCocycleZ3

/-- `ZMod 3` has three elements. -/
theorem cases3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide

theorem t11 : (1 : ZMod 3) + 1 = 2 := by decide
theorem t12 : (1 : ZMod 3) + 2 = 0 := by decide
theorem t21 : (2 : ZMod 3) + 1 = 0 := by decide
theorem t22 : (2 : ZMod 3) + 2 = 1 := by decide

section Additive

set_option linter.unusedSimpArgs false

variable {M : Type*} [AddCommGroup M] (ω : ZMod 3 → ZMod 3 → ZMod 3 → M)
  (c : ZMod 3 → ZMod 3 → M)
  (hP : ∀ w x y z, ω w x y + ω w (x + y) z + ω x y z = ω (w + x) y z + ω w x (y + z))
  (hH1 : ∀ x y z, ω x y z + c x (y + z) + ω y z x = c x y + ω y x z + c x z)
  (hH2 : ∀ x y z, -ω x y z + c (x + y) z + -ω z x y = c y z + -ω x z y + c x z)
  (h0l : ∀ y z, ω 0 y z = 0) (h0m : ∀ x z, ω x 0 z = 0) (h0r : ∀ x y, ω x y 0 = 0)

include hH1 h0l h0m in
theorem c_zero_right (x : ZMod 3) : c x 0 = 0 := by
  have h := hH1 x 0 0
  simp only [add_zero, h0l, h0m, zero_add] at h
  simpa using h

include hH2 h0l h0m in
theorem c_zero_left (y : ZMod 3) : c 0 y = 0 := by
  have h := hH2 0 0 y
  simp only [add_zero, h0l, h0m, neg_zero, zero_add] at h
  simpa using h

include hH1 h0l h0m in
/-- The class of `ω` is the cube of the twist (additively: `ω(1,1,1) + ω(1,2,1) = 3 c(1,1)`). -/
theorem invariant_eq_add : ω 1 1 1 + ω 1 2 1 = c 1 1 + c 1 1 + c 1 1 := by
  have hc10 := c_zero_right ω c hH1 h0l h0m 1
  have q111 : ω 1 1 1 + c 1 2 + ω 1 1 1 = c 1 1 + ω 1 1 1 + c 1 1 := by
    have h := hH1 1 1 1
    simp only [t11] at h
    linear_combination (norm := abel) h
  have q112 : ω 1 1 2 + ω 1 2 1 = c 1 1 + ω 1 1 2 + c 1 2 := by
    have h := hH1 1 1 2
    simp only [t12, hc10, add_zero] at h
    linear_combination (norm := abel) h
  linear_combination (norm := abel) q111 + q112

variable (hc : ∀ x, c x x = 0)

/-- The explicit trivializing cochain: `f(1,2) = a`, `f(2,1) = b`, `0` elsewhere. -/
def fZ3 (a b : M) (x y : ZMod 3) : M :=
  if x = 1 ∧ y = 2 then a else if x = 2 ∧ y = 1 then b else 0

theorem fZ3_zero_left (a b : M) (y : ZMod 3) : fZ3 a b 0 y = 0 := by
  unfold fZ3
  rw [if_neg (fun h => absurd h.1 (by decide)), if_neg (fun h => absurd h.1 (by decide))]

theorem fZ3_zero_right (a b : M) (x : ZMod 3) : fZ3 a b x 0 = 0 := by
  unfold fZ3
  rw [if_neg (fun h => absurd h.2 (by decide)), if_neg (fun h => absurd h.2 (by decide))]

theorem fZ3_11 (a b : M) : fZ3 a b 1 1 = 0 := by
  unfold fZ3
  rw [if_neg (fun h => absurd h.2 (by decide)), if_neg (fun h => absurd h.1 (by decide))]

theorem fZ3_22 (a b : M) : fZ3 a b 2 2 = 0 := by
  unfold fZ3
  rw [if_neg (fun h => absurd h.1 (by decide)), if_neg (fun h => absurd h.2 (by decide))]

theorem fZ3_12 (a b : M) : fZ3 a b 1 2 = a := by
  unfold fZ3
  rw [if_pos ⟨rfl, rfl⟩]

theorem fZ3_21 (a b : M) : fZ3 a b 2 1 = b := by
  unfold fZ3
  rw [if_neg (fun h => absurd h.1 (by decide)), if_pos ⟨rfl, rfl⟩]

include hP hH1 hH2 h0l h0m h0r hc in
/-- **Trivial twists force the trivial class** (additive form): `(ω, c)` is the coboundary of
`fZ3 (ω 1 1 2) (ω 2 2 1)`. -/
theorem isTrivial_add :
    (∀ x y z, fZ3 (ω 1 1 2) (ω 2 2 1) y z + fZ3 (ω 1 1 2) (ω 2 2 1) x (y + z) =
      ω x y z + fZ3 (ω 1 1 2) (ω 2 2 1) x y + fZ3 (ω 1 1 2) (ω 2 2 1) (x + y) z) ∧
    (∀ x y, fZ3 (ω 1 1 2) (ω 2 2 1) y x = c x y + fZ3 (ω 1 1 2) (ω 2 2 1) x y) := by
  have hc10 := c_zero_right ω c hH1 h0l h0m
  have hc01 := c_zero_left ω c hH2 h0l h0m
  have hc11 := hc 1
  have hc22 := hc 2
  -- pentagon instances
  have p3 : ω 1 1 2 + ω 1 2 1 = ω 2 2 1 := by
    have h := hP 1 1 2 1
    simp only [t11, t12, t21, t22, h0l, h0m, h0r, add_zero, zero_add] at h
    linear_combination (norm := abel) h
  have p6 : ω 1 2 1 + ω 2 1 2 = 0 := by
    have h := hP 1 2 1 2
    simp only [t11, t12, t21, t22, h0l, h0m, h0r, add_zero, zero_add] at h
    linear_combination (norm := abel) h
  have p7 : ω 1 2 2 + ω 1 1 1 + ω 2 2 1 = 0 := by
    have h := hP 1 2 2 1
    simp only [t11, t12, t21, t22, h0l, h0m, h0r, add_zero, zero_add] at h
    linear_combination (norm := abel) h
  have p5 : ω 1 2 1 + ω 2 1 1 = ω 1 2 2 := by
    have h := hP 1 2 1 1
    simp only [t11, t12, t21, t22, h0l, h0m, h0r, add_zero, zero_add] at h
    linear_combination (norm := abel) h
  have p4 : ω 1 1 2 + ω 1 2 2 = ω 2 2 2 + ω 1 1 1 := by
    have h := hP 1 1 2 2
    simp only [t11, t12, t21, t22, h0l, h0m, h0r, add_zero, zero_add] at h
    linear_combination (norm := abel) h
  -- hexagon instances
  have q111 : ω 1 1 1 + c 1 2 + ω 1 1 1 = c 1 1 + ω 1 1 1 + c 1 1 := by
    have h := hH1 1 1 1
    simp only [t11] at h
    linear_combination (norm := abel) h
  have q112 : ω 1 1 2 + ω 1 2 1 = c 1 1 + ω 1 1 2 + c 1 2 := by
    have h := hH1 1 1 2
    simp only [t12, hc10, add_zero] at h
    linear_combination (norm := abel) h
  have q222 : ω 2 2 2 + c 2 1 + ω 2 2 2 = c 2 2 + ω 2 2 2 + c 2 2 := by
    have h := hH1 2 2 2
    simp only [t22] at h
    linear_combination (norm := abel) h
  -- closed forms, `A = ω 1 1 2`, `B = ω 2 2 1`
  have e121 : ω 1 2 1 = ω 2 2 1 - ω 1 1 2 := by linear_combination (norm := abel) p3
  have e212 : ω 2 1 2 = ω 1 1 2 - ω 2 2 1 := by linear_combination (norm := abel) p6 - e121
  have ec12 : c 1 2 = ω 2 2 1 - ω 1 1 2 := by
    linear_combination (norm := abel) e121 - q112 - hc11
  have e111 : ω 1 1 1 = ω 1 1 2 - ω 2 2 1 := by
    linear_combination (norm := abel) q111 - ec12 + hc11 + hc11
  have e122 : ω 1 2 2 = -ω 1 1 2 := by linear_combination (norm := abel) p7 - e111
  have e211 : ω 2 1 1 = -ω 2 2 1 := by linear_combination (norm := abel) p5 + e122 - e121
  have e222 : ω 2 2 2 = ω 2 2 1 - ω 1 1 2 := by
    linear_combination (norm := abel) e122 - e111 - p4
  have ec21 : c 2 1 = ω 1 1 2 - ω 2 2 1 := by
    linear_combination (norm := abel) q222 - e222 + hc22 + hc22
  refine ⟨fun x y z => ?_, fun x y => ?_⟩
  · rcases cases3 x with rfl | rfl | rfl <;> rcases cases3 y with rfl | rfl | rfl <;>
      rcases cases3 z with rfl | rfl | rfl <;>
      simp only [t11, t12, t21, t22, add_zero, zero_add, h0l, h0m, h0r, fZ3_zero_left,
        fZ3_zero_right, fZ3_11, fZ3_22, fZ3_12, fZ3_21, e111, e121, e122, e211, e212,
        e222] <;> abel
  · rcases cases3 x with rfl | rfl | rfl <;> rcases cases3 y with rfl | rfl | rfl <;>
      simp only [hc10, hc01, hc11, hc22, ec12, ec21, fZ3_zero_left, fZ3_zero_right, fZ3_11,
        fZ3_22, fZ3_12, fZ3_21, add_zero, zero_add] <;> abel

end Additive

end AbelianCocycleZ3

open AbelianCocycleZ3

/-- An abelian 3-cocycle on an additive group `A` with values in a commutative group `G`
(e.g. `G = 𝕜ˣ`): the associator `ω` and braiding `c` of a skeletal pointed braided category
with simple objects `A` (normalized). -/
structure AbelianCocycle (A G : Type*) [AddCommGroup A] [CommGroup G] where
  /-- The associator. -/
  ω : A → A → A → G
  /-- The braiding. -/
  c : A → A → G
  pentagon : ∀ w x y z, ω w x y * ω w (x + y) z * ω x y z = ω (w + x) y z * ω w x (y + z)
  hexagon₁ : ∀ x y z, ω x y z * c x (y + z) * ω y z x = c x y * ω y x z * c x z
  hexagon₂ : ∀ x y z, (ω x y z)⁻¹ * c (x + y) z * (ω z x y)⁻¹ = c y z * (ω x z y)⁻¹ * c x z
  ω_zero_left : ∀ y z, ω 0 y z = 1
  ω_zero_mid : ∀ x z, ω x 0 z = 1
  ω_zero_right : ∀ x y, ω x y 0 = 1

namespace AbelianCocycle

variable {A G : Type*} [AddCommGroup A] [CommGroup G]

/-- Abelian cohomology: `Z' = Z · ∂f` (the identity functor with tensorator `f` is a braided
monoidal equivalence between the two skeletal braided categories). -/
def Cohomologous (Z Z' : AbelianCocycle A G) : Prop :=
  ∃ f : A → A → G, (∀ x y z, Z'.ω x y z * f y z * f x (y + z) = Z.ω x y z * f x y * f (x + y) z) ∧
    ∀ x y, Z'.c x y * f y x = Z.c x y * f x y

/-- `(ω, c)` is cohomologous to the trivial pair `(1, 1)`, by a normalized `f`
(`f(0,y) = f(x,0) = 1`, so that the identity functor with tensorator `f` and identity unit
morphism is a braided monoidal equivalence `(Vec_A, ω, c) ≃ (Vec_A, 1, 1)`). -/
def IsTrivial (Z : AbelianCocycle A G) : Prop :=
  ∃ f : A → A → G, (∀ x y z, f y z * f x (y + z) = Z.ω x y z * f x y * f (x + y) z) ∧
    (∀ x y, f y x = Z.c x y * f x y) ∧ (∀ y, f 0 y = 1) ∧ ∀ x, f x 0 = 1

/-- The twist `θ_x = c(x,x)` is a cohomology invariant. -/
theorem trace_eq_of_cohomologous {Z Z' : AbelianCocycle A G} (h : Z.Cohomologous Z') (x : A) :
    Z'.c x x = Z.c x x := by
  obtain ⟨f, -, hc⟩ := h
  exact mul_right_cancel (hc x x)

/-- A trivial abelian cocycle has trivial twists. -/
theorem trace_eq_one_of_isTrivial {Z : AbelianCocycle A G} (h : Z.IsTrivial) (x : A) :
    Z.c x x = 1 := by
  obtain ⟨f, -, hc, -⟩ := h
  exact mul_right_cancel (b := f x x) (by rw [one_mul]; exact (hc x x).symm)

/-- The additive form of an abelian cocycle (values in `Additive G`). -/
theorem toAdditive (Z : AbelianCocycle (ZMod 3) G) :
    (∀ w x y z, Additive.ofMul (Z.ω w x y) + Additive.ofMul (Z.ω w (x + y) z) +
      Additive.ofMul (Z.ω x y z) =
        Additive.ofMul (Z.ω (w + x) y z) + Additive.ofMul (Z.ω w x (y + z))) ∧
    (∀ x y z, Additive.ofMul (Z.ω x y z) + Additive.ofMul (Z.c x (y + z)) +
      Additive.ofMul (Z.ω y z x) =
        Additive.ofMul (Z.c x y) + Additive.ofMul (Z.ω y x z) + Additive.ofMul (Z.c x z)) ∧
    (∀ x y z, -Additive.ofMul (Z.ω x y z) + Additive.ofMul (Z.c (x + y) z) +
      -Additive.ofMul (Z.ω z x y) =
        Additive.ofMul (Z.c y z) + -Additive.ofMul (Z.ω x z y) + Additive.ofMul (Z.c x z)) ∧
    (∀ y z, Additive.ofMul (Z.ω 0 y z) = 0) ∧ (∀ x z, Additive.ofMul (Z.ω x 0 z) = 0) ∧
    (∀ x y, Additive.ofMul (Z.ω x y 0) = 0) := by
  refine ⟨fun w x y z => ?_, fun x y z => ?_, fun x y z => ?_, fun y z => ?_, fun x z => ?_,
    fun x y => ?_⟩
  · have := congrArg Additive.ofMul (Z.pentagon w x y z)
    simpa only [ofMul_mul] using this
  · have := congrArg Additive.ofMul (Z.hexagon₁ x y z)
    simpa only [ofMul_mul] using this
  · have := congrArg Additive.ofMul (Z.hexagon₂ x y z)
    simpa only [ofMul_mul, ofMul_inv] using this
  · rw [Z.ω_zero_left]
    rfl
  · rw [Z.ω_zero_mid]
    rfl
  · rw [Z.ω_zero_right]
    rfl

/-- **The class of `ω` is the cube of the twist**: `ω(1,1,1) ω(1,2,1) = c(1,1)³` on `ℤ/3`. -/
theorem invariant_eq (Z : AbelianCocycle (ZMod 3) G) :
    Z.ω 1 1 1 * Z.ω 1 2 1 = Z.c 1 1 * Z.c 1 1 * Z.c 1 1 := by
  obtain ⟨-, hH1, -, h0l, h0m, -⟩ := Z.toAdditive
  have := invariant_eq_add (fun x y z => Additive.ofMul (Z.ω x y z))
    (fun x y => Additive.ofMul (Z.c x y)) hH1 h0l h0m
  apply Additive.ofMul.injective
  simpa only [ofMul_mul] using this

/-- **Trivial twists force the trivial class** (the Tannakian step at the cocycle level): an
abelian 3-cocycle on `ℤ/3` with `c(x,x) = 1` for all `x` is cohomologous to `(1, 1)`. -/
theorem isTrivial_of_trace_eq_one (Z : AbelianCocycle (ZMod 3) G) (hc : ∀ x, Z.c x x = 1) :
    Z.IsTrivial := by
  obtain ⟨hP, hH1, hH2, h0l, h0m, h0r⟩ := Z.toAdditive
  have hc' : ∀ x, Additive.ofMul (Z.c x x) = 0 := fun x => by rw [hc x]; rfl
  obtain ⟨h1, h2⟩ := isTrivial_add (fun x y z => Additive.ofMul (Z.ω x y z))
    (fun x y => Additive.ofMul (Z.c x y)) hP hH1 hH2 h0l h0m h0r hc'
  refine ⟨fun x y => Additive.toMul
    (fZ3 (Additive.ofMul (Z.ω 1 1 2)) (Additive.ofMul (Z.ω 2 2 1)) x y), fun x y z => ?_,
    fun x y => ?_, fun y => ?_, fun x => ?_⟩
  · apply Additive.ofMul.injective
    simpa only [ofMul_mul, ofMul_toMul] using h1 x y z
  · apply Additive.ofMul.injective
    simpa only [ofMul_mul, ofMul_toMul] using h2 x y
  · simp only [fZ3_zero_left]
    rfl
  · simp only [fZ3_zero_right]
    rfl

/-- On `ℤ/3`, an abelian 3-cocycle is cohomologous to `(1, 1)` iff all its twists are trivial. -/
theorem isTrivial_iff (Z : AbelianCocycle (ZMod 3) G) : Z.IsTrivial ↔ ∀ x, Z.c x x = 1 :=
  ⟨trace_eq_one_of_isTrivial, isTrivial_of_trace_eq_one Z⟩

end AbelianCocycle

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.AbelianCocycleZ3.isTrivial_add
#print axioms HaagerupIzumi.C8.AbelianCocycle.trace_eq_of_cohomologous
#print axioms HaagerupIzumi.C8.AbelianCocycle.invariant_eq
#print axioms HaagerupIzumi.C8.AbelianCocycle.isTrivial_of_trace_eq_one
#print axioms HaagerupIzumi.C8.AbelianCocycle.isTrivial_iff
