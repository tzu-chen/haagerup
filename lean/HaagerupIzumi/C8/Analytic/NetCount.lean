module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-! # Exact steps in the net sector count (Proposition `clm:analytic-net-count`, A2)

Exact arguments from the proof of Proposition `clm:analytic-net-count`
(`haagerup_c8_expanded.tex`, lines 4291–4428).

* `eq_scalar_of_commute_of_separating` (irreducibility of the inclusion, lines
  4323–4333): an element `x` of an operator algebra `𝒩` for which the vacuum `Ω` is
  separating, commuting with operators (the rotations) whose common fixed vectors are the
  multiples of `Ω`, is a scalar: `x Ω` is fixed, hence `x Ω = c Ω`, and `x - c` kills `Ω`.
  Hypotheses: the separating property of the vacuum for `𝒩_H(I)` (Reeh–Schlieder), the
  one-dimensional zero-energy space of `H`, and the commutation of `x` with the rotations
  (locality and strong additivity of `𝒩_U`, external net facts).
* `card_eq_three_or_six` (lines 4358–4362): if `ℤ/3` embeds in the group of invertible
  objects, which has at most six elements (rank six), its order is three or six
  (Lagrange).  Hypotheses: the automorphism–invertible-object injection of Lemma
  `lem:automorphisms-invertibles` and the rank six of `𝓕_net`.
* The discriminant computation (lines 4383–4400): on `ℤ/3 × ℤ/3` with
  `q(a,b) = (2a² + b²)/3 mod ℤ`, the lines `L₊ = {(a,a)}` and `L₋ = {(a,-a)}` are isotropic
  (`Lplus_isotropic`, `Lminus_isotropic`), transverse (`Lplus_inter_Lminus`), and for
  `t, t' ∈ L₋` one has `t ∈ t' + L₊` only when `t = t'` (`Lminus_coset_Lplus`), which is
  the support computation behind `Hom(t, t' ⊗ Q₊) = ℂ` or `0`.  Kernel `decide`.
  The categorical statements are formalized in `Category/`: free-module induction as a (monoidal)
  equivalence (`RightMod.freeLminus_monoidalEquivalence_of_separable`), the count `9/3 = 3` of simple
  `Q₊`-modules (`RightMod.netCount_simple_modules`, `Category/SimpleModulesLminus`), and the
  identification with the untwisted `Vec_{ℤ/3}` (`untwisted_vec_equivalence_of_separable`), given the
  pointed structure of the ambient category and the self-braiding input `hθ`.
-/

namespace HaagerupIzumi.C8

section Irreducible

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Irreducibility step** (proof of Prop. `clm:analytic-net-count`, lines 4323–4333).
Let `𝒩` be an algebra of operators for which `Ω` is separating (`y ∈ 𝒩`, `y Ω = 0` imply
`y = 0`), and `R` a set of operators fixing `Ω` whose common fixed vectors are the
multiples of `Ω`.  Every `x ∈ 𝒩` commuting with `R` is a scalar. -/
theorem eq_scalar_of_commute_of_separating (𝒩 : Subalgebra K (Module.End K V)) (Ω : V)
    (R : Set (Module.End K V)) (hRΩ : ∀ r ∈ R, r Ω = Ω)
    (hfix : ∀ w : V, (∀ r ∈ R, r w = w) → ∃ c : K, w = c • Ω)
    (hsep : ∀ y ∈ 𝒩, y Ω = 0 → y = 0)
    {x : Module.End K V} (hx : x ∈ 𝒩) (hxR : ∀ r ∈ R, r * x = x * r) :
    ∃ c : K, x = algebraMap K (Module.End K V) c := by
  obtain ⟨c, hc⟩ := hfix (x Ω) fun r hr => by
    rw [← Module.End.mul_apply, hxR r hr, Module.End.mul_apply, hRΩ r hr]
  refine ⟨c, sub_eq_zero.1 (hsep _ (sub_mem hx (𝒩.algebraMap_mem c)) ?_)⟩
  rw [LinearMap.sub_apply, Module.algebraMap_end_apply, hc, sub_self]

end Irreducible

section InvertibleCount

/-- **Order of the invertibles** (lines 4358–4362).  If `ℤ/3` embeds in a finite group `G`
with at most six elements, then `|G| = 3` or `|G| = 6`. -/
theorem card_eq_three_or_six {G : Type*} [Group G] [Finite G]
    (f : Multiplicative (ZMod 3) →* G) (hf : Function.Injective f) (hle : Nat.card G ≤ 6) :
    Nat.card G = 3 ∨ Nat.card G = 6 := by
  have h3 : Nat.card f.range = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
  have hdvd := Subgroup.card_subgroup_dvd_card f.range
  rw [h3] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card G := Nat.card_pos
  omega

end InvertibleCount

section Discriminant

/-- The discriminant form `q(a,b) = (2a² + b²)/3 mod ℤ` of `𝒩_B`, recorded by its numerator
in `ℤ/3`. -/
def discQ (x : ZMod 3 × ZMod 3) : ZMod 3 := 2 * x.1 ^ 2 + x.2 ^ 2

/-- The extension line `L₊ = {(a,a)}` of `H/B` is isotropic. -/
theorem Lplus_isotropic : ∀ a : ZMod 3, discQ (a, a) = 0 := by decide

/-- The transverse line `L₋ = {(a,-a)}` is isotropic. -/
theorem Lminus_isotropic : ∀ a : ZMod 3, discQ (a, -a) = 0 := by decide

/-- Transversality `L₊ ∩ L₋ = {0}`. -/
theorem Lplus_inter_Lminus : ∀ a b : ZMod 3, ((a, a) : ZMod 3 × ZMod 3) = (b, -b) → a = 0 := by
  decide

/-- Support computation behind `Hom(t, t' ⊗ Q₊) = ℂ` or `0` (lines 4392–4399): for
`t = (a,-a)`, `t' = (b,-b)` in `L₋`, `t ∈ t' + L₊` forces `t = t'`. -/
theorem Lminus_coset_Lplus :
    ∀ a b c : ZMod 3, ((a, -a) : ZMod 3 × ZMod 3) = (b, -b) + (c, c) → a = b := by
  decide

end Discriminant

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.eq_scalar_of_commute_of_separating
#print axioms HaagerupIzumi.C8.card_eq_three_or_six
#print axioms HaagerupIzumi.C8.Lplus_isotropic
#print axioms HaagerupIzumi.C8.Lminus_isotropic
#print axioms HaagerupIzumi.C8.Lplus_inter_Lminus
#print axioms HaagerupIzumi.C8.Lminus_coset_Lplus
