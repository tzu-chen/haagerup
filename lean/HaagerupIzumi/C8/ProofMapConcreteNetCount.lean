module

public import HaagerupIzumi.C8.ProofMapConcreteBranching
public import HaagerupIzumi.C8.ProofMapConcreteBoundary

@[expose] public section

/-!
# The net sector count arrow of the proof map, made concrete

Proposition `clm:analytic-net-count` (A2, lines 4291–4428 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) is the arrow

* `L_netCount : netCompletelyRational → branchH → noSignExtension → rankSixRing →
  certDiscriminant → netCount`.

Its proof re-runs the rank-six ring and indicator argument of Appendix G for the boundary fusion
category `𝓕_net` of the net inclusion `𝒩_U ⊂ 𝒩_H` (lines 4410–4428).  The concrete objects are a
second `BoundaryData` `Bn` (fusion ring `K₀(𝓕_net)`, its dimensions, the invertible `a` attached to
the lattice automorphism of `H/B`, and the center data of `Z(𝓕_net)`), and the type `Sec` of
irreducible `𝒩_U` sectors.  `netNodes R Bn` overrides `netCount` of `R : Nodes` by `NetHI Bn`:

* `K₀(𝓕_net)` is `HI(ℤ/3)` (eq:rank6-ring with `m = 1`), `d_ρ = (3+√13)/2`, the `C`-twists are
  `1, ζ₃, ζ₃²` and the six residual central simples have the six nonresidue thirteenth roots as
  twists (the center data of line 4421);
* the invertible simples are exactly `𝟙, a, a*`, and the pointed part is untwisted (`ν₃(a) = 1`;
  this conjunct is an input, `NetInputs.untwisted`).

`ProofMapConcreteUnitarity.unitarityNodes`, applied on top, adds `#Sec = 12`; `netCount_arrow`
proves both.

Concrete argument: the Bischoff–Jones expansion of the lattice automorphism gives `ℤ/3 ↪ Inv`
(`autInvertible_arrow`); a further invertible would make `𝓕_net` pointed
(`dims_eq_one_of_extra_invertible`), which the index-two argument turns into an automorphism `g`
with `B^g = U`, excluded by the concrete
node `noSignExtension`; then `rankSixRing_arrow`, `rankSixMoments_arrow`,
`multiplicityOne_arrow`, `twelveTwists_arrow` (all proved for an arbitrary `BoundaryData`) give the
`HI(ℤ/3)` ring with its twelve-simple center, and `#Sec = 6 + #κ = 12`.  Remaining inputs
(`NetInputs`) are tagged in the field docstrings.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Fusion

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}
variable {ιn κn : Type*} [Fintype ιn] [DecidableEq ιn] [Fintype κn]

/-- The concrete `netCount` node for the net boundary data `Bn`.  The last conjunct `ν₃(a) = 1`
(untwisted pointed part of `𝓕_net`) is **not derived**: it is supplied by the input
`NetInputs.untwisted`, conditional on the proved free-induction equivalence for `H/B`. -/
def NetHI (Bn : BoundaryData ιn κn) : Prop :=
  (∃ ρ ρ₁ ρ₂, IsHIRing Bn.F Bn.a ρ ρ₁ ρ₂ 1 ∧ Bn.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 Bn ∧
    SixResidualTwists Bn) ∧
  (Z3Generator Bn.F Bn.a ∧
    ∀ x, Bn.F.IsInvertible x → x = Bn.F.unit ∨ x = Bn.a ∨ x = Bn.F.dual Bn.a) ∧
  Bn.ν₃ = 1

/-- The proof map with `netCount` made concrete. -/
def netNodes (R : Nodes) (Bn : BoundaryData ιn κn) : Nodes :=
  { R with netCount := NetHI Bn }

/-- The remaining inputs of `L_netCount`, tagged; `cr`, `disc` are the opaque nodes
`netCompletelyRational`, `certDiscriminant`, `algRing` is the concrete algebraic `rankSixRing`,
and `tann` is the free-induction equivalence for `H/B` on the isotropic line `L₋`
(`UntwistedNode`, proved from `UntwistedInputs` in `ProofMapConcrete`). -/
structure NetInputs (D : ClosureData A) (u : V) (Sg : SignData A) (Bn : BoundaryData ιn κn)
    (Sec : Type*) [Fintype Sec] (cr disc algRing tann : Prop) where
  /-- [external] `𝓕_net` is a `C*` fusion category (positive dimensions, `d_{x*} = d_x`), the
  inclusion has finite index (Kawahigashi–Longo Proposition 2.3, line 4334), and the
  extension-dimension identities of its Lagrangian algebra `A_net` (`Dim 𝓕_net = 3s`,
  `d_X = s - 1`; lines 4334–4345, as for `𝓕`, lines 3250–3260). -/
  dims : cr → PositiveDims Bn.F Bn.d ∧ ∑ i, Bn.d i ^ 2 = 3 * Bn.s ∧ Bn.dX = Bn.s - 1
  /-- [manuscript step] lines 4307–4322 (graph reduction: the algebraic decomposition of `H`, with
  multiplicities `1, 1, 2` at rank six, is the net decomposition) and [external] center induction
  (`rank 𝓕_net = dim End(A_net)`, lines 4345–4352): `rank 𝓕_net = 6`. -/
  rank : cr → algRing → Fintype.card ιn = 6
  /-- [external] Bischoff–Jones Corollary 3.4 and [manuscript step] eq:analytic-end-algebra
  (the `End(1 ⊕ X ⊕ 2Y)` computation is `Fusion.endHIsoOfSimple`):
  `K₀(𝓕_net) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)`. -/
  iso : cr → algRing → FusionAlgebraIso Bn.F
  /-- [external] Bischoff–Jones (Lemma 3.1, Corollary 3.4) for the lattice automorphism of `H/B`
  acting on the net inclusion (lines 4355–4358), with [manuscript step] `f ∗ f = f`
  (`AutExpansion`, fields tagged there). -/
  bj : disc → ∃ x y : ιn → ℝ, AutExpansion Bn x y
  /-- [external] lines 4362–4373: if `𝓕_net` were pointed of rank six, multiplicativity of the index
  (`Branching.index_two_of_pointed`: `[𝒩_B : 𝒩_U] = 2`), [manuscript step] the structure of
  index-two local extensions (lines 4366–4370), CKLW Theorem 6.9, Proposition 7.6 and Theorem 7.5
  give a finite-order automorphism `g` of `B` with `B^g = U`. -/
  pointed : cr → Fintype.card ιn = 6 → (∀ i, Bn.d i = 1) → ∃ g, FixesExactlyU D u Sg g
  /-- **The conjunct `ν₃(a) = 1` of `NetHI` is assumed here.**  Lines 4383–4406: the lattice net
  `𝒩_B` has the discriminant data of `B`; free `Q₊`-module induction from `L₋` is an equivalence
  onto all `Q₊`-modules (`tann`: proved, `Category.RightMod.freeLminus_isEquivalence`, with the
  three simple modules of `Category.RightMod.netCount_simple_modules`; [external] the lattice net's
  sector category is `Rep(B)`).  Not formalized: [manuscript step] the Tannakian identification of
  the pointed category on `L₋` with the untwisted `Vec_{ℤ/3}` as a tensor category, its tensorial
  embedding in `𝓕_net`, and [external] the Frobenius–Schur indicator `ν₃` of an untwisted pointed
  part.  The categorical model does not contain `ν₃`, so the conclusion is an input. -/
  untwisted : tann → disc → cr → Bn.ν₃ = 1
  /-- The evaluated center-induction formulas for `𝓕_net` (`InductionFormulas`, fields tagged
  there; lines 4410–4424). -/
  ind : ∀ ρ ρ₁ ρ₂ m, IsHIRing Bn.F Bn.a ρ ρ₁ ρ₂ m → InductionFormulas m (Bn.d ρ) Bn
  /-- [external] the Lagrangian-algebra theorem `Rep(𝒩_U) ≃ Z(𝓕_net)` (line 4426) and
  [manuscript step] the exhaustion of the center simples by `𝟙, X, Y, C₀, C₁, C₂, Z_j`
  (eq:analytic-center-dimensions): `#Sec = 6 + #κ`. -/
  count : cr → Fintype.card Sec = 6 + Fintype.card κn

/-- An auxiliary node structure, used only inside the proof of `netCount_arrow` to apply the
boundary-ring arrow theorems of `ProofMapConcreteBoundary` (stated for `boundaryNodes R B` with an
arbitrary `R`) to the net data `Bn`: the opaque parts of the nodes that `boundaryNodes` wraps are
set to `True`, so `boundaryNodes (netCarrier R) Bn` consists of the concrete fusion-ring statements
about `Bn` only.  It is not one of the node structures of the proof map. -/
def netCarrier (R : Nodes) : Nodes :=
  { R with
    lagrangianCenter := True
    rankFork := True
    notRankFour := True
    untwistedPointed := True
    branchH := True
    certDiscriminant := True }

/-- **`L_netCount`** (Proposition `clm:analytic-net-count`, lines 4291–4428).

* Concrete nodes: `noSignExtension` (no finite-order automorphism `g` of `B` has `B^g = U`),
  `rankSixRing` (`algRing`, applied to `rank`), `netCount` (`NetHI`, and `#Sec = 12`).
  `netCompletelyRational`, `certDiscriminant` stay opaque and are applied to the inputs; `branchH`
  enters through `rank`.
* Concrete theorems: `autInvertible_arrow`, `dims_eq_one_of_extra_invertible`,
  `rankSixRing_arrow`, `rankSixMoments_arrow`, `multiplicityOne_arrow`, `twelveTwists_arrow` of
  `ProofMapConcreteBoundary`, applied to the net data `Bn`.
* Remaining inputs: the fields of `NetInputs` (tagged there); `htann` is the proved free-induction
  equivalence (`UntwistedNode`), supplied by `ProofMapConcrete`. -/
theorem netCount_arrow (R : Nodes) (D : ClosureData A) (u : V) (Sg : SignData A)
    (Bn : BoundaryData ιn κn) (Sec : Type*) [Fintype Sec] (cr disc algRing tann : Prop)
    (I : NetInputs D u Sg Bn Sec cr disc algRing tann) (htann : tann) :
    cr → (∀ g, ¬ FixesExactlyU D u Sg g) → algRing → disc →
      NetHI Bn ∧ Fintype.card Sec = 12 := by
  intro hcr hnofix hring hdisc
  set N := boundaryNodes (netCarrier R) Bn
  have hdims := I.dims hcr
  have hlag : N.lagrangianCenter := ⟨trivial, hdims⟩
  have h6 := I.rank hcr hring
  have hZ : N.invertiblesContainZ3 :=
    autInvertible_arrow (netCarrier R) Bn (fun _ => I.bj hdisc) hlag trivial
  have h3 : N.threeInvertibles := by
    refine ⟨hZ, fun x hx => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨hxu, hxa, hxb⟩ := hne
    obtain ⟨-, hall⟩ := dims_eq_one_of_extra_invertible hZ hdims.1 (by omega) hx hxu hxa hxb
    obtain ⟨g, hg⟩ := I.pointed hcr h6 hall
    exact hnofix g hg
  have hfork : N.rankFork := ⟨trivial, Or.inr h6⟩
  have hnot4 : N.notRankFour := ⟨trivial, by omega⟩
  have hring6 := rankSixRing_arrow (netCarrier R) Bn (fun _ => I.iso hcr hring) hfork hnot4 h3
    hlag trivial
  have hmom := rankSixMoments_arrow (netCarrier R) Bn I.ind hring6
    ⟨trivial, I.untwisted htann hdisc hcr⟩ hlag
  have hm1 := multiplicityOne_arrow (netCarrier R) Bn hmom
  have htw := twelveTwists_arrow (netCarrier R) Bn hm1 hmom
  refine ⟨⟨htw, h3, I.untwisted htann hdisc hcr⟩, ?_⟩
  obtain ⟨-, -, -, -, -, -, hsix⟩ := htw
  rw [I.count hcr, hsix.card]

#print axioms netCount_arrow

end HaagerupIzumi.C8.ProofMap
