module

public import HaagerupIzumi.C8.ProofMap
public import HaagerupIzumi.C8.CoreTops

@[expose] public section

/-!
# The universal top bound arrow of the proof map, made concrete

`ProofMap.L_topBound : certStructural → stronglyRational → pf13Factor → positiveStress →
initialGrades → topBound` is eq:sharp-top-bound (lines 3044–3198 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): every simple `U`-module has `0 ≤ h ≤ 17/10`.

The concrete objects (`TopData`): an index type `S` of the simple `U`-modules, their lowest
weights `hw M`, and the multiplicities `x M a`, `y M a` of the fourteen tops `x_a = (1, a)`,
`y_a = (τ, a)` of the core `A_L = ⊕ 𝒯_{1,j} ⊗ PF_{0,-5j}` in the lowest space of `M`.
`topBoundNodes R T` overrides the node `topBound` of `R : Nodes` by
`∀ M, 0 ≤ hw M ∧ hw M ≤ 17/10`; `topBound_arrow` proves `L_topBound` for it through
`CoreTops.lowest_weight_le_of_trace` (hence `CoreTops.universal_top_bound` and
`CFT.core_top_bound`), with `0 ≤ h` from the nonnegativity of the fourteen trace contributions.

If `S` were empty the node would be vacuous; the combined file `ProofMapConcrete` takes `S` to be
the type `Characters.Label` of the twelve simple `U`-modules and `hw` to be their actual lowest
weights `CharacterData.hw`, shared with the character branch.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.CoreTops

/-- The concrete data of the top bound. -/
structure TopData (S : Type*) where
  /-- The lowest weight of the simple `U`-module `M`. -/
  hw : S → ℚ
  /-- The multiplicity of the core top `x_a = (1, a)` in the lowest space of `M`. -/
  x : S → ℕ → ℕ
  /-- The multiplicity of the core top `y_a = (τ, a)` in the lowest space of `M`. -/
  y : S → ℕ → ℕ

variable {S : Type*}

/-- The proof map with `topBound` made concrete. -/
def topBoundNodes (R : Nodes) (T : TopData S) : Nodes :=
  { R with topBound := ∀ M, 0 ≤ T.hw M ∧ T.hw M ≤ 17 / 10 }

/-- The fourteen trace contributions `W` of eq:top-W are nonnegative (table at lines 3153–3162). -/
theorem topW_nonneg : ∀ a ∈ List.range 7, 0 ≤ topW false a ∧ 0 ≤ topW true a := by
  decide +kernel

/-- The remaining inputs of `L_topBound`, tagged, each stated conditionally on the premise nodes
of `R` from which the manuscript draws it. -/
structure TopBoundInputs (R : Nodes) (T : TopData S) : Prop where
  /-- [manuscript step] Lemma `lem:compatible-top` (line 2890) makes the lowest space of every
  simple `M` a complete sum of `A_L` tops, which (with the ALY top formulas) is a
  finite-dimensional right `𝔰𝔩₂`-representation, so its charge multiplicities decrease away from
  `0`; the core extension `A_L ⊂ U` is [certificate] data (`certStructural`, lines 3048–3079) and
  its parafermion part is the factor of `pf13Factor`. -/
  mono : R.certStructural → R.pf13Factor →
    ∀ M (c : ℤ), 0 ≤ c → nMult (T.x M) (T.y M) (c + 2) ≤ nMult (T.x M) (T.y M) c
  /-- [manuscript step] eq:top-trace (line 2949): tracing the positive stress identity
  (`positiveStress`) over the lowest space gives `W_total = h · D`, with the fourteen traces of
  eq:top-W. -/
  trace : R.positiveStress → R.certStructural → ∀ M, ∑ a ∈ Finset.range 7,
      ((T.x M a : ℚ) * topW false a + (T.y M a : ℚ) * topW true a) =
    T.hw M * ∑ a ∈ Finset.range 7,
      ((T.x M a : ℚ) * dimOf false a + (T.y M a : ℚ) * dimOf true a)
  /-- [definitional] the lowest space of a simple module is nonzero. -/
  pos : ∀ M, 0 < ∑ a ∈ Finset.range 7,
      ((T.x M a : ℚ) * dimOf false a + (T.y M a : ℚ) * dimOf true a)

/-- **`L_topBound`** (eq:sharp-top-bound).

* Concrete node: `topBound`.  The premises `certStructural`, `pf13Factor`, `positiveStress` (opaque
  in this file) are the ones the inputs are applied to; `stronglyRational`, `initialGrades` are
  not used.
* Concrete theorem: `CoreTops.lowest_weight_le_of_trace` (the charge minimizations, the dimensions
  and traces of the fourteen tops, the `𝔰𝔩₂` inequalities `y₂ ≥ x₅`, `y₄ ≥ x₅ + x₆`, and the
  nonnegative identity eq:sharp-top-bound), and `topW_nonneg` for `h ≥ 0`.
* Remaining inputs: the fields of `TopBoundInputs` (tagged there). -/
theorem topBound_arrow (R : Nodes) (T : TopData S) (I : TopBoundInputs R T) :
    (topBoundNodes R T).certStructural → (topBoundNodes R T).stronglyRational →
      (topBoundNodes R T).pf13Factor → (topBoundNodes R T).positiveStress →
      (topBoundNodes R T).initialGrades → (topBoundNodes R T).topBound := by
  intro hcs _ hpf hps _ M
  have hmono := I.mono hcs hpf
  have htrace := I.trace hps hcs
  have hD := I.pos
  refine ⟨?_, lowest_weight_le_of_trace (T.x M) (T.y M) (hmono M) (T.hw M) (htrace M) (hD M)⟩
  have hW : 0 ≤ ∑ a ∈ Finset.range 7,
      ((T.x M a : ℚ) * topW false a + (T.y M a : ℚ) * topW true a) :=
    Finset.sum_nonneg fun a ha => by
      obtain ⟨h1, h2⟩ := topW_nonneg a (List.mem_range.mpr (Finset.mem_range.mp ha))
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) h1) (mul_nonneg (Nat.cast_nonneg _) h2)
  by_contra hneg
  push Not at hneg
  have hprod := mul_neg_of_neg_of_pos hneg (hD M)
  linarith [htrace M]

#print axioms topW_nonneg
#print axioms topBound_arrow

end HaagerupIzumi.C8.ProofMap
