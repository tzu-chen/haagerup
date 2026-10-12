module

public import HaagerupIzumi.C8.ProofMap
public import HaagerupIzumi.C8.Analytic.Comparison

@[expose] public section

/-!
# The strong-unitarity arrow of the proof map, made concrete

`ProofMap.L_stronglyUnitary : reconstruction → netCount → modularData → stronglyUnitary` is the
counting step of Proposition `prop:analytic-strong-unitarity` (lines 4583–4590 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): the reconstruction functor sends the twelve
irreducible net sectors injectively (it is fully faithful) to unitary simple `U`-modules, and
there are twelve simple `U`-modules, so every simple `U`-module is unitarizable.

The concrete objects: a finite type `Sec` of (isomorphism classes of) irreducible sectors of the
net `𝒩_U`, a finite type `Smp` of isomorphism classes of simple `U`-modules, the map
`recon : Sec → Smp` induced by the reconstruction functor, and the predicate
`Unitarizable : Smp → Prop`.  `unitarityNodes` overrides:

* `reconstruction`: `R.reconstruction`, and `recon` is injective with unitarizable values (full
  faithfulness; the functor lands in `Rep^u(U)`);
* `netCount`: `R.netCount`, and there are twelve sectors;
* `stronglyUnitary`: every simple `U`-module is unitarizable.

The count of twelve simple `U`-modules (the rank of the Haagerup modular data) is not part of a
node: `stronglyUnitary_arrow` takes it as `hcard`, conditional on `modularData`; in
`ProofMapConcrete` it is a consequence of the identification of the simples with the twelve labels
(`SimpleLabels.card`).

`Unitarizable` is a predicate parameter ("admits a positive-definite invariant Hermitian form"),
not modelled, so the meaning of `stronglyUnitary` rests on its interpretation; the same predicate
appears in `reconstruction` (the reconstructed modules are unitary), which ties the two nodes
together.  The combined file `ProofMapConcrete` takes `Smp` to be the type `Simp` of simple
`U`-modules shared with the top-bound, branching and projective-vacuum branches.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8

variable {Sec Smp : Type*} [Fintype Sec] [Fintype Smp]

/-- The proof map with the nodes of the strong-unitarity step made concrete. -/
def unitarityNodes (R : Nodes) (recon : Sec → Smp) (Unitarizable : Smp → Prop) : Nodes :=
  { R with
    reconstruction := R.reconstruction ∧ Function.Injective recon ∧ ∀ s, Unitarizable (recon s)
    netCount := R.netCount ∧ Fintype.card Sec = 12
    stronglyUnitary := ∀ M, Unitarizable M }

/-- **`L_stronglyUnitary`** (Proposition `prop:analytic-strong-unitarity`, counting step).

* Concrete nodes: `reconstruction`, `netCount`, `stronglyUnitary`; `modularData` (opaque) is
  applied to `hcard`.
* Concrete theorem: `forall_of_injective_card_eq` (via `bijective_of_injective_of_card_eq`: an
  injection of twelve sectors into twelve simples is a bijection).
* Remaining input: `hcard`, there are twelve simple `U`-modules, conditional on `modularData`
  (the full faithfulness and unitarity of the reconstruction are part of the node
  `reconstruction`, the sector count part of `netCount`). -/
theorem stronglyUnitary_arrow (R : Nodes) (recon : Sec → Smp) (Unitarizable : Smp → Prop)
    (hcard : R.modularData → Fintype.card Smp = 12) :
    (unitarityNodes R recon Unitarizable).reconstruction →
      (unitarityNodes R recon Unitarizable).netCount →
      (unitarityNodes R recon Unitarizable).modularData →
      (unitarityNodes R recon Unitarizable).stronglyUnitary := by
  rintro ⟨-, hinj, hunit⟩ ⟨-, h12⟩ hmd
  exact forall_of_injective_card_eq recon hinj h12 (hcard hmd) Unitarizable hunit

#print axioms stronglyUnitary_arrow

end HaagerupIzumi.C8.ProofMap
