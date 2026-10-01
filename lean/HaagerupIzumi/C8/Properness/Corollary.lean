module

public import HaagerupIzumi.C8.Properness.Final
public import HaagerupIzumi.C8.VertexAlgebra.Recursive

@[expose] public section

/-! # Strong generation and `weight one = K` from the finite gates

Combines `closure_hypothesis_one`, `closure_hypothesis_two` (this directory) with
`HaagerupIzumi.C8.VertexAlgebra.recursive_strong_generation` (Theorem `thm:recursive`,
`C8/VertexAlgebra/Recursive.lean`) for `S 1 = K`, `S 2 = S₂`, `S 3 = S₃`, `S 4 = P₄`, `h = 4`
(manuscript, Section `sec:properness`, lines 2592–2597): the differential normal span of the
four spaces is a vertex subalgebra, equal to the vertex algebra they generate, whose weight-one
part is `K`.

The identification of this generated algebra with `U` (it contains `K, u, ω_B`, and the
minimal-generator record shows that `K, u, ω_B` generate `S₂`) is not formalized here.
-/

namespace HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

/-- The finite-gate part of Proposition `prop:mainproper`: from the exact certificates and
the nilpotence of raising/lowering words, `K, S₂, S₃, P₄` strongly generate the vertex algebra
they generate, and its weight-one space is `K`. -/
theorem strong_generation_of_certificates (D : ClosureData A) (L : LowerCertificate D)
    (G : Gate4Certificate D) (G5 : Gate5Certificate D G)
    (hnilE : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.eL) (A.mode 0 D.eR) w v = 0)
    (hnilF : ∀ w : List Bool, w.length = 25 → ∀ v ∈ D.S₃,
      CFT.raisingWord (A.mode 0 D.fL) (A.mode 0 D.fR) w v = 0) :
    A.IsSubalgebra (A.normalSpan (⋃ d, (D.family d : Set V))) ∧
      A.generated (⋃ d, (D.family d : Set V)) = A.normalSpan (⋃ d, (D.family d : Set V)) ∧
      A.generated (⋃ d, (D.family d : Set V)) ⊓ A.grade 1 = D.K :=
  A.toVertexAlgebra.recursive_strong_generation D.family 4 D.family_grade D.family_top
    (closure_hypothesis_one D L G G5 hnilE hnilF) (closure_hypothesis_two D L)

#print axioms strong_generation_of_certificates

end HaagerupIzumi.C8
