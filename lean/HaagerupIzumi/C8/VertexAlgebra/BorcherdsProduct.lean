module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsDongModes

@[expose] public section

/-!
# Closure under `n`-th products: reduction to the iterate family

W3, item (1) (`Lattice/W3_PLAN.md`).  With Dong's lemma (`ModeAlgebra.dong_of_good`,
`VertexAlgebra/BorcherdsDongModes.lean`) the closure of `Good` under `n`-th products of
homogeneous vectors (`ProductClosedHom`) is reduced to one statement, `IterClosed`: the
**iterate family** `p = 0` of the Borcherds identity for `(a_(n) w, b, c)`, for homogeneous `Good`
`a`, `w` and all homogeneous `b`, `c`:

`(x_(r) b)_(q) c = ∑_t (-1)^t (r choose t) (x_(r-t) b_(q+t) c - (-1)^r b_(q+r-t) x_(t) c)`,
`x = a_(n) w`.

* `productClosedHom_of_iterClosed : IterClosed → ProductClosedHom`.

`IterClosed` is the open part of item (1); see `Lattice/W3_PLAN.md` for the plan (the field-level
iterate identity for three pairwise local fields).

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-- The iterate family of the Borcherds identity for products of homogeneous `Good` vectors
(the open part of milestone item (1)). -/
def IterClosed : Prop :=
  ∀ {i m e : ℕ} {a w : V}, a ∈ M.grade i → M.Good a → w ∈ M.grade m → M.Good w → ∀ n : ℤ,
    M.mode n a w ∈ M.grade e → ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∀ q r : ℤ, M.bD e j l (M.mode n a w) b c 0 q r = 0

/-- **Closure under `n`-th products from the iterate family** (Dong's lemma supplies locality). -/
theorem productClosedHom_of_iterClosed (h : M.IterClosed) : M.ProductClosedHom := by
  intro i m a w ha hga hw hgw n
  obtain ⟨e, he⟩ := M.mode_mem_some_grade ha hw n
  exact M.good_mode_of_iter ha hga hw hgw n he (h ha hga hw hgw n he)

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.ModeAlgebra.productClosedHom_of_iterClosed
