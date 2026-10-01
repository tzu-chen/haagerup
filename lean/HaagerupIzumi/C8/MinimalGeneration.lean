module

public import HaagerupIzumi.C8.MainProperness

@[expose] public section

/-!
# The minimal-generation certificate (lines 2047–2055)

"The minimal-generator record … starts with the six specified currents, `ω_B`, and `u`, then
closes their weight-two span under current zero modes and `u_1`.  Every intermediate vector is
therefore an actual `U`-vector.  The final span has dimension `120` … The equality with the saved
space `S₂` is checked only after this construction."

`closureSpace` is that construction: the smallest subspace containing `ω_B`, `u`, the affine
vacuum vectors `T k` and `k_(-1) k'` (`k, k' ∈ K`), and closed under `k_(0)` (`k ∈ K`) and `u_(1)`.
`S₂_le_U_of_closure` shows that the record's conclusion `S₂ ≤ closureSpace` gives the hypothesis
`hmin : S₂ ≤ U` of `prop_mainproper`, since `U` is a vertex subalgebra containing the
generators.
-/

namespace HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

open ClosureData

/-- The closure of the weight-two span of the generators under current zero modes and `u_(1)`. -/
def ClosureData.closureSpace (D : ClosureData A) (u : V) : Submodule k V :=
  sInf {W : Submodule k V | A.ω ∈ W ∧ u ∈ W ∧ (∀ x ∈ D.K, A.T x ∈ W) ∧
    (∀ x ∈ D.K, ∀ y ∈ D.K, A.mode (-1) x y ∈ W) ∧
    (∀ x ∈ D.K, ∀ w ∈ W, A.mode 0 x w ∈ W) ∧ (∀ w ∈ W, A.mode 1 u w ∈ W)}

/-- **Minimal generation.**  If the saved `S₂` lies in the closure computed by the
minimal-generator record, then every vector of `S₂` is an actual vector of `U = ⟨K, ω_B, u⟩`. -/
theorem S₂_le_U_of_closure (D : ClosureData A) (u : V) (hclosure : D.S₂ ≤ D.closureSpace u) :
    D.S₂ ≤ D.U u := by
  have hsub := A.toVertexAlgebra.generated_isSubalgebra (D.gens u)
  have hgen : ∀ x ∈ D.gens u, x ∈ D.U u := fun x hx => A.toVertexAlgebra.subset_generated _ hx
  have hK : ∀ x ∈ D.K, x ∈ D.U u := fun x hx =>
    (Submodule.span_le.2 fun y hy => hgen y (Or.inl hy)) hx
  have hω : A.ω ∈ D.U u := hgen _ (Or.inr (Or.inl rfl))
  have hu : u ∈ D.U u := hgen _ (Or.inr (Or.inr rfl))
  -- `T x = x_(-2) 1` lies in any subalgebra containing `x`
  have hT : ∀ x ∈ D.U u, A.T x ∈ D.U u := fun x hx => by
    rw [A.T_eq]
    exact hsub.2 (-2) x hx _ hsub.1
  refine hclosure.trans (sInf_le ⟨hω, hu, fun x hx => hT x (hK x hx),
    fun x hx y hy => hsub.2 (-1) x (hK x hx) y (hK y hy),
    fun x hx w hw => hsub.2 0 x (hK x hx) w hw, fun w hw => hsub.2 1 u hu w hw⟩)

#print axioms S₂_le_U_of_closure

end HaagerupIzumi.C8
