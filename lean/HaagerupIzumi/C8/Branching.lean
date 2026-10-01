module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Finite steps of the branching argument (Appendix G, lines 3213–3387)

* `integer_weight_le` — a simple summand with integral lowest weight `h` and
  `0 ≤ h ≤ 17/10` has `h = 0` or `h = 1` (used for `B↓U = U ⊕ X`).
* `complement_currents` — `86 - 6 = 80` currents in the complement.
* `rank_fork` — `dim End(1 ⊕ X ⊕ Y ⊕ Y*) = 4` and `dim End(1 ⊕ X ⊕ 2Y) = 6`
  (eq:rank-fork), from `∑ multiplicity²`.
* `extension_dimensions` — with `d_X = s - 1`, `d_Y = s`, the extension
  `H = 1 + X + Y + Y*` has `FPdim H = 3s` and `Dim 𝓒 = (FPdim H)² = 9s²`.
* `six_invertibles_impossible` — six invertibles would give `3s = 6`, hence
  `d_X = 1`, contradicting Lemma `lem:no-sign-extension`.
* `e6_diagram_orbits`, `a2_diagram_orbits` — the diagram automorphisms of `E₆` and `A₂`
  have at least `4` and `1` orbits on simple roots; `4 + 1 = 5 > 2 = rank(𝔰𝔩₂ ⊕ 𝔰𝔩₂)`
  (the arithmetic in Lemma `lem:no-sign-extension`; the toral-fixed-point theorem
  for finite-order automorphisms, RLYG §5.2, is external).
-/

namespace HaagerupIzumi.C8.Branching

/-- A summand of a strongly rational restriction with integral lowest weight bounded by
the universal top bound `17/10` has weight `0` or `1`. -/
theorem integer_weight_le (h : ℤ) (h0 : 0 ≤ (h : ℝ)) (h1 : (h : ℝ) ≤ 17 / 10) :
    h = 0 ∨ h = 1 := by
  have a : 0 ≤ h := by exact_mod_cast h0
  have b : h < 2 := by
    have : (h : ℝ) < 2 := by linarith
    exact_mod_cast this
  omega

/-- `dim B₁ - dim U₁ = 86 - 6 = 80`: the complementary currents of `X_top`. -/
theorem complement_currents : (86 : ℕ) - 6 = 80 := rfl

/-- `B₁` of the lattice VOA `V_{E₆ ⊕ A₂}`: Cartan rank `8` plus `72 + 6` roots. -/
theorem dim_B1 : (8 : ℕ) + 72 + 6 = 86 := rfl

/-- The rank fork, eq:rank-fork: `rank 𝓕 = dim End_𝓒(H) = ∑ (multiplicity)²`. -/
theorem rank_fork :
    (1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2 : ℕ) = 4 ∧ (1 ^ 2 + 1 ^ 2 + 2 ^ 2 : ℕ) = 6 := by
  norm_num

/-- Extension dimension identities: if `d_X = s - 1` and `d_Y = d_{Y*} = s`, then
`FPdim H = 1 + d_X + 2 d_Y = 3s` and the Lagrangian identity gives `Dim 𝓒 = 9 s²`. -/
theorem extension_dimensions (s dX dY : ℝ) (hX : dX = s - 1) (hY : dY = s) :
    1 + dX + 2 * dY = 3 * s ∧ (1 + dX + 2 * dY) ^ 2 = 9 * s ^ 2 := by
  subst hX hY
  constructor <;> ring

/-- Six invertibles: `𝓕` pointed of rank six has `Dim 𝓕 = 6 = 3s`, hence `s = 2` and
`d_X = s - 1 = 1`, i.e. `X` would be invertible, contradicting `lem:no-sign-extension`. -/
theorem six_invertibles_impossible (s dX : ℝ) (hDim : 3 * s = 6) (hX : dX = s - 1)
    (hnoSign : dX ≠ 1) : False := by
  apply hnoSign
  rw [hX]
  linarith

/-- The nontrivial diagram automorphism of `E₆` (simple roots `0–1–2–3–4`, `5` attached
to `2`): it swaps `0 ↔ 4`, `1 ↔ 3` and fixes `2, 5`. -/
def e6Flip : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 4 * Equiv.swap 1 3

/-- Orbit representatives: a node is a representative if it is the smaller element of
its orbit. -/
def e6OrbitReps : Finset (Fin 6) :=
  Finset.univ.filter fun i => i ≤ e6Flip i

/-- The `E₆` diagram automorphism is a graph automorphism of the Dynkin diagram. -/
def e6Edges : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (2, 5)}

theorem e6Flip_preserves_edges :
    ∀ e ∈ e6Edges, (e6Flip e.1, e6Flip e.2) ∈ e6Edges ∨ (e6Flip e.2, e6Flip e.1) ∈ e6Edges := by
  decide

theorem e6Flip_involutive : e6Flip * e6Flip = 1 := by decide

/-- The flip has exactly four orbits on the six simple roots: `{0,4}, {1,3}, {2}, {5}`. -/
theorem e6_diagram_orbits : e6OrbitReps.card = 4 := by decide

/-- The identity has six orbits; so every diagram automorphism of `E₆` (the group is
`{1, e6Flip}` by `e6_diagram_automorphisms`) has at least four orbits. -/
theorem e6_orbits_ge_four : 4 ≤ e6OrbitReps.card ∧ 4 ≤ (Finset.univ : Finset (Fin 6)).card := by
  decide

/-- Adjacency in the `E₆` Dynkin diagram. -/
def e6Adj (i j : Fin 6) : Prop := (i, j) ∈ e6Edges ∨ (j, i) ∈ e6Edges

instance : DecidableRel e6Adj := fun i j => by unfold e6Adj; infer_instance

/-- Pruned search over the images `s₀, …, s₅` of the six nodes: an injective assignment sending
the edges `0–1, 1–2, 2–3, 3–4, 2–5` to edges is the identity or the flip. -/
theorem e6_edge_maps : ∀ s2 s1 : Fin 6, e6Adj s1 s2 → ∀ s0 : Fin 6, e6Adj s0 s1 →
    ∀ s3 : Fin 6, e6Adj s2 s3 → ∀ s4 : Fin 6, e6Adj s3 s4 → ∀ s5 : Fin 6, e6Adj s2 s5 →
    [s0, s1, s2, s3, s4, s5].Nodup →
    (∀ i, ![s0, s1, s2, s3, s4, s5] i = i) ∨ (∀ i, ![s0, s1, s2, s3, s4, s5] i = e6Flip i) := by
  decide

/-- **The diagram automorphisms of `E₆` are `1` and `e6Flip`**: a permutation of the simple
roots sending edges to edges is one of the two.  With `e6_diagram_orbits`, every diagram
automorphism of `E₆` has at least four orbits (lemma `lem:no-sign-extension`). -/
theorem e6_diagram_automorphisms (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ e ∈ e6Edges, e6Adj (σ e.1) (σ e.2)) : σ = 1 ∨ σ = e6Flip := by
  have hnd : [σ 0, σ 1, σ 2, σ 3, σ 4, σ 5].Nodup :=
    List.Nodup.map σ.injective (by decide : ([0, 1, 2, 3, 4, 5] : List (Fin 6)).Nodup)
  have hv : ∀ i, σ i = ![σ 0, σ 1, σ 2, σ 3, σ 4, σ 5] i := by
    intro i
    fin_cases i <;> rfl
  rcases e6_edge_maps (σ 2) (σ 1) (hσ (1, 2) (by decide)) (σ 0) (hσ (0, 1) (by decide))
      (σ 3) (hσ (2, 3) (by decide)) (σ 4) (hσ (3, 4) (by decide)) (σ 5) (hσ (2, 5) (by decide))
      hnd with h | h
  · exact Or.inl (Equiv.ext fun i => (hv i).trans (h i))
  · exact Or.inr (Equiv.ext fun i => (hv i).trans (h i))

/-- The nontrivial diagram automorphism of `A₂` has one orbit; the identity has two. -/
theorem a2_diagram_orbits :
    (Finset.univ.filter fun i : Fin 2 => i ≤ Equiv.swap (0 : Fin 2) 1 i).card = 1 := by
  decide

/-- The toral fixed subalgebra of an automorphism of `E₆ ⊕ A₂` preserving both ideals has
dimension at least `4 + 1 = 5`, which exceeds the rank `2` of `U₁ ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`. -/
theorem toral_bound : (2 : ℕ) < 4 + 1 := by norm_num


/-- Corollary `cor:analytic-net-extension`: the Lagrangian `Q₃` has `dim Q₃ = Dim 𝓗₃ = 3s` and
`μ(𝒩_U) = Dim Rep(𝒩_U) = 9s²`, so `μ(𝓔₃) = μ(𝒩_U)/dim(Q₃)² = 1` (holomorphic). -/
theorem mu_index_one (s : ℝ) (hs : s ≠ 0) : (9 * s ^ 2) / (3 * s) ^ 2 = 1 := by
  field_simp
  ring

/-- `Dim 𝓗₃ = 3(1 + d²) = 3s` with `s = 1 + d² = 3d + 2` for `d² = 3d + 1`. -/
theorem dim_H3 (d : ℝ) (hd : d ^ 2 = 3 * d + 1) : 3 * (1 + d ^ 2) = 3 * (3 * d + 2) := by
  rw [hd]; ring

/-- Clm `clm:analytic-net-count`: a pointed rank-six boundary category would give
`[𝒩_H : 𝒩_U] = 6`; with `[𝒩_H : 𝒩_B] = 3`, multiplicativity of the index gives
`[𝒩_B : 𝒩_U] = 2`. -/
theorem index_two_of_pointed (iHU iHB iBU : ℝ) (hmult : iHU = iHB * iBU) (h6 : iHU = 6)
    (h3 : iHB = 3) : iBU = 2 := by
  subst h6 h3
  linarith

#print axioms integer_weight_le
#print axioms six_invertibles_impossible
#print axioms e6_diagram_orbits
#print axioms e6_diagram_automorphisms

end HaagerupIzumi.C8.Branching
