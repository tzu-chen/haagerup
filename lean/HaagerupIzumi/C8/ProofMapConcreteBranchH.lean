module

public import HaagerupIzumi.C8.ProofMapConcreteBranching
public import HaagerupIzumi.C8.VacuumLike

@[expose] public section

/-!
# The `H`-branching arrow of the proof map, made concrete

eq:H-branching-fork (lines 3222–3238 of `c8_expanded_20260929/haagerup_c8_expanded.tex`):

* `L_branchH : branchB → topBound → certStructural → stronglyRational → branchH`.

The node `branchH` is `HBranching SD Hd` (`ProofMapConcreteBranching`): the multiplicity function of
`H↓U` is `𝟏 + X + Y + Y*` with lowest weights `0, 1, 1, 1` and top dimensions `80, 81, 81` of
`X, Y, Y*`.

The concrete objects: `H = B ⊕ J ⊕ J²` (line 3231); `B↓U = ⊕_{j : σ} M_j` is `BranchBData`, and for
each of the two sectors `J, J²` a `SectorData`: the sector as a weak module over the lattice VOA
`B` (hence over `U`, by restriction of the modes), its weight-one space `J₁`, and a decomposition
`J↓U = ⊕_{j : τ} M_j` recorded by the isomorphism classes `lab j` and the weight-one spaces
`T j ⊆ J₁` of the summands.

Concrete argument (`branchH_arrow`): every summand of `J↓U` has integral lowest weight `≠ 0`, so
`h = 1` by the top bound (`hw_eq_one_of_bound`, i.e. `Branching.integer_weight_le`); its top
`T j ⊆ J₁` is a nonzero subspace stable under the zero modes of `U`, hence all of `J₁` by the
irreducibility certificate; two different summands would have the same top `J₁` and disjoint tops,
so `J↓U = Y` is simple with `dim Y_top = 81`; the same for `J²`; with `B↓U = U ⊕ X` (node `branchB`)
the multiplicity function is `𝟏 + X + Y + Y*`.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Characters HaagerupIzumi.C8.VacuumLike

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

/-- A lattice sector `J` of `H = B ⊕ J ⊕ J²` and the decomposition `J↓U = ⊕_{j : τ} M_j`. -/
structure SectorData (A : VertexOperatorAlgebra k V) (M : Type*) [AddCommGroup M] [Module k M]
    (τ Simp : Type*) where
  /-- `J` as a weak module over the lattice VOA `B`. -/
  W : WeakModule A.toVertexAlgebra M
  /-- The weight-one space `J₁`. -/
  J1 : Submodule k M
  /-- The isomorphism class of the summand `M_j` among the simple `U`-modules. -/
  lab : τ → Simp
  /-- The weight-one space `(M_j)₁ ⊆ J₁`. -/
  T : τ → Submodule k M

variable {M : Type*} [AddCommGroup M] [Module k M] {τ : Type*}

/-- `F ⊆ M` is stable under the zero modes `a_(d-1)` of the homogeneous states `a ∈ U_d`. -/
def ZeroModeStable (D : ClosureData A) (u : V) (W : WeakModule A.toVertexAlgebra M)
    (F : Submodule k M) : Prop :=
  ∀ (d : ℕ) (a : V), a ∈ D.U u ⊓ A.grade d → ∀ w ∈ F, W.act ((d : ℤ) - 1) a w ∈ F

/-- **Certificate (`cert:structural-inputs`, lines 3224–3230):** the top `J₁` of a mixed lattice
sector is `81`-dimensional and irreducible under the zero modes of `U`. -/
def SectorCertificate (D : ClosureData A) (u : V) (S : SectorData A M τ Simp) : Prop :=
  Module.finrank k S.J1 = 81 ∧
    ∀ F : Submodule k M, F ≤ S.J1 → ZeroModeStable D u S.W F → F = ⊥ ∨ F = S.J1

/-- The remaining inputs of `L_branchH` for one sector, tagged; `cs`, `rat` are the opaque parts of
`certStructural` and `stronglyRational`. -/
structure SectorInputs {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V)
    [Fintype τ]
    (S : SectorData A M τ Simp) (cs rat : Prop) : Prop where
  /-- [certificate] `SectorCertificate`, part of `certStructural` (`cs`, its opaque part). -/
  cert : cs → SectorCertificate D u S
  /-- [definitional] `H` is `ℤ`-graded (holomorphic), so the summands have integral lowest
  weights. -/
  int : ∀ j, ∃ n : ℤ, SD.hw (S.lab j) = n
  /-- [certificate] the mixed sector `J` starts at weight one (line 3224), so no summand has
  lowest weight zero. -/
  noZero : ∀ j, SD.hw (S.lab j) ≠ 0
  /-- [definitional] `T j` is the weight-one space of `M_j`. -/
  grade : ∀ j, S.T j ≤ S.J1
  /-- [external] complete reducibility of `J` over the strongly rational (regular) `U`
  (Dong–Li–Mason; node `stronglyRational`, "`J↓U` is semisimple", line 3236): the `M_j` are
  `U`-submodules, and zero modes preserve weights. -/
  stable : rat → ∀ j, ZeroModeStable D u S.W (S.T j)
  /-- [external] complete reducibility (as for `stable`): the sum `⊕ M_j` is direct. -/
  disj : rat → ∀ j j', j ≠ j' → Disjoint (S.T j) (S.T j')
  /-- [external] complete reducibility (as for `stable`): a simple summand of lowest weight one
  has a nonzero top `(M_j)₁`. -/
  top : rat → ∀ j, SD.hw (S.lab j) = 1 → S.T j ≠ ⊥
  /-- [external] complete reducibility (as for `stable`): `J₁ = ⊕_j (M_j)₁`. -/
  sum : rat → ∑ j, Module.finrank k (S.T j) = Module.finrank k S.J1
  /-- [definitional] for a summand of lowest weight one, the top dimension is `dim (M_j)₁`. -/
  td : ∀ j, SD.hw (S.lab j) = 1 → SD.td (S.lab j) = Module.finrank k (S.T j)

/-- **One sector restricts to a single simple `U`-module** of lowest weight one with an
`81`-dimensional top. -/
theorem sector_simple {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V)
    [Fintype τ]
    (S : SectorData A M τ Simp) (cs rat : Prop) (I : SectorInputs SD D u S cs rat) (hcs : cs)
    (hrat : rat) (htop : ∀ M, 0 ≤ SD.hw M ∧ SD.hw M ≤ 17 / 10) :
    ∃ y, (∀ j, j = y) ∧ SD.hw (S.lab y) = 1 ∧ SD.td (S.lab y) = 81 := by
  obtain ⟨h81, hirr⟩ := I.cert hcs
  have hone : ∀ j, SD.hw (S.lab j) = 1 := fun j =>
    hw_eq_one_of_bound (I.int j) (htop _).1 (htop _).2 (I.noZero j)
  have hfull : ∀ j, S.T j = S.J1 := fun j =>
    (hirr _ (I.grade j) (I.stable hrat j)).resolve_left (I.top hrat j (hone j))
  have hJ : S.J1 ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h81
    exact absurd h81 (by norm_num)
  have hsub : ∀ j j' : τ, j = j' := by
    intro j j'
    by_contra hne
    have hd := I.disj hrat j j' hne
    rw [hfull j, hfull j'] at hd
    exact hJ (disjoint_self.mp hd)
  obtain ⟨y⟩ : Nonempty τ := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have := I.sum hrat
    rw [Finset.univ_eq_empty, Finset.sum_empty, h81] at this
    exact absurd this (by norm_num)
  refine ⟨y, fun j => hsub j y, hone y, ?_⟩
  rw [I.td y (hone y), hfull y, h81]

/-- The remaining inputs of `L_branchH` linking the three pieces `B, J, J²` to the multiplicity
function of `H↓U`, tagged. -/
structure BranchHInputs {Simp : Type*} [DecidableEq Simp] (SD : SimpleData Simp) {σ : Type*}
    [Fintype σ] (Bb : BranchBData A σ Simp)
    (Hd : BranchHData Simp) {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂]
    [Module k M₂] {τ₁ τ₂ : Type*} [Fintype τ₁] [Fintype τ₂] (S₁ : SectorData A M₁ τ₁ Simp)
    (S₂ : SectorData A M₂ τ₂ Simp) : Prop where
  /-- [definitional] `H↓U = B↓U ⊕ J↓U ⊕ J²↓U` (line 3231): the multiplicities add. -/
  mult : ∀ l, Hd.mult l = ∑ j, indL (Bb.lab j) l + ∑ j, indL (S₁.lab j) l + ∑ j, indL (S₂.lab j) l
  /-- [definitional] the vacuum summand `U` has lowest weight `0` (CFT type). -/
  vac : SD.hw (Bb.lab Bb.vac) = 0
  /-- [definitional] for the summand `X` of lowest weight one, the top dimension is `dim X₁`. -/
  tdX : ∀ j, SD.hw (Bb.lab j) = 1 → SD.td (Bb.lab j) = Module.finrank k (Bb.T j)

/-- **`L_branchH`** (eq:H-branching-fork, lines 3222–3238).

* Concrete nodes: `branchB` (`B↓U = U ⊕ X`), `topBound`, `branchH` (`HBranching`).  The sector
  certificates are applied to the opaque part `cs` of `certStructural`, the complete-reducibility
  inputs to the opaque `stronglyRational` (`rat`).
* Concrete theorems: `sector_simple` (via `hw_eq_one_of_bound`, i.e. `Branching.integer_weight_le`),
  and the counting of indicators.
* Remaining inputs: `SectorInputs` for `J` and `J²`, and `BranchHInputs` (fields tagged). -/
theorem branchH_arrow {Simp : Type*} [DecidableEq Simp] (SD : SimpleData Simp) (D : ClosureData A)
    (u : V) {σ : Type*} [Fintype σ] (Bb : BranchBData A σ Simp) (Hd : BranchHData Simp)
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
    [AddCommGroup M₂] [Module k M₂] {τ₁ τ₂ : Type*} [Fintype τ₁] [Fintype τ₂]
    (S₁ : SectorData A M₁ τ₁ Simp) (S₂ : SectorData A M₂ τ₂ Simp) (cs rat : Prop)
    (I₁ : SectorInputs SD D u S₁ cs rat) (I₂ : SectorInputs SD D u S₂ cs rat)
    (IH : BranchHInputs SD Bb Hd S₁ S₂) :
    BranchB SD D u Bb → (∀ M, 0 ≤ SD.hw M ∧ SD.hw M ≤ 17 / 10) → cs → rat → HBranching SD Hd := by
  rintro ⟨x, hxv, hall, -, hX1, hX80⟩ htop hcs hrat
  obtain ⟨y₁, hy₁, hY₁, tY₁⟩ := sector_simple SD D u S₁ cs rat I₁ hcs hrat htop
  obtain ⟨y₂, hy₂, hY₂, tY₂⟩ := sector_simple SD D u S₂ cs rat I₂ hcs hrat htop
  refine ⟨Bb.lab Bb.vac, Bb.lab x, S₁.lab y₁, S₂.lab y₂, fun l => ?_, IH.vac, hX1, hY₁, hY₂,
    by rw [IH.tdX x hX1, hX80], tY₁, tY₂⟩
  rw [IH.mult l, Fintype.sum_eq_add Bb.vac x (Ne.symm hxv) (fun j hj => absurd (hall j)
      (by rintro (h | h) <;> [exact hj.1 h; exact hj.2 h])),
    Fintype.sum_eq_single y₁ (fun j hj => absurd (hy₁ j) hj),
    Fintype.sum_eq_single y₂ (fun j hj => absurd (hy₂ j) hj), Fin.sum_univ_four]
  rfl

#print axioms sector_simple
#print axioms branchH_arrow

end HaagerupIzumi.C8.ProofMap
