module

public import HaagerupIzumi.C8.ProofMapSimples
public import HaagerupIzumi.C8.Branching

@[expose] public section

/-!
# The branching arrows of the proof map, made concrete

Section "Branching" of Appendix G of `c8_expanded_20260929/haagerup_c8_expanded.tex` (lines
3213–3318) has three manuscript arrows in `ProofMap` whose concrete core is formalized here:

* `L_branchB : stronglyRational → weightOne → certStructural → topBound → certDimensions →
  branchB` (eq:B-branching, lines 3213–3221);
* `L_rankFork : lagrangianCenter → branchH → rankFork` (eq:rank-fork, lines 3263–3272);
* `L_noSign : weightOne → branchB → stronglyRational → noSignExtension`
  (Lemma `lem:no-sign-extension`, lines 3300–3318).

The concrete objects:

* `SD : SimpleData Simp` (`ProofMapSimples`): the isomorphism classes `Simp` of simple `U`-modules,
  with their lowest weights `SD.hw` and top dimensions `SD.td` (not yet identified with the twelve
  labels of the character table; that identification comes after the modular data);
* `BranchBData A σ Simp`: a decomposition `B↓U = ⊕_{j : σ} M_j` of the lattice VOA `B` (the space
  `V` of `A`) into simple `U`-modules, recorded by the isomorphism class `lab j : Simp` of `M_j`,
  its weight-one space `T j = (M_j)₁ ⊆ B₁`, and the summand `vac` containing the vacuum;
* `BranchHData Simp`: the multiplicities `mult l` of the simple `U`-modules in `H↓U`;
* `SignData A`: the finite-order automorphisms `g` of `B` with their linear action `act g` and the
  dimension `toral g` of a maximal toral subalgebra of `(B₁)^g`, and the proposition
  `XInvertible` ("the summand `X` of `B↓U` is invertible in `Rep(U)`").

`branchingNodes R D u SD Bb Hd Sg ι` overrides the following nodes of `R : Nodes`:

| node | concrete statement |
|---|---|
* `certStructural`: `R.certStructural`, and the zero-mode action on the 80 complementary currents
  is irreducible: `B₁/K` has no proper nonzero subspace stable under the zero modes `a_(d-1)` of
  the states `a ∈ U_d` (`CurrentsIrreducible`, part of `cert:structural-inputs`, lines 2677–2682);
* `branchB`: eq:B-branching, the summands are exactly `vac` and one `x ≠ vac`; the summand `vac`
  has weight-one space `U₁`; `h_{M_x} = 1`; `dim (M_x)_top = 80`;
* `branchH`: eq:H-branching-fork, `H↓U = 𝟏 ⊕ X ⊕ Y ⊕ Y*` as a multiplicity function, with lowest
  weights `0, 1, 1, 1` and top dimensions `80, 81, 81` of `X, Y, Y*` (`HBranching`);
* `rankFork`: `rank 𝓕 = dim End_𝒞(H) = ∑_l mult(l)²` (`card ι`, `ι` the simples of `𝓕`);
* `noSignExtension`: `X` is not invertible, and no finite-order automorphism `g` of `B` has
  `B^g = U`.

`ProofMapConcreteBoundary.boundaryNodes` is applied on top of these: it adds `card ι ∈ {4, 6}` to
`rankFork` and `d_X ≠ 1` to `noSignExtension` as conjuncts, and `branchRankFork_arrow`,
`noSign_arrow` prove these conjuncts as well.  `branchH` is the conclusion of `L_branchH`, proved in
`ProofMapConcreteBranchH.branchH_arrow`.

Remaining inputs are tagged **[external]**, **[certificate]**, **[definitional]**, **[standard]**
or **[manuscript step]** in the field docstrings of `BranchBInputs`, `SignInputs` and in the
arrow docstrings.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Characters

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

/-! ### The concrete objects and nodes -/

/-- `F ⊆ B` is stable under the zero modes `a_(d-1)` of the homogeneous states `a ∈ U_d`. -/
def UZeroModeStable (D : ClosureData A) (u : V) (F : Submodule k V) : Prop :=
  ∀ (d : ℕ) (a : V), a ∈ D.U u ⊓ A.grade d → ∀ w ∈ F, A.mode ((d : ℤ) - 1) a w ∈ F

/-- **Certificate (part of `cert:structural-inputs`, lines 2677–2682, 3213–3218): the zero-mode
action on the eighty complementary currents is irreducible.**  Every subspace `K ≤ W ≤ B₁` stable
under the zero modes of `U` is `K` or `B₁` (`K = U₁` by the node `weightOne`). -/
def CurrentsIrreducible (D : ClosureData A) (u : V) : Prop :=
  ∀ W : Submodule k V, D.K ≤ W → W ≤ A.grade 1 → UZeroModeStable D u W →
    W = D.K ∨ W = A.grade 1

/-- A decomposition `B↓U = ⊕_{j : σ} M_j` into simple `U`-modules. -/
structure BranchBData (A : VertexOperatorAlgebra k V) (σ Simp : Type*) where
  /-- The isomorphism class `lab j : Simp` of the simple summand `M_j` among the simple
  `U`-modules (`SimpleData`). -/
  lab : σ → Simp
  /-- The weight-one space `(M_j)₁ ⊆ B₁` of the summand `M_j`. -/
  T : σ → Submodule k V
  /-- The summand containing the vacuum `𝟏 ∈ B₀`. -/
  vac : σ

/-- eq:B-branching, `B↓U = U ⊕ X`, `h_X = 1`, `dim X_top = 80`: the summands are exactly the
vacuum summand (whose weight-one space is `U₁`, i.e. it is `U`) and one further summand `X = M_x`
of lowest weight `1` with an `80`-dimensional top. -/
def BranchB {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V) {σ : Type*}
    (Bb : BranchBData A σ Simp) : Prop :=
  ∃ x, x ≠ Bb.vac ∧ (∀ j, j = Bb.vac ∨ j = x) ∧ Bb.T Bb.vac = D.U u ⊓ A.grade 1 ∧
    SD.hw (Bb.lab x) = 1 ∧ Module.finrank k (Bb.T x) = 80

/-- The multiplicities of the simple `U`-modules (indexed by `Simp`) in `H↓U`. -/
structure BranchHData (Simp : Type*) where
  /-- `mult l = [H↓U : M_l]`. -/
  mult : Simp → ℕ

/-- The indicator `[l = x]`. -/
def indL {Simp : Type*} [DecidableEq Simp] (x l : Simp) : ℕ := if l = x then 1 else 0

/-- eq:H-branching-fork, `H↓U = 𝟏 ⊕ X ⊕ Y ⊕ Y*` with `h_Y = h_{Y*} = 1`, `dim Y_top =
dim Y*_top = 81` (and `h_X = 1`, `dim X_top = 80`, `h_𝟏 = 0`): the multiplicity function is the
sum of the indicators of four simples `l₁, X, Y, Y* : Simp` with these lowest weights and top dimensions.  `Y*` (the
restriction of `J²`) may or may not be isomorphic to `Y` (the restriction of `J`). -/
def HBranching {Simp : Type*} [DecidableEq Simp] (SD : SimpleData Simp) (Hd : BranchHData Simp) :
    Prop :=
  ∃ l₁ lX lY lYs : Simp, (∀ l, Hd.mult l = ∑ i, indL (![l₁, lX, lY, lYs] i) l) ∧
    SD.hw l₁ = 0 ∧ SD.hw lX = 1 ∧ SD.hw lY = 1 ∧ SD.hw lYs = 1 ∧
    SD.td lX = 80 ∧ SD.td lY = 81 ∧ SD.td lYs = 81

/-- Finite-order automorphisms of `B` and the toral data of Lemma `lem:no-sign-extension`. -/
structure SignData (A : VertexOperatorAlgebra k V) where
  /-- The finite-order automorphisms of `B`. -/
  Aut : Type
  /-- The linear action of `g` on `B`. -/
  act : Aut → V →ₗ[k] V
  /-- The dimension of a maximal toral subalgebra of the fixed Lie algebra `(B₁)^g`. -/
  toral : Aut → ℕ
  /-- "The summand `X` of `B↓U = U ⊕ X` is an invertible object of `Rep(U)`." -/
  XInvertible : Prop

/-- `B^g = U`: the fixed vectors of `g` are exactly the vectors of `U`. -/
def FixesExactlyU (D : ClosureData A) (u : V) (Sg : SignData A) (g : Sg.Aut) : Prop :=
  ∀ v, Sg.act g v = v ↔ v ∈ D.U u

/-- The number of orbits of a permutation of `Fin n` (the number of orbit minima). -/
def orbitCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ m : Fin n, i ≤ (σ ^ (m : ℕ)) i).card

/-- The proof map with the branching nodes made concrete (table in the module docstring). -/
def branchingNodes (R : Nodes) (D : ClosureData A) (u : V) {Simp : Type*} [Fintype Simp]
    [DecidableEq Simp] (SD : SimpleData Simp) {σ : Type*}
    (Bb : BranchBData A σ Simp) (Hd : BranchHData Simp) (Sg : SignData A) (ι : Type*) [Fintype ι] :
    Nodes :=
  { R with
    certStructural := R.certStructural ∧ CurrentsIrreducible D u
    branchB := BranchB SD D u Bb
    branchH := HBranching SD Hd
    rankFork := Fintype.card ι = ∑ l, Hd.mult l ^ 2
    noSignExtension := ¬ Sg.XInvertible ∧ ∀ g, ¬ FixesExactlyU D u Sg g }

/-! ### `L_branchB` -/

/-- The remaining inputs of `L_branchB`, tagged; `rat` is the opaque node `stronglyRational`. -/
structure BranchBInputs {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V)
    {σ : Type*} [Fintype σ] (Bb : BranchBData A σ Simp) (rat : Prop) : Prop where
  /-- [definitional] `B` is `ℤ`-graded, so every summand has an integral lowest weight `SD.hw` of
  its class. -/
  int : ∀ j, ∃ n : ℤ, SD.hw (Bb.lab j) = n
  /-- [definitional] The summand containing `𝟏` contains `U = U·𝟏`, hence is `U` (simple), and its
  weight-one space is `U₁`. -/
  vacT : Bb.T Bb.vac = D.U u ⊓ A.grade 1
  /-- [standard] `B₀ = k𝟏` (the lattice VOA is of CFT type) lies in the vacuum summand, so the
  other summands have no weight-zero vectors, i.e. lowest weight `≠ 0`. -/
  vac_unique : ∀ j, j ≠ Bb.vac → SD.hw (Bb.lab j) ≠ 0
  /-- [definitional] `T j` is the weight-one space of `M_j`. -/
  grade : ∀ j, Bb.T j ≤ A.grade 1
  /-- [external] complete reducibility of `B` over the strongly rational (regular) `U`
  (Dong–Li–Mason; node `stronglyRational`, line 3213): the `M_j` are `U`-submodules, and zero
  modes preserve weights. -/
  stable : rat → ∀ j, UZeroModeStable D u (Bb.T j)
  /-- [external] complete reducibility (as for `stable`): the sum `⊕ M_j` is direct. -/
  disj : rat → ∀ j, j ≠ Bb.vac → Disjoint (Bb.T Bb.vac) (Bb.T j)
  /-- [external] complete reducibility (as for `stable`): a simple summand of lowest weight one
  has a nonzero top `(M_j)₁`. -/
  top : rat → ∀ j, SD.hw (Bb.lab j) = 1 → Bb.T j ≠ ⊥
  /-- [external] complete reducibility (as for `stable`): `B₁ = ⊕_j (M_j)₁`. -/
  sum : rat → ∑ j, Module.finrank k (Bb.T j) = Module.finrank k (A.grade 1)

/-- A summand of integral lowest weight `0 ≤ h ≤ 17/10` other than the vacuum has `h = 1`
(`Branching.integer_weight_le`). -/
theorem hw_eq_one_of_bound {h : ℚ} (hint : ∃ n : ℤ, h = n) (h0 : 0 ≤ h) (h1 : h ≤ 17 / 10)
    (hne : h ≠ 0) : h = 1 := by
  obtain ⟨n, rfl⟩ := hint
  have h0' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h0
  have h1' : (n : ℝ) ≤ 17 / 10 := by
    have := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at this
    exact this
  rcases Branching.integer_weight_le n h0' h1' with rfl | rfl
  · exact (hne (by simp)).elim
  · simp

/-- **`L_branchB`** (eq:B-branching, lines 3213–3221).

* Concrete nodes: `weightOne` (`U₁ = K`, `dim K = 6`), `certStructural` (`CurrentsIrreducible`),
  `topBound` (`0 ≤ h ≤ 17/10` for the lowest weights `SD.hw` of all simple `U`-modules),
  `certDimensions` (`dim B₁ = 86`), `branchB`.  `stronglyRational` (opaque, `rat`) is applied to
  the complete-reducibility inputs `stable`, `disj`, `top`, `sum`.
* Concrete argument: every non-vacuum summand has `h = 1` (`Branching.integer_weight_le`); for
  such a summand `K ⊔ (M_j)₁` lies between `K` and `B₁`, is stable under the zero modes of `U`
  and is different from `K`, so it is `B₁` by irreducibility, and `dim (M_j)₁ = 86 - 6 = 80`
  (`Branching.complement_currents`); counting
  `dim B₁ = 6 + 80·#(non-vacuum summands)` leaves exactly one.
* Remaining inputs: the fields of `BranchBInputs` (tagged there). -/
theorem branchB_arrow {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V)
    {σ : Type*} [Fintype σ]
    [DecidableEq σ] (Bb : BranchBData A σ Simp) (rat : Prop) (I : BranchBInputs SD D u Bb rat) :
    rat → (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) →
    CurrentsIrreducible D u → (∀ M, 0 ≤ SD.hw M ∧ SD.hw M ≤ 17 / 10) →
    (Module.finrank k D.K = 6 ∧ Module.finrank k (A.grade 1) = 86 ∧ IsSl2SumSpan A D.K) →
    BranchB SD D u Bb := by
  rintro hrat ⟨hU1, hK6, -⟩ hirr htop ⟨-, hB86, -⟩
  have hTvac : Bb.T Bb.vac = D.K := I.vacT.trans hU1
  -- every non-vacuum summand has lowest weight one
  have hone : ∀ j, j ≠ Bb.vac → SD.hw (Bb.lab j) = 1 := fun j hj =>
    hw_eq_one_of_bound (I.int j) (htop _).1 (htop _).2 (I.vac_unique j hj)
  have : FiniteDimensional k (A.grade 1) := Module.finite_of_finrank_pos (by omega)
  have hKle : D.K ≤ A.grade 1 := hU1.symm.le.trans inf_le_right
  -- every non-vacuum summand has an 80-dimensional top
  have h80 : ∀ j, j ≠ Bb.vac → Module.finrank k (Bb.T j) = 80 := by
    intro j hj
    have hdisj : Disjoint D.K (Bb.T j) := by
      have := I.disj hrat j hj
      rwa [hTvac] at this
    have hstabK : UZeroModeStable D u D.K := by
      intro d a ha w hw
      have := I.stable hrat Bb.vac d a ha w (by rw [hTvac]; exact hw)
      rwa [hTvac] at this
    have hW : D.K ⊔ Bb.T j = D.K ∨ D.K ⊔ Bb.T j = A.grade 1 := by
      refine hirr _ le_sup_left (sup_le hKle (I.grade j)) ?_
      intro d a ha w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hstabK d a ha x hx))
        (Submodule.mem_sup_right (I.stable hrat j d a ha y hy))
    have hWB : D.K ⊔ Bb.T j = A.grade 1 := by
      refine hW.resolve_left fun hK => I.top hrat j (hone j hj) ?_
      have hle : Bb.T j ≤ D.K := le_sup_right.trans hK.le
      exact hdisj.eq_bot_of_ge hle
    have : FiniteDimensional k D.K := Submodule.finiteDimensional_of_le hKle
    have : FiniteDimensional k (Bb.T j) := Submodule.finiteDimensional_of_le (I.grade j)
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq D.K (Bb.T j)
    rw [hWB, hdisj.eq_bot, finrank_bot, hB86, hK6] at hfr
    have := Branching.complement_currents
    omega
  -- counting: `86 = 6 + 80 · #(non-vacuum summands)`
  have hsplit : Module.finrank k (Bb.T Bb.vac) +
      ∑ j ∈ Finset.univ.erase Bb.vac, Module.finrank k (Bb.T j) =
      ∑ j, Module.finrank k (Bb.T j) :=
    Finset.add_sum_erase Finset.univ (fun j => Module.finrank k (Bb.T j)) (Finset.mem_univ Bb.vac)
  have hrest : ∑ j ∈ Finset.univ.erase Bb.vac, Module.finrank k (Bb.T j) =
      (Finset.univ.erase Bb.vac).card * 80 :=
    Finset.sum_const_nat fun j hj => h80 j (Finset.ne_of_mem_erase hj)
  rw [hrest, hTvac, hK6, I.sum hrat, hB86] at hsplit
  have hcard : (Finset.univ.erase Bb.vac).card = 1 := by omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ Finset.univ.erase Bb.vac := by rw [hx]; exact Finset.mem_singleton_self x
  have hxv : x ≠ Bb.vac := Finset.ne_of_mem_erase hxmem
  refine ⟨x, hxv, fun j => ?_, I.vacT, hone x hxv, h80 x hxv⟩
  by_cases hj : j = Bb.vac
  · exact Or.inl hj
  · have : j ∈ Finset.univ.erase Bb.vac := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    rw [hx] at this
    exact Or.inr (Finset.mem_singleton.mp this)

/-! ### `L_rankFork` -/

theorem sum_indL_mul {Simp : Type*} [Fintype Simp] [DecidableEq Simp] (x y : Simp) :
    ∑ l, indL x l * indL y l = if x = y then 1 else 0 := by
  simp only [indL, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-- `∑_l (∑_i [l = v_i])² = #{(i, j) : v_i = v_j}`. -/
theorem sum_sq_indicators {Simp : Type*} [Fintype Simp] [DecidableEq Simp] (v : Fin 4 → Simp) :
    ∑ l, (∑ i, indL (v i) l) ^ 2 = ∑ i, ∑ j, if v i = v j then 1 else 0 := by
  calc ∑ l, (∑ i, indL (v i) l) ^ 2 = ∑ l, ∑ i, ∑ j, indL (v i) l * indL (v j) l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ∑ l, indL (v i) l * indL (v j) l := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, if v i = v j then 1 else 0 := by
        simp only [sum_indL_mul]

/-- eq:rank-fork from the multiplicities: for `𝟏 ⊕ X ⊕ Y ⊕ Y*` with `𝟏, X, Y` pairwise
non-isomorphic and `Y* ≇ 𝟏, X`, `∑ mult² = 4` if `Y ≇ Y*` and `= 6` if `Y ≅ Y*`
(`Branching.rank_fork`: `1²+1²+1²+1² = 4`, `1²+1²+2² = 6`). -/
theorem sum_sq_mult_fork {Simp : Type*} [Fintype Simp] [DecidableEq Simp] (l₁ lX lY lYs : Simp)
    (h1X : l₁ ≠ lX) (h1Y : l₁ ≠ lY)
    (hXY : lX ≠ lY) (h1Ys : l₁ ≠ lYs) (hXYs : lX ≠ lYs) :
    ∑ l, (∑ i, indL (![l₁, lX, lY, lYs] i) l) ^ 2 = 4 ∨
      ∑ l, (∑ i, indL (![l₁, lX, lY, lYs] i) l) ^ 2 = 6 := by
  rw [sum_sq_indicators]
  by_cases hY : lY = lYs
  · subst hY
    right
    simp only [Fin.sum_univ_four]
    simp [h1X, h1Y, hXY, h1X.symm, h1Y.symm, hXY.symm]
  · left
    simp only [Fin.sum_univ_four]
    simp [h1X, h1Y, hXY, h1Ys, hXYs, hY, h1X.symm, h1Y.symm, hXY.symm,
      h1Ys.symm, hXYs.symm, Ne.symm hY]

/-- **`L_rankFork`** (eq:rank-fork, lines 3263–3272).

* Concrete nodes: `branchH` (`HBranching`), `rankFork` (`rank 𝓕 = ∑ mult²`, and with the conjunct
  of `boundaryNodes`, `rank 𝓕 ∈ {4, 6}`); `lagrangianCenter` stays opaque here and the adjunction
  input is applied to it.
* Concrete argument: `𝟏, X, Y` are pairwise non-isomorphic and `Y* ≇ 𝟏, X` because their lowest
  weights `0, 1, 1` and top dimensions `80, 81` differ ("distinguished by their lowest spaces",
  line 3237); then `sum_sq_mult_fork`.
* Remaining input `hadj`: [external] for the Lagrangian algebra `H = I(𝟏)` of `𝒞 ≃ Z(𝓕)`
  (DMNO Section 4, node `lagrangianCenter`), the adjunction `Hom_𝒞(I𝟏, I𝟏) ≅ Hom_𝓕(FI𝟏, 𝟏)` with
  `FI(𝟏) = ⊕_a a ⊗ a*` gives `dim End_𝒞(H) = rank 𝓕`, and [standard] Schur's lemma in the
  semisimple `𝒞` gives `dim End_𝒞(H) = ∑ mult²` (lines 3263–3268). -/
theorem branchRankFork_arrow {Simp : Type*} [Fintype Simp] [DecidableEq Simp] (SD : SimpleData Simp)
    (Hd : BranchHData Simp) (ι : Type*) [Fintype ι]
    (lag : Prop) (hadj : lag → Fintype.card ι = ∑ l, Hd.mult l ^ 2) :
    lag → HBranching SD Hd →
      Fintype.card ι = ∑ l, Hd.mult l ^ 2 ∧ (Fintype.card ι = 4 ∨ Fintype.card ι = 6) := by
  rintro hlag ⟨l₁, lX, lY, lYs, hm, h1, hX, hY, hYs, tX, tY, tYs⟩
  have hc := hadj hlag
  refine ⟨hc, ?_⟩
  have h1X : l₁ ≠ lX := fun h => by rw [h, hX] at h1; norm_num at h1
  have h1Y : l₁ ≠ lY := fun h => by rw [h, hY] at h1; norm_num at h1
  have h1Ys : l₁ ≠ lYs := fun h => by rw [h, hYs] at h1; norm_num at h1
  have hXY : lX ≠ lY := fun h => by rw [h, tY] at tX; norm_num at tX
  have hXYs : lX ≠ lYs := fun h => by rw [h, tYs] at tX; norm_num at tX
  have hsum : ∑ l, Hd.mult l ^ 2 = ∑ l, (∑ i, indL (![l₁, lX, lY, lYs] i) l) ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [hm l]
  rw [hc, hsum]
  exact sum_sq_mult_fork l₁ lX lY lYs h1X h1Y hXY h1Ys hXYs

/-! ### `L_noSign` -/

/-- The diagram automorphisms `1` and the flip of `E₆` have six and four orbits on the simple
roots (`Branching.e6_diagram_orbits` for the flip). -/
theorem orbitCount_e6 :
    orbitCount (1 : Equiv.Perm (Fin 6)) = 6 ∧ orbitCount Branching.e6Flip = 4 := by
  decide

/-- Every diagram automorphism of `E₆` has at least four orbits on the simple roots. -/
theorem four_le_orbitCount_e6 (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ e ∈ Branching.e6Edges, Branching.e6Adj (σ e.1) (σ e.2)) : 4 ≤ orbitCount σ := by
  rcases Branching.e6_diagram_automorphisms σ hσ with rfl | rfl
  · rw [orbitCount_e6.1]; norm_num
  · rw [orbitCount_e6.2]

/-- Every permutation of `Fin (n + 1)` (in particular every diagram automorphism of `A₂`) has at
least one orbit. -/
theorem one_le_orbitCount {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) : 1 ≤ orbitCount τ :=
  Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => Fin.zero_le _⟩⟩

/-- The remaining inputs of `L_noSign`, tagged. -/
structure SignInputs {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V) {σ : Type*}
    (Bb : BranchBData A σ Simp) (Sg : SignData A) : Prop where
  /-- [external] RLYG Section 5.2 (line 3309): a finite-order automorphism of a complex simple Lie
  algebra is conjugate to a toral automorphism times a diagram automorphism, and fixes a toral
  subalgebra whose dimension is the number of orbits of the diagram automorphism on the simple
  roots.  `g` preserves the nonisomorphic ideals `𝔢₆, 𝔞₂` of `B₁` separately (lines 3313–3315), so
  `(B₁)^g` contains a toral subalgebra of dimension `orbits(σ) + orbits(τ)`, `σ` a diagram
  automorphism of `E₆` (edge-preserving permutation of its simple roots), `τ` one of `A₂`. -/
  rlyg : ∀ g, ∃ σ' : Equiv.Perm (Fin 6),
    (∀ e ∈ Branching.e6Edges, Branching.e6Adj (σ' e.1) (σ' e.2)) ∧
    ∃ τ : Equiv.Perm (Fin 2), orbitCount σ' + orbitCount τ ≤ Sg.toral g
  /-- [standard] If `B^g = U` then `(B₁)^g = U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂` (node `weightOne`), whose toral
  subalgebras have dimension at most its rank `2` (lines 3305–3307, 3316–3317). -/
  rank : (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) →
    ∀ g, FixesExactlyU D u Sg g → Sg.toral g ≤ 2
  /-- [manuscript step] lines 3302–3305: if `X` were invertible, self-duality of `B` and
  connectedness give `X² = 𝟏`; the extension `B = U ⊕ X` (node `branchB`) is `ℤ/2`-graded and its
  sign automorphism `g` has `B^g = U`. -/
  sign : BranchB SD D u Bb → Sg.XInvertible → ∃ g, FixesExactlyU D u Sg g

/-- **`L_noSign`** (Lemma `lem:no-sign-extension`, lines 3300–3318).

* Concrete nodes: `weightOne`, `branchB`, `noSignExtension` (no finite-order automorphism `g` of `B`
  has `B^g = U`, `X` is not invertible, and, the conjunct of `boundaryNodes`, `d_X ≠ 1`).
* Concrete theorems: `Branching.e6_diagram_automorphisms` (the diagram automorphisms of `E₆` are `1`
  and the flip), `orbitCount_e6` (six and four orbits; `Branching.e6_diagram_orbits`), at least one
  orbit for `A₂`, and `Branching.toral_bound` (`2 < 4 + 1`).
* Remaining inputs: the fields of `SignInputs` (tagged there), and `hfp` ([standard], stated
  conditionally on `stronglyRational`, which makes `Rep(U)` a fusion category): an object of
  Frobenius–Perron dimension one is invertible (EGNO, *Tensor categories*, §3.3), so `d_X = 1`
  would make `X` invertible. -/
theorem noSign_arrow {Simp : Type*} (SD : SimpleData Simp) (D : ClosureData A) (u : V) {σ : Type*}
    (Bb : BranchBData A σ Simp) (Sg : SignData A) (I : SignInputs SD D u Bb Sg) (rat : Prop)
    (dX : ℝ)
    (hfp : rat → dX = 1 → Sg.XInvertible) :
    (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) →
    BranchB SD D u Bb → rat →
      (¬ Sg.XInvertible ∧ ∀ g, ¬ FixesExactlyU D u Sg g) ∧ dX ≠ 1 := by
  intro hw1 hB hrat
  have hnofix : ∀ g, ¬ FixesExactlyU D u Sg g := by
    intro g hg
    obtain ⟨σ', hσ', τ, hle⟩ := I.rlyg g
    have h2 := I.rank hw1 g hg
    have h4 := four_le_orbitCount_e6 σ' hσ'
    have h1 : 1 ≤ orbitCount τ := one_le_orbitCount τ
    have hb := Branching.toral_bound
    omega
  have hnotinv : ¬ Sg.XInvertible := fun hX => by
    obtain ⟨g, hg⟩ := I.sign hB hX
    exact hnofix g hg
  exact ⟨⟨hnotinv, hnofix⟩, fun h => hnotinv (hfp hrat h)⟩

#print axioms branchB_arrow
#print axioms branchRankFork_arrow
#print axioms noSign_arrow
#print axioms orbitCount_e6

end HaagerupIzumi.C8.ProofMap
