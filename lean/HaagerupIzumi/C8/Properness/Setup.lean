module

public import HaagerupIzumi.C8.Properness.ModeLemmas

@[expose] public section

/-! # Finite data of the properness argument

Data and spaces of `c8_expanded_20260929/haagerup_c8_expanded.tex`,
Sections `sec:construction`–`sec:finite` (lines 1872–2266):

* the six currents `(H_L,E_L,F_L)`, `(H_R,E_R,F_R)` (eqs. `eq:leftcurrents`,
  `eq:rightcurrents`), spanning the current space `K`;
* the constructed spaces `S₂ ⊂ U₂`, `S₃ ⊂ U₃` (Certificate `cert:initial`) and the actual
  triplet `P₄ = span{q₊, q₀, q₋}` (line 2211, record
  `hi_cft_20260923_next_structure_p4_controls.json`, where `q₀ = F_R q₊`, `q₋ = F_R q₀`);
* the normal spaces of eqs. `eq:normal4`, `eq:normal5`, as spans of the displayed words:
  `N₃ = K₋₁S₂ + TS₂`, `N₄ = K₋₁S₃ + TS₃ + (S₂)₋₁S₂`, `W₄ = N₄ + P₄`,
  `N₅ = K₋₁W₄ + TW₄ + (S₂)₋₁S₃`.

  The manuscript says (line 2216) that these "denote full differential normal spaces,
  using the lower closure identities to reorder expressions".  We use the displayed spans
  themselves; every reordered word that the argument needs is *proved* to lie in them
  (skew symmetry, the negative-mode reduction and the lower identities), so no reordering
  claim is assumed.  Each displayed word is a differential normal word in
  `K, S₂, S₃, P₄`, so membership in these spans implies membership in the normal span
  `𝒩` of Theorem `thm:recursive`.

* `LowerCertificate`: the exact lower identities (Certificate `cert:lower`, record
  `hi_cft_20260923_next_structure_lower_closure.json`, 3,970 relations; Lemma `lem:levels`;
  Certificate `cert:initial`, records `hi_cft_20260923_c8_exact_unitary_certificate.json`,
  `hi_cft_20260923_c8_grade3_exact_v2.json`, `hi_cft_20260923_c8_minimal_generators.json`)
  and the triplet controls (record `hi_cft_20260923_next_structure_p4_controls.json`:
  18 current-zero-mode identities and 6 Virasoro controls).  Every field is a finite
  exact identity or membership asserted by these records.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace VertexAlgebra

variable (A : VertexAlgebra k V)

/-- The span `X₋₁Y` of the words `x_(-1) y`. -/
def negProd (X Y : Submodule k V) : Submodule k V :=
  Submodule.span k {v | ∃ x ∈ X, ∃ y ∈ Y, v = A.mode (-1) x y}

/-- The span `X₀Y` of the singular products `x_(0) y`. -/
def zeroProd (X Y : Submodule k V) : Submodule k V :=
  Submodule.span k {v | ∃ x ∈ X, ∃ y ∈ Y, v = A.mode 0 x y}

variable {A}

theorem mem_negProd {X Y : Submodule k V} {x y : V} (hx : x ∈ X) (hy : y ∈ Y) :
    A.mode (-1) x y ∈ A.negProd X Y :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem mem_zeroProd {X Y : Submodule k V} {x y : V} (hx : x ∈ X) (hy : y ∈ Y) :
    A.mode 0 x y ∈ A.zeroProd X Y :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem negProd_le {X Y Z : Submodule k V} (h : ∀ x ∈ X, ∀ y ∈ Y, A.mode (-1) x y ∈ Z) :
    A.negProd X Y ≤ Z := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy

theorem zeroProd_le {X Y Z : Submodule k V} (h : ∀ x ∈ X, ∀ y ∈ Y, A.mode 0 x y ∈ Z) :
    A.zeroProd X Y ≤ Z := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy

theorem map_T_le {X Z : Submodule k V} (h : ∀ x ∈ X, A.T x ∈ Z) : X.map A.T ≤ Z :=
  Submodule.map_le_iff_le_comap.mpr fun x hx => h x hx

theorem negProd_le_grade {X Y : Submodule k V} {i j : ℕ} (hX : X ≤ A.grade i)
    (hY : Y ≤ A.grade j) : A.negProd X Y ≤ A.grade (i + j) :=
  negProd_le fun _ hx _ hy => A.mode_mem_grade (hX hx) (hY hy) (by push_cast; ring)

theorem zeroProd_le_grade {X Y : Submodule k V} {i j : ℕ} (hX : X ≤ A.grade i)
    (hY : Y ≤ A.grade j) (hij : 1 ≤ i + j) : A.zeroProd X Y ≤ A.grade (i + j - 1) :=
  zeroProd_le fun _ hx _ hy => A.mode_mem_grade (hX hx) (hY hy) (by push_cast [hij]; ring)

theorem map_T_le_grade {X : Submodule k V} {i : ℕ} (hX : X ≤ A.grade i) :
    X.map A.T ≤ A.grade (i + 1) :=
  map_T_le fun _ hx => A.T_grade (hX hx)

/-- Bilinear extension: a property of `x_(n) y` on spanning sets holds on the spans. -/
theorem mode_span_mem (n : ℤ) {s t : Set V} {Z : Submodule k V}
    (h : ∀ x ∈ s, ∀ y ∈ t, A.mode n x y ∈ Z) :
    ∀ x ∈ Submodule.span k s, ∀ y ∈ Submodule.span k t, A.mode n x y ∈ Z := by
  intro x hx y hy
  have h1 : ∀ x ∈ s, Submodule.span k t ≤ Z.comap (A.mode n x) := fun x hx' =>
    Submodule.span_le.mpr fun y hy' => h x hx' y hy'
  have h2 : Submodule.span k s ≤ Z.comap ((A.mode n).flip y) :=
    Submodule.span_le.mpr fun x hx' => h1 x hx' hy
  exact h2 hx

end VertexAlgebra

/-- The finite data of the closure argument (Sections `sec:construction`, `sec:finite`). -/
structure ClosureData (A : VertexOperatorAlgebra k V) where
  /-- Left current triple `(H_L, E_L, F_L)`. -/
  hL : V
  eL : V
  fL : V
  /-- Right current triple `(H_R, E_R, F_R)`. -/
  hR : V
  eR : V
  fR : V
  /-- The constructed 120-dimensional weight-two space. -/
  S₂ : Submodule k V
  /-- The constructed 956-dimensional weight-three space. -/
  S₃ : Submodule k V
  /-- The actual triplet vectors `q₊ = P4_plus`, `q₀ = P4_zero`, `q₋ = P4_minus`. -/
  qp : V
  q0 : V
  qm : V
  currents_grade : ∀ x ∈ ({hL, eL, fL, hR, eR, fR} : Set V), x ∈ A.grade 1
  S₂_grade : S₂ ≤ A.grade 2
  S₃_grade : S₃ ≤ A.grade 3
  triplet_grade : ∀ q ∈ ({qp, q0, qm} : Set V), q ∈ A.grade 4

namespace ClosureData

variable {A : VertexOperatorAlgebra k V} (D : ClosureData A)

/-- The six currents. -/
def currents : Set V := {D.hL, D.eL, D.fL, D.hR, D.eR, D.fR}

/-- The current space `K` (weight one). -/
def K : Submodule k V := Submodule.span k D.currents

/-- The triplet vectors. -/
def triplet : Set V := {D.qp, D.q0, D.qm}

/-- The actual triplet `P₄`. -/
def P₄ : Submodule k V := Submodule.span k D.triplet

/-- `N₃ = K₋₁S₂ + TS₂` (Certificate `cert:initial`). -/
def N₃ : Submodule k V := A.negProd D.K D.S₂ ⊔ D.S₂.map A.T

/-- `N₄ = K₋₁S₃ + TS₃ + (S₂)₋₁S₂` (eq. `eq:normal4`). -/
def N₄ : Submodule k V := A.negProd D.K D.S₃ ⊔ D.S₃.map A.T ⊔ A.negProd D.S₂ D.S₂

/-- `W₄ = N₄ + P₄` (eq. `eq:normal4`). -/
def W₄ : Submodule k V := D.N₄ ⊔ D.P₄

/-- `N₅ = K₋₁W₄ + TW₄ + (S₂)₋₁S₃` (eq. `eq:normal5`). -/
def N₅ : Submodule k V := A.negProd D.K D.W₄ ⊔ D.W₄.map A.T ⊔ A.negProd D.S₂ D.S₃

/-- The full differential normal space `𝒩₃(K + S₂) = 𝒩(K ∪ S₂) ∩ V₃`
(Definition `def:normal-span`). -/
def fullN₃ : Submodule k V := A.normalSpan ((D.K : Set V) ∪ D.S₂) ⊓ A.grade 3

/-- The full differential normal space `𝒩₄(K + S₂ + S₃) = 𝒩(K ∪ S₂ ∪ S₃) ∩ V₄`. -/
def fullN₄ : Submodule k V := A.normalSpan ((D.K : Set V) ∪ D.S₂ ∪ D.S₃) ⊓ A.grade 4

/-- The ladder of target spaces by weight: `ℂ1, K, S₂, S₃, W₄, N₅`, and everything above. -/
def ladder : ℕ → Submodule k V
  | 0 => A.grade 0
  | 1 => D.K
  | 2 => D.S₂
  | 3 => D.S₃
  | 4 => D.W₄
  | 5 => D.N₅
  | _ + 6 => ⊤

/-! ### Grades -/

theorem K_grade : D.K ≤ A.grade 1 :=
  Submodule.span_le.mpr fun x hx => D.currents_grade x hx

theorem P₄_grade : D.P₄ ≤ A.grade 4 :=
  Submodule.span_le.mpr fun x hx => D.triplet_grade x hx

theorem N₃_grade : D.N₃ ≤ A.grade 3 :=
  sup_le (VertexAlgebra.negProd_le_grade D.K_grade D.S₂_grade)
    (VertexAlgebra.map_T_le_grade D.S₂_grade)

theorem N₄_grade : D.N₄ ≤ A.grade 4 :=
  sup_le (sup_le (VertexAlgebra.negProd_le_grade D.K_grade D.S₃_grade)
    (VertexAlgebra.map_T_le_grade D.S₃_grade))
    (VertexAlgebra.negProd_le_grade D.S₂_grade D.S₂_grade)

theorem W₄_grade : D.W₄ ≤ A.grade 4 :=
  sup_le D.N₄_grade D.P₄_grade

theorem N₅_grade : D.N₅ ≤ A.grade 5 :=
  sup_le (sup_le (VertexAlgebra.negProd_le_grade D.K_grade D.W₄_grade)
    (VertexAlgebra.map_T_le_grade D.W₄_grade))
    (VertexAlgebra.negProd_le_grade D.S₂_grade D.S₃_grade)

theorem ladder_grade : ∀ d : ℕ, d ≤ 5 → D.ladder d ≤ A.grade d
  | 0, _ => le_rfl
  | 1, _ => D.K_grade
  | 2, _ => D.S₂_grade
  | 3, _ => D.S₃_grade
  | 4, _ => D.W₄_grade
  | 5, _ => D.N₅_grade
  | _ + 6, h => absurd h (by omega)

/-! ### Membership of the displayed words -/

theorem mem_K {x : V} (hx : x ∈ D.currents) : x ∈ D.K := Submodule.subset_span hx

theorem eL_mem : D.eL ∈ D.K := D.mem_K (by simp [currents])
theorem eR_mem : D.eR ∈ D.K := D.mem_K (by simp [currents])
theorem fL_mem : D.fL ∈ D.K := D.mem_K (by simp [currents])
theorem fR_mem : D.fR ∈ D.K := D.mem_K (by simp [currents])
theorem hL_mem : D.hL ∈ D.K := D.mem_K (by simp [currents])
theorem hR_mem : D.hR ∈ D.K := D.mem_K (by simp [currents])

theorem qp_mem : D.qp ∈ D.P₄ := Submodule.subset_span (by simp [triplet])
theorem q0_mem : D.q0 ∈ D.P₄ := Submodule.subset_span (by simp [triplet])
theorem qm_mem : D.qm ∈ D.P₄ := Submodule.subset_span (by simp [triplet])

theorem N₃_of_K_S₂ {x a : V} (hx : x ∈ D.K) (ha : a ∈ D.S₂) : A.mode (-1) x a ∈ D.N₃ :=
  Submodule.mem_sup_left (VertexAlgebra.mem_negProd hx ha)

theorem N₃_of_T {a : V} (ha : a ∈ D.S₂) : A.T a ∈ D.N₃ :=
  Submodule.mem_sup_right (Submodule.mem_map_of_mem ha)

theorem N₄_of_K_S₃ {x s : V} (hx : x ∈ D.K) (hs : s ∈ D.S₃) : A.mode (-1) x s ∈ D.N₄ :=
  Submodule.mem_sup_left (Submodule.mem_sup_left (VertexAlgebra.mem_negProd hx hs))

theorem N₄_of_T {s : V} (hs : s ∈ D.S₃) : A.T s ∈ D.N₄ :=
  Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs))

theorem N₄_of_S₂_S₂ {a b : V} (ha : a ∈ D.S₂) (hb : b ∈ D.S₂) : A.mode (-1) a b ∈ D.N₄ :=
  Submodule.mem_sup_right (VertexAlgebra.mem_negProd ha hb)

theorem N₄_le_W₄ : D.N₄ ≤ D.W₄ := le_sup_left

theorem P₄_le_W₄ : D.P₄ ≤ D.W₄ := le_sup_right

theorem N₅_of_K_W₄ {x w : V} (hx : x ∈ D.K) (hw : w ∈ D.W₄) : A.mode (-1) x w ∈ D.N₅ :=
  Submodule.mem_sup_left (Submodule.mem_sup_left (VertexAlgebra.mem_negProd hx hw))

theorem N₅_of_T {w : V} (hw : w ∈ D.W₄) : A.T w ∈ D.N₅ :=
  Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hw))

theorem N₅_of_S₂_S₃ {a s : V} (ha : a ∈ D.S₂) (hs : s ∈ D.S₃) : A.mode (-1) a s ∈ D.N₅ :=
  Submodule.mem_sup_right (VertexAlgebra.mem_negProd ha hs)

end ClosureData

open ClosureData

variable {A : VertexOperatorAlgebra k V}

/-- The exact lower identities and the triplet controls.

* `KK0`: the current zero modes close on `K` (the `𝔰𝔩₂ ⊕ 𝔰𝔩₂` brackets of
  Lemma `lem:levels`).
* `KS₂0`, `S₃`-provenance: Certificate `cert:initial` ("the spaces are current-stable";
  `S₃ = N₃ + Span{a₀b : a, b ∈ S₂}`).
* `TK`, `KmK`, `ω_mem`: `S₂` contains `ω_B` and the 22 affine vacuum vectors
  `x_(-2)1 = Tx`, `x_(-1)y` (Certificate `cert:initial`, lines 2025–2032, 2085–2089).
* `KS₂1`, `S₂S₂1`, `S₂S₂2`: the singular products of `K` and `S₂` with `S₂`
  (record `..._next_structure_lower_closure.json`; manuscript line 2364).
* `P₄_prov`: `P₄ ⊂ (S₂)₀S₃ + 𝒩₄(K + S₂ + S₃)` (line 2222; provenance field of the triplet
  record), stated with the full normal space.
* `hL_q … fR_qm`: the 18 exact current-zero-mode identities of the triplet record
  (left currents kill the triplet; `H_R q_± = ±2 q_±`, `H_R q₀ = 0`;
  `E_R q₊ = 0`, `E_R q₀ = 2 q₊`, `E_R q₋ = 2 q₀`; `F_R q₊ = q₀`, `F_R q₀ = q₋`,
  `F_R q₋ = 0`).
* `L1_P₄`, `L2_P₄`: the six direct Virasoro controls `L(1)P₄ ⊂ S₃`, `L(2)P₄ ⊂ S₂`
  (Certificate `cert:lower`). -/
structure LowerCertificate (D : ClosureData A) : Prop where
  KK0 : ∀ x ∈ D.K, ∀ y ∈ D.K, A.mode 0 x y ∈ D.K
  KS₂0 : ∀ x ∈ D.K, ∀ a ∈ D.S₂, A.mode 0 x a ∈ D.S₂
  KS₂1 : ∀ x ∈ D.K, ∀ a ∈ D.S₂, A.mode 1 x a ∈ D.K
  TK : ∀ x ∈ D.K, A.T x ∈ D.S₂
  KmK : ∀ x ∈ D.K, ∀ y ∈ D.K, A.mode (-1) x y ∈ D.S₂
  ω_mem : A.ω ∈ D.S₂
  S₂S₂0 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, A.mode 0 a b ∈ D.S₃
  S₂S₂1 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, A.mode 1 a b ∈ D.S₂
  S₂S₂2 : ∀ a ∈ D.S₂, ∀ b ∈ D.S₂, A.mode 2 a b ∈ D.K
  N₃_le_S₃ : D.N₃ ≤ D.S₃
  S₃_prov : D.S₃ ≤ D.N₃ ⊔ A.zeroProd D.S₂ D.S₂
  P₄_prov : D.P₄ ≤ A.zeroProd D.S₂ D.S₃ ⊔ D.fullN₄
  hL_q : ∀ q ∈ D.triplet, A.mode 0 D.hL q = 0
  eL_q : ∀ q ∈ D.triplet, A.mode 0 D.eL q = 0
  fL_q : ∀ q ∈ D.triplet, A.mode 0 D.fL q = 0
  hR_qp : A.mode 0 D.hR D.qp = (2 : k) • D.qp
  hR_q0 : A.mode 0 D.hR D.q0 = 0
  hR_qm : A.mode 0 D.hR D.qm = (-2 : k) • D.qm
  eR_qp : A.mode 0 D.eR D.qp = 0
  eR_q0 : A.mode 0 D.eR D.q0 = (2 : k) • D.qp
  eR_qm : A.mode 0 D.eR D.qm = (2 : k) • D.q0
  fR_qp : A.mode 0 D.fR D.qp = D.q0
  fR_q0 : A.mode 0 D.fR D.q0 = D.qm
  fR_qm : A.mode 0 D.fR D.qm = 0
  L1_P₄ : ∀ q ∈ D.triplet, A.mode 2 A.ω q ∈ D.S₃
  L2_P₄ : ∀ q ∈ D.triplet, A.mode 3 A.ω q ∈ D.S₂

#print axioms VertexAlgebra.mode_span_mem
#print axioms ClosureData.N₅_grade
#print axioms ClosureData.ladder_grade

end HaagerupIzumi.C8
