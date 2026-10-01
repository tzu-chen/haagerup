module

public import HaagerupIzumi.C8.Fusion.BasedRing
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The rank-six fusion ring `eq:rank6-ring`

Appendix G of `c8_expanded_20260929/haagerup_c8_expanded.tex`, lines 3792–3826.

Main theorem `rank6_ring`.  Let `R` be a based ring of rank six whose invertible
simples are exactly `1, a, a* = a²` (a cyclic group of order three).  Assume

* `hFP`: the Frobenius–Perron dimension `d` is a character with positive values
  (Frobenius–Perron theorem for fusion rings, EGNO Prop. 3.3.6; in the manuscript
  the positive spherical dimensions of the pseudo-unitary category);
* `hchar`: the complexified fusion algebra has at most two characters, and
* `hnc`: it is noncommutative.

The last two are consequences of the identification
`K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (Bischoff–Jones composition algebra,
\[BJ, Cor. 3.4\], with `End_𝓒(H)` of dimension six), which is an external
categorical input and is *not* proved here.

Then there are noninvertible simples `ρ, ρ₁ = aρ, ρ₂ = a²ρ` exhausting the
noninvertibles and `m ≥ 1` with
`ρ a = a² ρ`, all noninvertibles self-dual, and `ρ² = 1 + m(ρ + aρ + a²ρ)`
(`IsHIRing`).

Proof (as in the manuscript): if left multiplication by `a` fixed the three
noninvertibles, reciprocity makes `N_{ρ_i ρ_j}^g` independent of the invertible
`g`, so `χ_ζ` (`a ↦ ζ`, `ρ ↦ 0`) for both primitive cube roots `ζ` are characters;
together with `FPdim` this gives three characters.  Hence `a` permutes the
noninvertibles freely.  The right action commutes with it, so it is the same
cycle (then the ring is commutative) or the inverse cycle, i.e. `ρ a = a² ρ`.
Self-duality and the shape of `ρ²` follow by reciprocity; `m = 0` would make `ρ`
invertible.
-/

namespace HaagerupIzumi.C8.Fusion

open Finset BasedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fusion ring `eq:rank6-ring` (line 3823), with `a* = a²`:
the six simples are `1, a, a², ρ, ρ₁ = aρ, ρ₂ = a²ρ`; `a³ = 1`, `ρ a = a² ρ`,
the noninvertibles are self-dual and `ρ² = 1 + m(ρ + aρ + a²ρ)` with `m ≥ 1`. -/
structure IsHIRing (R : BasedRing ι) (a ρ ρ₁ ρ₂ : ι) (m : ℕ) : Prop where
  exhaust : ∀ x, x = R.unit ∨ x = a ∨ x = R.dual a ∨ x = ρ ∨ x = ρ₁ ∨ x = ρ₂
  nodup : [R.unit, a, R.dual a, ρ, ρ₁, ρ₂].Nodup
  a_inv : R.IsInvertible a
  a_mul_a : ∀ l, R.N a a l = if l = R.dual a then 1 else 0
  a_mul_ρ : ∀ l, R.N a ρ l = if l = ρ₁ then 1 else 0
  a2_mul_ρ : ∀ l, R.N (R.dual a) ρ l = if l = ρ₂ then 1 else 0
  ρ_mul_a : ∀ l, R.N ρ a l = if l = ρ₂ then 1 else 0
  dual_ρ : R.dual ρ = ρ
  dual_ρ₁ : R.dual ρ₁ = ρ₁
  dual_ρ₂ : R.dual ρ₂ = ρ₂
  ρ_mul_ρ : ∀ l, R.N ρ ρ l =
    (if l = R.unit then 1 else 0) + (if l = ρ ∨ l = ρ₁ ∨ l = ρ₂ then m else 0)
  one_le : 1 ≤ m

/-- Bookkeeping for the pointed part `{1, a, b}` with `b = a*` and `a ⊗ a = b`. -/
structure Z3 (R : BasedRing ι) (a b : ι) : Prop where
  ha : R.IsInvertible a
  hb : R.IsInvertible b
  dual_a : R.dual a = b
  dual_b : R.dual b = a
  ua : R.unit ≠ a
  ub : R.unit ≠ b
  ab : a ≠ b
  Lau : R.lmul a R.unit = a
  Laa : R.lmul a a = b
  Lab : R.lmul a b = R.unit
  Lbu : R.lmul b R.unit = b
  Lba : R.lmul b a = R.unit
  Lbb : R.lmul b b = a
  Rua : R.rmul R.unit a = a
  Raa : R.rmul a a = b
  Rba : R.rmul b a = R.unit
  Rub : R.rmul R.unit b = b
  Rab : R.rmul a b = R.unit
  Rbb : R.rmul b b = a
  LaLa : ∀ x, R.lmul a (R.lmul a x) = R.lmul b x
  LbLb : ∀ x, R.lmul b (R.lmul b x) = R.lmul a x
  LaLb : ∀ x, R.lmul a (R.lmul b x) = x
  LbLa : ∀ x, R.lmul b (R.lmul a x) = x
  RaRa : ∀ x, R.rmul (R.rmul x a) a = R.rmul x b
  RbRb : ∀ x, R.rmul (R.rmul x b) b = R.rmul x a
  RaRb : ∀ x, R.rmul (R.rmul x a) b = x
  RbRa : ∀ x, R.rmul (R.rmul x b) a = x
  dLa : ∀ x, R.dual (R.lmul a x) = R.rmul (R.dual x) b
  dLb : ∀ x, R.dual (R.lmul b x) = R.rmul (R.dual x) a
  dRa : ∀ x, R.dual (R.rmul x a) = R.lmul b (R.dual x)
  dRb : ∀ x, R.dual (R.rmul x b) = R.lmul a (R.dual x)
  LRaa : ∀ x, R.rmul (R.lmul a x) a = R.lmul a (R.rmul x a)
  LRab : ∀ x, R.rmul (R.lmul a x) b = R.lmul a (R.rmul x b)
  LRba : ∀ x, R.rmul (R.lmul b x) a = R.lmul b (R.rmul x a)
  LRbb : ∀ x, R.rmul (R.lmul b x) b = R.lmul b (R.rmul x b)

theorem Z3.of (R : BasedRing ι) {a : ι} (ha : R.IsInvertible a) (ha1 : a ≠ R.unit)
    (haa : ∀ l, R.N a a l = if l = R.dual a then 1 else 0) : Z3 R a (R.dual a) := by
  have hb : R.IsInvertible (R.dual a) := ha.dual
  have Laa : R.lmul a a = R.dual a := ha.lmul_eq (by rw [haa, if_pos rfl]; exact one_ne_zero)
  have Lba : R.lmul (R.dual a) a = R.unit :=
    hb.lmul_eq (by rw [ha.N_dual_left, if_pos rfl]; exact one_ne_zero)
  have Lbb : R.lmul (R.dual a) (R.dual a) = a := by
    have h := ha.lmul_dual_lmul a
    rwa [Laa] at h
  have Raa : R.rmul a a = R.dual a := ha.rmul_eq (by rw [haa, if_pos rfl]; exact one_ne_zero)
  exact {
    ha := ha
    hb := hb
    dual_a := rfl
    dual_b := R.dual_dual a
    ua := Ne.symm ha1
    ub := fun h => ha1 (by
      have h' := congrArg R.dual h
      rw [R.dual_unit, R.dual_dual] at h'
      exact h'.symm)
    ab := fun h => ha1 (by
      have h1 := Lba
      rw [← h, Laa, ← h] at h1
      exact h1)
    Lau := ha.lmul_unit
    Laa := Laa
    Lab := ha.lmul_eq (by rw [ha R.unit, if_pos rfl]; exact one_ne_zero)
    Lbu := hb.lmul_unit
    Lba := Lba
    Lbb := Lbb
    Rua := ha.rmul_unit_left
    Raa := Raa
    Rba := ha.rmul_eq (by rw [ha.N_dual_left, if_pos rfl]; exact one_ne_zero)
    Rub := hb.rmul_unit_left
    Rab := hb.rmul_eq (by rw [ha R.unit, if_pos rfl]; exact one_ne_zero)
    Rbb := by
      have h := ha.rmul_rmul_dual a
      rwa [Raa] at h
    LaLa := fun x => ha.lmul_lmul ha hb Laa x
    LbLb := fun x => hb.lmul_lmul hb ha Lbb x
    LaLb := fun x => ha.lmul_lmul_dual x
    LbLa := fun x => ha.lmul_dual_lmul x
    RaRa := fun x => ha.rmul_rmul ha hb Laa x
    RbRb := fun x => hb.rmul_rmul hb ha Lbb x
    RaRb := fun x => ha.rmul_rmul_dual x
    RbRa := fun x => ha.rmul_dual_rmul x
    dLa := fun x => ha.dual_lmul x
    dLb := fun x => by rw [hb.dual_lmul, R.dual_dual]
    dRa := fun x => ha.dual_rmul x
    dRb := fun x => by rw [hb.dual_rmul, R.dual_dual]
    LRaa := fun x => ha.rmul_lmul ha x
    LRab := fun x => ha.rmul_lmul hb x
    LRba := fun x => hb.rmul_lmul ha x
    LRbb := fun x => hb.rmul_lmul hb x }

namespace Z3

variable {R : BasedRing ι} {a b : ι}

theorem P_dual (Z : Z3 R a b) {x : ι} (h1 : x ≠ R.unit) (h2 : x ≠ a) (h3 : x ≠ b) :
    R.dual x ≠ R.unit ∧ R.dual x ≠ a ∧ R.dual x ≠ b := by
  refine ⟨fun h => h1 ?_, fun h => h3 ?_, fun h => h2 ?_⟩
  · have h' := congrArg R.dual h
    rwa [R.dual_dual, R.dual_unit] at h'
  · have h' := congrArg R.dual h
    rwa [R.dual_dual, Z.dual_a] at h'
  · have h' := congrArg R.dual h
    rwa [R.dual_dual, Z.dual_b] at h'

theorem P_lmul_a (Z : Z3 R a b) {x : ι} (h1 : x ≠ R.unit) (h2 : x ≠ a) (h3 : x ≠ b) :
    R.lmul a x ≠ R.unit ∧ R.lmul a x ≠ a ∧ R.lmul a x ≠ b := by
  refine ⟨fun h => h3 ?_, fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [← Z.LbLa x, h, Z.Lbu]
  · rw [← Z.LbLa x, h, Z.Lba]
  · rw [← Z.LbLa x, h, Z.Lbb]

theorem P_lmul_b (Z : Z3 R a b) {x : ι} (h1 : x ≠ R.unit) (h2 : x ≠ a) (h3 : x ≠ b) :
    R.lmul b x ≠ R.unit ∧ R.lmul b x ≠ a ∧ R.lmul b x ≠ b := by
  refine ⟨fun h => h2 ?_, fun h => h3 ?_, fun h => h1 ?_⟩
  · rw [← Z.LaLb x, h, Z.Lau]
  · rw [← Z.LaLb x, h, Z.Laa]
  · rw [← Z.LaLb x, h, Z.Lab]

theorem P_rmul_a (Z : Z3 R a b) {x : ι} (h1 : x ≠ R.unit) (h2 : x ≠ a) (h3 : x ≠ b) :
    R.rmul x a ≠ R.unit ∧ R.rmul x a ≠ a ∧ R.rmul x a ≠ b := by
  refine ⟨fun h => h3 ?_, fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [← Z.RaRb x, h, Z.Rub]
  · rw [← Z.RaRb x, h, Z.Rab]
  · rw [← Z.RaRb x, h, Z.Rbb]

theorem P_rmul_b (Z : Z3 R a b) {x : ι} (h1 : x ≠ R.unit) (h2 : x ≠ a) (h3 : x ≠ b) :
    R.rmul x b ≠ R.unit ∧ R.rmul x b ≠ a ∧ R.rmul x b ≠ b := by
  refine ⟨fun h => h2 ?_, fun h => h3 ?_, fun h => h1 ?_⟩
  · rw [← Z.RbRa x, h, Z.Rua]
  · rw [← Z.RbRa x, h, Z.Raa]
  · rw [← Z.RbRa x, h, Z.Rba]

end Z3

/-- The function `1 ↦ 1`, `a ↦ ω`, `b ↦ ω²`, all other simples `↦ 0`. -/
noncomputable def cubeChar (R : BasedRing ι) (a b : ι) (ω : ℂ) : ι → ℂ := fun x =>
  (if x = R.unit then 1 else 0) + (if x = a then ω else 0) + (if x = b then ω ^ 2 else 0)

/-- If left multiplication by `a` fixes every simple outside `{1, a, b}`, then for every
`ω` with `ω² + ω + 1 = 0` the function `cubeChar R a b ω` is a character
(lines 3804–3809). -/
theorem Z3.isCharacter_cubeChar {R : BasedRing ι} {a b : ι} (Z : Z3 R a b)
    (htriv : ∀ x, x ≠ R.unit → x ≠ a → x ≠ b → R.lmul a x = x)
    {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) : R.IsCharacter (cubeChar R a b ω) := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω4 : ω ^ 4 = ω := by linear_combination (ω ^ 2 - ω) * hω
  have hua := Z.ua
  have hub := Z.ub
  have hab := Z.ab
  have hau := hua.symm
  have hbu := hub.symm
  have hba := hab.symm
  have hLb : ∀ x, x ≠ R.unit → x ≠ a → x ≠ b → R.lmul b x = x := fun x h1 h2 h3 =>
    calc R.lmul b x = R.lmul b (R.lmul a x) := by rw [htriv x h1 h2 h3]
      _ = x := Z.LbLa x
  have hRa : ∀ x, x ≠ R.unit → x ≠ a → x ≠ b → R.rmul x a = x := fun x h1 h2 h3 => by
    obtain ⟨d1, d2, d3⟩ := Z.P_dual h1 h2 h3
    have h := Z.dLb (R.dual x)
    rw [hLb _ d1 d2 d3, R.dual_dual] at h
    exact h.symm
  have hRb : ∀ x, x ≠ R.unit → x ≠ a → x ≠ b → R.rmul x b = x := fun x h1 h2 h3 => by
    obtain ⟨d1, d2, d3⟩ := Z.P_dual h1 h2 h3
    have h := Z.dLa (R.dual x)
    rw [htriv _ d1 d2 d3, R.dual_dual] at h
    exact h.symm
  have hcases : ∀ z : ι, z = R.unit ∨ z = a ∨ z = b ∨ (z ≠ R.unit ∧ z ≠ a ∧ z ≠ b) := by
    intro z
    by_cases h1 : z = R.unit
    · exact Or.inl h1
    by_cases h2 : z = a
    · exact Or.inr (Or.inl h2)
    by_cases h3 : z = b
    · exact Or.inr (Or.inr (Or.inl h3))
    exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
  refine ⟨by simp [cubeChar, hua, hub], fun x y => ?_⟩
  have hR : ∑ l, (R.N x y l : ℂ) * cubeChar R a b ω l =
      (R.N x y R.unit : ℂ) + (R.N x y a : ℂ) * ω + (R.N x y b : ℂ) * ω ^ 2 := by
    simp [cubeChar, mul_add, Finset.sum_add_distrib, mul_ite]
  rw [hR, R.N_unit_right, Z.ha.N_right_obj, Z.hb.N_right_obj]
  rcases hcases x with hx | hx | hx | ⟨h1, h2, h3⟩
  · rw [hx, R.dual_unit, Z.Rua, Z.Rub]
    rcases hcases y with hy | hy | hy | ⟨k1, k2, k3⟩
    · rw [hy]; simp [cubeChar, hua, hub]
    · rw [hy]; simp [cubeChar, hua, hub, hab, hau]
    · rw [hy]; simp [cubeChar, hua, hub, hbu, hba]
    · simp [cubeChar, hua, hub, k1, k2, k3]
  · rw [hx, Z.dual_a, Z.Rba, Z.Rbb]
    rcases hcases y with hy | hy | hy | ⟨k1, k2, k3⟩
    · rw [hy]; simp [cubeChar, hua, hub, hab, hau]
    · rw [hy]; simp [cubeChar, hab, hau]
      ring1
    · rw [hy]; simp [cubeChar, hab, hau, hbu, hba]
      linear_combination hω3
    · simp [cubeChar, hab, hau, k1, k2, k3]
  · rw [hx, Z.dual_b, Z.Raa, Z.Rab]
    rcases hcases y with hy | hy | hy | ⟨k1, k2, k3⟩
    · rw [hy]; simp [cubeChar, hua, hub, hbu, hba]
    · rw [hy]; simp [cubeChar, hab, hau, hbu, hba]
      linear_combination hω3
    · rw [hy]; simp [cubeChar, hbu, hba]
      linear_combination hω4
    · simp [cubeChar, hbu, hba, k1, k2, k3]
  · obtain ⟨d1, d2, d3⟩ := Z.P_dual h1 h2 h3
    rw [hRa _ d1 d2 d3, hRb _ d1 d2 d3]
    by_cases hy : y = R.dual x
    · simp [cubeChar, h1, h2, h3, hy]
      linear_combination (-1 : ℂ) * hω
    · simp [cubeChar, h1, h2, h3, hy]

/-- **eq:rank6-ring** (lines 3792–3826).  See the module docstring for the hypotheses:
`hcard`, `ha`, `ha1`, `haa`, `hinv` say that the invertible simples are exactly
`1, a, a² = a*`; `hFP` (Frobenius–Perron dimension) is a positive character;
`hchar` (at most two characters) and `hnc` (noncommutativity) are the consequences
of `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` used in the manuscript. -/
theorem rank6_ring (R : BasedRing ι) (hcard : Fintype.card ι = 6) {a : ι}
    (ha : R.IsInvertible a) (ha1 : a ≠ R.unit)
    (haa : ∀ l, R.N a a l = if l = R.dual a then 1 else 0)
    (hinv : ∀ x, R.IsInvertible x → x = R.unit ∨ x = a ∨ x = R.dual a)
    (d : ι → ℝ) (hFP : R.IsCharacter d) (hFPpos : ∀ i, 0 < d i)
    (hchar : ∀ χ₁ χ₂ χ₃ : ι → ℂ, R.IsCharacter χ₁ → R.IsCharacter χ₂ → R.IsCharacter χ₃ →
      χ₁ = χ₂ ∨ χ₁ = χ₃ ∨ χ₂ = χ₃)
    (hnc : ∃ i j l, R.N i j l ≠ R.N j i l) :
    ∃ ρ ρ₁ ρ₂ m, IsHIRing R a ρ ρ₁ ρ₂ m := by
  obtain ⟨b, hbdef⟩ : ∃ b, R.dual a = b := ⟨_, rfl⟩
  have Z : Z3 R a b := hbdef ▸ Z3.of R ha ha1 haa
  rw [hbdef] at hinv haa
  have hua := Z.ua
  have hub := Z.ub
  have hab := Z.ab
  have hau := hua.symm
  have hbu := hub.symm
  have hba := hab.symm
  by_cases hA : ∀ x, x ≠ R.unit → x ≠ a → x ≠ b → R.lmul a x = x
  · /- Case A: `a` fixes every noninvertible: three characters. -/
    exfalso
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ ^ 2 + ζ + 1 = 0 := by
      obtain ⟨ζ, hζp⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 :=
        ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
      have h := hζp.geom_sum_eq_zero (by norm_num)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero] at h
      exact ⟨ζ, by linear_combination h⟩
    have hζ2 : (ζ ^ 2) ^ 2 + ζ ^ 2 + 1 = 0 := by linear_combination (ζ ^ 2 - ζ + 1) * hζ
    have χ1 := Z.isCharacter_cubeChar hA hζ
    have χ2 := Z.isCharacter_cubeChar hA hζ2
    have χ3 := hFP.map Complex.ofRealHom
    have hda : d a = 1 := by
      have h1 := hFP.map_lmul Z.ha a
      have h2 := hFP.map_lmul Z.ha b
      rw [Z.Laa] at h1
      rw [Z.Lab, hFP.map_unit] at h2
      have h3 : d a ^ 3 = 1 := by linear_combination (d a) * h1 + h2
      exact (pow_eq_one_iff_of_nonneg (hFPpos a).le (by norm_num)).mp h3
    have hv : ∀ ω : ℂ, cubeChar R a b ω a = ω := fun ω => by
      simp [cubeChar, hau, hab]
    rcases hchar _ _ _ χ1 χ2 χ3 with e | e | e
    · have h1 := congrFun e a
      rw [hv, hv] at h1
      have h3 : (3 : ℂ) = 0 := by
        linear_combination 4 * hζ - (2 * ζ + 1) * h1 - (2 * ζ + 1) * hζ
      norm_num at h3
    · have h1 := congrFun e a
      rw [hv] at h1
      simp only [hda, map_one] at h1
      have h3 : (3 : ℂ) = 0 := by linear_combination hζ - (ζ + 2) * h1
      norm_num at h3
    · have h1 := congrFun e a
      rw [hv] at h1
      simp only [hda, map_one] at h1
      have h3 : (3 : ℂ) = 0 := by linear_combination hζ2 - (ζ ^ 2 + 2) * h1
      norm_num at h3
  · /- Case B: `a` moves some noninvertible `ρ`. -/
    push Not at hA
    obtain ⟨ρ, hρ1, hρ2, hρ3, hρa⟩ := hA
    obtain ⟨ρ₁, La0⟩ : ∃ r, R.lmul a ρ = r := ⟨_, rfl⟩
    obtain ⟨ρ₂, Lb0⟩ : ∃ r, R.lmul b ρ = r := ⟨_, rfl⟩
    have La1 : R.lmul a ρ₁ = ρ₂ := by rw [← La0, Z.LaLa, Lb0]
    have La2 : R.lmul a ρ₂ = ρ := by rw [← Lb0, Z.LaLb]
    have Lb1 : R.lmul b ρ₁ = ρ := by rw [← La0, Z.LbLa]
    have Lb2 : R.lmul b ρ₂ = ρ₁ := by rw [← Lb0, Z.LbLb, La0]
    have h01 : ρ ≠ ρ₁ := fun h => hρa (by rw [La0, h])
    have h02 : ρ ≠ ρ₂ := by
      intro h
      apply hρa
      have e : R.lmul a ρ = R.lmul a ρ₂ := by rw [← h]
      rw [e, La2]
    have h12 : ρ₁ ≠ ρ₂ := by
      intro h
      apply h02
      have e : R.lmul a ρ₂ = R.lmul a ρ₁ := by rw [h]
      rw [← La2, e, La1]
    have h10 := h01.symm
    have h20 := h02.symm
    have h21 := h12.symm
    obtain ⟨hρ₁1, hρ₁2, hρ₁3⟩ : ρ₁ ≠ R.unit ∧ ρ₁ ≠ a ∧ ρ₁ ≠ b := by
      have := Z.P_lmul_a hρ1 hρ2 hρ3
      rwa [La0] at this
    obtain ⟨hρ₂1, hρ₂2, hρ₂3⟩ : ρ₂ ≠ R.unit ∧ ρ₂ ≠ a ∧ ρ₂ ≠ b := by
      have := Z.P_lmul_b hρ1 hρ2 hρ3
      rwa [Lb0] at this
    have h1ρ := hρ1.symm
    have haρ := hρ2.symm
    have hbρ := hρ3.symm
    have h1ρ₁ := hρ₁1.symm
    have haρ₁ := hρ₁2.symm
    have hbρ₁ := hρ₁3.symm
    have h1ρ₂ := hρ₂1.symm
    have haρ₂ := hρ₂2.symm
    have hbρ₂ := hρ₂3.symm
    have hnodup : [R.unit, a, b, ρ, ρ₁, ρ₂].Nodup := by
      simp [hua, hub, hab, h1ρ, haρ, hbρ, h1ρ₁, haρ₁, hbρ₁, h1ρ₂, haρ₂, hbρ₂, h01, h02, h12]
    have hall : ∀ x, x = R.unit ∨ x = a ∨ x = b ∨ x = ρ ∨ x = ρ₁ ∨ x = ρ₂ := by
      have huniv : [R.unit, a, b, ρ, ρ₁, ρ₂].toFinset = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnodup, hcard]; simp)
      intro x
      have hx : x ∈ [R.unit, a, b, ρ, ρ₁, ρ₂].toFinset := by
        rw [huniv]
        exact Finset.mem_univ x
      simpa using hx
    have hRρ := Z.P_rmul_a hρ1 hρ2 hρ3
    rcases hall (R.rmul ρ a) with h | h | h | h | h | h
    · exact absurd h hRρ.1
    · exact absurd h hRρ.2.1
    · exact absurd h hRρ.2.2
    · /- B1: `ρ a = ρ`: then the right, hence the left action of `a` is trivial. -/
      exfalso
      have R1 : R.rmul ρ₁ a = ρ₁ := by rw [← La0, Z.LRaa, h]
      have R2 : R.rmul ρ₂ a = ρ₂ := by rw [← Lb0, Z.LRba, h]
      obtain ⟨d1, d2, d3⟩ := Z.P_dual hρ1 hρ2 hρ3
      have hd : R.rmul (R.dual ρ) a = R.dual ρ := by
        rcases hall (R.dual ρ) with e | e | e | e | e | e
        · exact absurd e d1
        · exact absurd e d2
        · exact absurd e d3
        · rw [e, h]
        · rw [e, R1]
        · rw [e, R2]
      have h' := Z.dRa (R.dual ρ)
      rw [hd, R.dual_dual, Lb0] at h'
      exact h02 h'
    · /- B2: `ρ a = a ρ`: then `a` is central and the ring is commutative. -/
      exfalso
      have hRL : ∀ x, R.rmul x a = R.lmul a x := by
        intro x
        rcases hall x with e | e | e | e | e | e <;> rw [e]
        · rw [Z.Rua, Z.Lau]
        · rw [Z.Raa, Z.Laa]
        · rw [Z.Rba, Z.Lab]
        · rw [h, La0]
        · rw [← La0, Z.LRaa, h, La0]
        · rw [← Lb0, Z.LRba, h, Lb1, Lb0, La2]
      have hS : ∀ x y l, R.N x (R.lmul a y) l = R.N (R.lmul a x) y l := fun x y l => by
        rw [Z.ha.N_lmul_right, hRL]
      have hT : ∀ x y l, R.N (R.lmul a x) y l = R.N x y (R.lmul b l) := fun x y l => by
        rw [Z.ha.N_lmul_left, Z.dual_a]
      have hC : ∀ x y, (∀ l, R.N x y l = R.N y x l) →
          ∀ l, R.N (R.lmul a x) y l = R.N y (R.lmul a x) l := by
        intro x y hxy l
        rw [hT, hS, hT, hxy]
      have hC' : ∀ x y, (∀ l, R.N x y l = R.N y x l) →
          ∀ l, R.N x (R.lmul a y) l = R.N (R.lmul a y) x l := by
        intro x y hxy l
        exact (hC y x (fun l => (hxy l).symm) l).symm
      have hbase : ∀ x y, (x = R.unit ∨ x = ρ) → (y = R.unit ∨ y = ρ) →
          ∀ l, R.N x y l = R.N y x l := by
        intro x y hx hy l
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
        · rw [R.unit_mul, R.mul_unit]
        · rw [R.unit_mul, R.mul_unit]
      have hrep : ∀ z, ∃ z₀, (z₀ = R.unit ∨ z₀ = ρ) ∧
          (z = z₀ ∨ z = R.lmul a z₀ ∨ z = R.lmul a (R.lmul a z₀)) := by
        intro z
        rcases hall z with e | e | e | e | e | e
        · exact ⟨R.unit, Or.inl rfl, Or.inl e⟩
        · exact ⟨R.unit, Or.inl rfl, Or.inr (Or.inl (by rw [e, Z.Lau]))⟩
        · exact ⟨R.unit, Or.inl rfl, Or.inr (Or.inr (by rw [e, Z.Lau, Z.Laa]))⟩
        · exact ⟨ρ, Or.inr rfl, Or.inl e⟩
        · exact ⟨ρ, Or.inr rfl, Or.inr (Or.inl (by rw [e, La0]))⟩
        · exact ⟨ρ, Or.inr rfl, Or.inr (Or.inr (by rw [e, La0, La1]))⟩
      have hcomm : ∀ x y l, R.N x y l = R.N y x l := by
        intro x y
        obtain ⟨x₀, hx₀, hx⟩ := hrep x
        obtain ⟨y₀, hy₀, hy⟩ := hrep y
        have h00 := hbase x₀ y₀ hx₀ hy₀
        have hY : ∀ l, R.N x₀ y l = R.N y x₀ l := by
          rcases hy with e | e | e <;> rw [e]
          · exact h00
          · exact hC' x₀ y₀ h00
          · exact hC' x₀ (R.lmul a y₀) (hC' x₀ y₀ h00)
        rcases hx with e | e | e <;> rw [e]
        · exact hY
        · exact hC x₀ y hY
        · exact hC (R.lmul a x₀) y (hC x₀ y hY)
      obtain ⟨i, j, l, hne⟩ := hnc
      exact hne (hcomm i j l)
    · /- B3: `ρ a = a² ρ`, the Haagerup–Izumi ring. -/
      have Rρb : R.rmul ρ b = ρ₁ := by rw [← Z.RaRa, h, ← Lb0, Z.LRba, h, Lb2]
      have Rρ₂a : R.rmul ρ₂ a = ρ₁ := by rw [← Lb0, Z.LRba, h, Lb2]
      have Rρ₁b : R.rmul ρ₁ b = ρ₂ := by rw [← La0, Z.LRab, Rρb, La1]
      have Rρ₂b : R.rmul ρ₂ b = ρ := by rw [← Lb0, Z.LRbb, Rρb, Lb1]
      obtain ⟨d1, d2, d3⟩ := Z.P_dual hρ1 hρ2 hρ3
      have hdρ : R.dual ρ = ρ := by
        rcases hall (R.dual ρ) with e | e | e | e | e | e
        · exact absurd e d1
        · exact absurd e d2
        · exact absurd e d3
        · exact e
        · exfalso
          have h' := Z.dLa ρ
          rw [La0, e, Rρ₁b] at h'
          rw [← e, R.dual_dual] at h'
          exact h02 h'
        · exfalso
          have h' := Z.dLb ρ
          rw [Lb0, e, Rρ₂a] at h'
          rw [← e, R.dual_dual] at h'
          exact h01 h'
      have hdρ₁ : R.dual ρ₁ = ρ₁ := by rw [← La0, Z.dLa, hdρ, Rρb, La0]
      have hdρ₂ : R.dual ρ₂ = ρ₂ := by rw [← Lb0, Z.dLb, hdρ, h, Lb0]
      have N1 : R.N ρ ρ R.unit = 1 := by rw [R.N_unit_right, hdρ, if_pos rfl]
      have Na : R.N ρ ρ a = 0 := by
        rw [R.frob_right, hdρ, Z.ha.N_lmul, La0, if_neg h01]
      have Nb : R.N ρ ρ b = 0 := by
        rw [R.frob_right, hdρ, Z.hb.N_lmul, Lb0, if_neg h02]
      have hkey : ∀ l, R.N ρ ρ (R.rmul l b) = R.N ρ ρ (R.lmul b l) := by
        intro l
        have e1 : R.N ρ ρ₂ l = R.N ρ ρ (R.rmul l b) := by
          rw [← h, Z.ha.N_rmul_right, Z.dual_a]
        have e2 : R.N ρ ρ₂ l = R.N ρ ρ (R.lmul b l) := by
          rw [← Lb0, Z.hb.N_lmul_right, Rρb, ← La0, Z.ha.N_lmul_left, Z.dual_a]
        rw [← e1, e2]
      have N12 : R.N ρ ρ ρ₂ = R.N ρ ρ ρ := by
        have := hkey ρ₁
        rwa [Rρ₁b, Lb1] at this
      have N11 : R.N ρ ρ ρ = R.N ρ ρ ρ₁ := by
        have := hkey ρ₂
        rwa [Rρ₂b, Lb2] at this
      have hρρ : ∀ l, R.N ρ ρ l = (if l = R.unit then 1 else 0) +
          (if l = ρ ∨ l = ρ₁ ∨ l = ρ₂ then R.N ρ ρ ρ else 0) := by
        intro l
        rcases hall l with e | e | e | e | e | e <;> rw [e] <;>
          simp [N1, Na, Nb, N12, ← N11, hau, hbu, h1ρ, haρ, hbρ, h1ρ₁, haρ₁, hbρ₁, h1ρ₂, haρ₂,
            hbρ₂, hρ1, hρ₁1, hρ₂1, h01, h02, h12, h10, h20, h21]
      have hm : 1 ≤ R.N ρ ρ ρ := by
        by_contra hm0
        have hm0' : R.N ρ ρ ρ = 0 := by omega
        have hρinv : R.IsInvertible ρ := by
          intro l
          rw [hdρ, hρρ l, hm0']
          simp
        rcases hinv ρ hρinv with e | e | e
        · exact hρ1 e
        · exact hρ2 e
        · exact hρ3 e
      refine ⟨ρ, ρ₁, ρ₂, R.N ρ ρ ρ, ?_⟩
      exact {
        exhaust := by
          intro x
          rw [hbdef]
          exact hall x
        nodup := by
          rw [hbdef]
          exact hnodup
        a_inv := Z.ha
        a_mul_a := by
          rw [hbdef]
          exact haa
        a_mul_ρ := fun l => by rw [Z.ha.N_lmul, La0]
        a2_mul_ρ := fun l => by rw [hbdef, Z.hb.N_lmul, Lb0]
        ρ_mul_a := fun l => by rw [Z.ha.N_rmul, h]
        dual_ρ := hdρ
        dual_ρ₁ := hdρ₁
        dual_ρ₂ := hdρ₂
        ρ_mul_ρ := hρρ
        one_le := hm }

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.Z3.isCharacter_cubeChar
#print axioms HaagerupIzumi.C8.Fusion.rank6_ring
