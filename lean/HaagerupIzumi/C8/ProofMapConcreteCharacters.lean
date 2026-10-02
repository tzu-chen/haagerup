module

public import HaagerupIzumi.C8.ProofMapProperness
public import HaagerupIzumi.C8.CharacterUniqueness
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Geometry.Manifold.Notation

@[expose] public section

/-!
# The character branch of the proof map, made concrete

Section `sec:characters` of `c8_expanded_20260929/haagerup_c8_expanded.tex` (lines 4136–4211)
has two manuscript arrows in `ProofMap`:

* `L_characters : modularData → weightOne → projectiveVacuum → initialGrades → stronglyRational →
  characterVector ∧ lowestWeights`;
* `L_unmixed : lowestWeights → stronglyRational → certDiscriminant → unmixedRestrictions`.

`characterNodes R D u C` extends the properness nodes `ProofMapProperness.concreteNodes R D u`
(so `weightOne` is the concrete `U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`, `dim K = 6`) by concrete statements about
the character data `C : CharacterData`: the modular representation `σ`, the character vector `F` of
the twelve simple `U`-modules with graded dimensions `a l n = dim (M_l)_{n + t_l}`
(`t_l = twistExp l`), their actual lowest weights `hw l` and top dimensions `td l`, the two
Evans–Gannon columns `Ξ₀ = Ξ_{:,0}`, `Ξ₃ = Ξ_{:,d₃}` with their `q`-coefficients, and the
multiplicities of the twelve simples in the four unmixed lattice modules.

| node | concrete statement |
|---|---|
| `initialGrades` | `R.initialGrades`, and `dim U₀ = 1` (`a o 0 = 1`, CFT type) |
| `projectiveVacuum` | `R.projectiveVacuum`, and the nonvacuum simples `b, a, c₀` of trivial twist have no weight-zero vectors (`a l 0 = 0`; strict positivity of nonvacuum lowest weights) |
| `characterVector` | `F = Ξ₀` and `a l n = e₀ l n` for all `l, n`: the character vector is the `γ = 0` Evans–Gannon vector |
| `lowestWeights` | `hw l = lowestWeight l` and `td l = topDim l` (the table at line 4178) |
| `unmixedRestrictions` | the modules `(0, ±1)` restrict to `c₁` and `(±1, 0)` to `c₂` |

`characters_arrow` proves `L_characters` through `CharacterUniqueness.haagerup_character_unique`
(itself through the fully proved `pole_cancellation`) and `Characters.gamma_eq_zero`;
`unmixed_arrow` proves `L_unmixed` through `Characters.unmixed_restriction` and
`Characters.unmixed_restriction_two`.  For `γ = 0` the manuscript reads the coefficient
`dim U₁ = 6 + 13γ` off the identity `χ = Ξ₀ + γ Ξ₃`; this needs uniqueness of `q`-expansion
coefficients, proved here (`qseries_coeff_eq_zero`, via Tannery's theorem).

Remaining inputs (`CharacterInputs`) are explicit hypotheses, each tagged **[external]**,
**[certificate]**, **[definitional]** or **[manuscript step]**: finite image (DLN Theorem I), the
diagonal character `T` and `S_{0,c₁} ≠ 0` (Huang, with the modular data and `c = 8`), holomorphy,
covariance and convergence of the characters (Zhu, Huang), their `q`-expansions and the meaning
of `hw, td` and of the `q^{2/3}` coefficient of `ch U` (definitions), the Evans–Gannon
fundamental matrix (`EvansGannon`, external), and, for `L_unmixed`, the lattice data of the four
unmixed lattice modules (certificate) with the bookkeeping of their semisimple restriction
(manuscript step).  Inputs that the manuscript takes from a premise node of the arrow are stated
conditionally on that node of `R` (`modularData`, `stronglyRational`, `certDiscriminant`, and the
opaque parts of `projectiveVacuum`, `initialGrades`).

The index type `Label` of the twelve simple `U`-modules is the one of `Characters`; the combined
file `ProofMapConcrete` uses it also for the top bound and for strong unitarity.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Characters HaagerupIzumi.C8.CharacterUniqueness Complex
open Filter Topology
open scoped MatrixGroups Manifold Matrix

/-! ### Uniqueness of `q`-expansion coefficients -/

/-- A power series absolutely convergent on `(0, 1)` tends to its constant term as `r → 0⁺`
(Tannery's theorem). -/
theorem tendsto_powerSeries_const (d : ℕ → ℂ)
    (hs : ∀ r : ℝ, 0 < r → r < 1 → Summable fun k => ‖d k‖ * r ^ k) :
    Tendsto (fun r : ℝ => ∑' k, d k * (r : ℂ) ^ k) (𝓝[>] 0) (𝓝 (d 0)) := by
  have hlim : ∀ k, Tendsto (fun r : ℝ => d k * (r : ℂ) ^ k) (𝓝[>] 0)
      (𝓝 (d k * ((0 : ℝ) : ℂ) ^ k)) := fun k =>
    ((continuous_const.mul (Complex.continuous_ofReal.pow k)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hsum0 : ∑' k, d k * ((0 : ℝ) : ℂ) ^ k = d 0 := by
    rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
    simp
  rw [← hsum0]
  refine tendsto_tsum_of_dominated_convergence (f := fun (r : ℝ) (k : ℕ) => d k * (r : ℂ) ^ k)
    (bound := fun k => ‖d k‖ * (1 / 2 : ℝ) ^ k) (hs (1 / 2) (by norm_num) (by norm_num)) hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with r hr k
  show ‖d k * (r : ℂ) ^ k‖ ≤ ‖d k‖ * (1 / 2 : ℝ) ^ k
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1.le hr.2.le k) (norm_nonneg _)

/-- A power series absolutely convergent and vanishing on `(0, 1)` has zero constant term. -/
theorem powerSeries_const_eq_zero (d : ℕ → ℂ)
    (hs : ∀ r : ℝ, 0 < r → r < 1 → Summable fun k => ‖d k‖ * r ^ k)
    (h0 : ∀ r : ℝ, 0 < r → r < 1 → ∑' k, d k * (r : ℂ) ^ k = 0) : d 0 = 0 := by
  have hT := tendsto_powerSeries_const d hs
  have hev : (fun r : ℝ => ∑' k, d k * (r : ℂ) ^ k) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact h0 r hr.1 hr.2
  exact tendsto_nhds_unique (hT.congr' hev) tendsto_const_nhds

/-- A power series absolutely convergent and vanishing on `(0, 1)` has zero coefficients. -/
theorem powerSeries_coeff_eq_zero (c : ℕ → ℂ)
    (hs : ∀ r : ℝ, 0 < r → r < 1 → Summable fun k => ‖c k‖ * r ^ k)
    (h0 : ∀ r : ℝ, 0 < r → r < 1 → ∑' k, c k * (r : ℂ) ^ k = 0) : ∀ n, c n = 0 := by
  have hsn : ∀ n, ∀ r : ℝ, 0 < r → r < 1 → Summable fun k => ‖c (k + n)‖ * r ^ k := by
    intro n r hr0 hr1
    have h := (summable_nat_add_iff n).mpr (hs r hr0 hr1)
    have hrn : r ^ n ≠ 0 := pow_ne_zero n hr0.ne'
    refine (h.mul_right (r ^ n)⁻¹).congr fun k => ?_
    show ‖c (k + n)‖ * r ^ (k + n) * (r ^ n)⁻¹ = ‖c (k + n)‖ * r ^ k
    rw [pow_add, mul_assoc, mul_assoc, mul_inv_cancel₀ hrn, mul_one]
  have H : ∀ n, ∀ r : ℝ, 0 < r → r < 1 → ∑' k, c (k + n) * (r : ℂ) ^ k = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      intro r hr0 hr1
      have hcn : c n = 0 := by
        simpa using powerSeries_const_eq_zero (fun k => c (k + n)) (hsn n) ih
      have hsC : Summable fun k => c (k + n) * (r : ℂ) ^ k := by
        refine Summable.of_norm ((hsn n r hr0 hr1).congr fun k => ?_)
        show ‖c (k + n)‖ * r ^ k = ‖c (k + n) * (r : ℂ) ^ k‖
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      have hsplit : ∑' k, c (k + n) * (r : ℂ) ^ k =
          c (0 + n) * (r : ℂ) ^ 0 + ∑' k, c (k + 1 + n) * (r : ℂ) ^ (k + 1) :=
        hsC.tsum_eq_zero_add
      have e : ∑' k, c (k + 1 + n) * (r : ℂ) ^ (k + 1) =
          (r : ℂ) * ∑' k, c (k + (n + 1)) * (r : ℂ) ^ k := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        rw [show k + 1 + n = k + (n + 1) by omega, pow_succ]
        ring
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      rw [ih r hr0 hr1, zero_add, hcn, zero_mul, zero_add, e] at hsplit
      exact (mul_eq_zero.mp hsplit.symm).resolve_left hr'
  intro n
  simpa using powerSeries_const_eq_zero (fun k => c (k + n)) (hsn n) (H n)

/-- A `q`-series `∑ₙ cₙ q^{n + λ}` (`q^e = exp(2πi e τ)`), absolutely convergent at every height,
converges on `ℍ`. -/
theorem summable_qterm (lam : ℝ) (c : ℕ → ℂ)
    (hc : ∀ y : ℝ, 0 < y →
      Summable fun n : ℕ => ‖c n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + lam) * y))
    (τ : UpperHalfPlane) :
    Summable fun n : ℕ => c n * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam : ℝ) : ℂ) * τ) := by
  refine Summable.of_norm ?_
  simpa only [norm_qterm] using hc τ.im τ.im_pos

/-- **Uniqueness of `q`-expansion coefficients.**  If `∑ₙ cₙ q^{n + λ}`, absolutely convergent at
every height, vanishes on `ℍ`, then every `cₙ = 0` (restrict to `τ = iy`, put `r = e^{-2πy}`). -/
theorem qseries_coeff_eq_zero (lam : ℝ) (c : ℕ → ℂ)
    (hc : ∀ y : ℝ, 0 < y →
      Summable fun n : ℕ => ‖c n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + lam) * y))
    (h0 : ∀ τ : UpperHalfPlane,
      ∑' n : ℕ, c n * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam : ℝ) : ℂ) * τ) = 0) :
    ∀ n, c n = 0 := by
  have hexp : ∀ r : ℝ, 0 < r → r < 1 → ∃ y : ℝ, 0 < y ∧ Real.exp (-2 * Real.pi * y) = r := by
    intro r hr0 hr1
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    refine ⟨-Real.log r / (2 * Real.pi),
      div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) (by positivity), ?_⟩
    have e : -2 * Real.pi * (-Real.log r / (2 * Real.pi)) = Real.log r := by
      rw [mul_div_assoc', div_eq_iff (by positivity)]
      ring
    rw [e, Real.exp_log hr0]
  have hfac : ∀ (y : ℝ) (k : ℕ), Real.exp (-2 * Real.pi * ((k : ℝ) + lam) * y) =
      Real.exp (-2 * Real.pi * y) ^ k * Real.exp (-2 * Real.pi * lam * y) := by
    intro y k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  refine powerSeries_coeff_eq_zero c (fun r hr0 hr1 => ?_) (fun r hr0 hr1 => ?_)
  · obtain ⟨y, hy, hyr⟩ := hexp r hr0 hr1
    have hE : Real.exp (-2 * Real.pi * lam * y) ≠ 0 := (Real.exp_pos _).ne'
    refine ((hc y hy).mul_right (Real.exp (-2 * Real.pi * lam * y))⁻¹).congr fun k => ?_
    show ‖c k‖ * Real.exp (-2 * Real.pi * ((k : ℝ) + lam) * y) *
      (Real.exp (-2 * Real.pi * lam * y))⁻¹ = ‖c k‖ * r ^ k
    rw [hfac, hyr, mul_assoc, mul_assoc, mul_inv_cancel₀ hE, mul_one]
  · obtain ⟨y, hy, hyr⟩ := hexp r hr0 hr1
    have hτ : 0 < ((y : ℂ) * I).im := by simpa using hy
    have h := h0 (UpperHalfPlane.mk ((y : ℂ) * I) hτ)
    have hterm : ∀ n : ℕ, c n * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam : ℝ) : ℂ) *
        ((UpperHalfPlane.mk ((y : ℂ) * I) hτ : UpperHalfPlane) : ℂ)) =
        c n * (r : ℂ) ^ n * (Real.exp (-2 * Real.pi * lam * y) : ℂ) := by
      intro n
      have e : 2 * Real.pi * I * (((n : ℝ) + lam : ℝ) : ℂ) * ((y : ℂ) * I) =
          ((-2 * Real.pi * ((n : ℝ) + lam) * y : ℝ) : ℂ) := by
        push_cast
        linear_combination (2 * (Real.pi : ℂ) * ((n : ℂ) + (lam : ℂ)) * (y : ℂ)) * I_sq
      rw [UpperHalfPlane.coe_mk, e, ← Complex.ofReal_exp, hfac, hyr]
      push_cast
      ring
    simp only [hterm] at h
    rw [tsum_mul_right] at h
    have hE : (Real.exp (-2 * Real.pi * lam * y) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    exact (mul_eq_zero.mp h).resolve_right hE

/-- Summability of `‖f + c g‖ E` from that of `‖f‖ E` and `‖g‖ E`. -/
theorem summable_norm_add_mul {f g : ℕ → ℂ} {E : ℕ → ℝ} (c : ℂ)
    (hf : Summable fun n => ‖f n‖ * E n) (hg : Summable fun n => ‖g n‖ * E n)
    (hE : ∀ n, 0 ≤ E n) : Summable fun n => ‖f n + c * g n‖ * E n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (hE n)) (fun n => ?_)
    (hf.add (hg.mul_left ‖c‖))
  calc ‖f n + c * g n‖ * E n ≤ (‖f n‖ + ‖c‖ * ‖g n‖) * E n := by
        refine mul_le_mul_of_nonneg_right ?_ (hE n)
        calc ‖f n + c * g n‖ ≤ ‖f n‖ + ‖c * g n‖ := norm_add_le _ _
          _ = ‖f n‖ + ‖c‖ * ‖g n‖ := by rw [norm_mul]
    _ = ‖f n‖ * E n + ‖c‖ * (‖g n‖ * E n) := by ring

/-- Summability of `‖f - g‖ E` from that of `‖f‖ E` and `‖g‖ E`. -/
theorem summable_norm_sub {f g : ℕ → ℂ} {E : ℕ → ℝ}
    (hf : Summable fun n => ‖f n‖ * E n) (hg : Summable fun n => ‖g n‖ * E n)
    (hE : ∀ n, 0 ≤ E n) : Summable fun n => ‖f n - g n‖ * E n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (hE n)) (fun n => ?_)
    (hf.add hg)
  calc ‖f n - g n‖ * E n ≤ (‖f n‖ + ‖g n‖) * E n :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (hE n)
    _ = ‖f n‖ * E n + ‖g n‖ * E n := by ring

/-! ### The concrete objects -/

/-- The index `n` of the lowest weight `n + t_l` in the table at line 4178. -/
def lwIndex : Label → ℕ
  | .o => 0 | .b => 1 | .a => 1 | .c0 => 1 | .c1 => 0 | .c2 => 0
  | .d1 => 0 | .d2 => 0 | .d3 => 1 | .d4 => 0 | .d5 => 0 | .d6 => 0

theorem lowestWeight_eq_lwIndex (l : Label) : lowestWeight l = lwIndex l + twistExp l := by
  cases l <;> norm_num [lowestWeight, lwIndex, twistExp]

/-- The character data of Section `sec:characters`. -/
structure CharacterData where
  /-- Zhu's modular representation on the twelve characters. -/
  σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup Label ℂ
  /-- The character vector of the twelve simple `U`-modules `M_l`. -/
  F : UpperHalfPlane → Label → ℂ
  /-- Graded dimensions: `a l n = dim (M_l)_{n + t_l}`. -/
  a : Label → ℕ → ℕ
  /-- The lowest weight of `M_l`. -/
  hw : Label → ℚ
  /-- The top dimension of `M_l`. -/
  td : Label → ℕ
  /-- The Evans–Gannon column `Ξ_{:,0}`. -/
  Ξ₀ : UpperHalfPlane → Label → ℂ
  /-- The Evans–Gannon column `Ξ_{:,d₃}`. -/
  Ξ₃ : UpperHalfPlane → Label → ℂ
  /-- `q`-coefficients of `Ξ₀`. -/
  e₀ : Label → ℕ → ℂ
  /-- `q`-coefficients of `Ξ₃`. -/
  e₃ : Label → ℕ → ℂ
  /-- Multiplicities of the twelve simples in the restrictions of the lattice modules `(0, ±1)`. -/
  n₁ : Bool → Label → ℕ
  /-- Multiplicities of the twelve simples in the restrictions of the lattice modules `(±1, 0)`. -/
  n₂ : Bool → Label → ℕ

/-- **External input: the Evans–Gannon fundamental matrix** ([EG, §§1.4, 2.4, eq. (2.7)],
lines 4161–4170): the columns `Ξ_{:,0}` and `Ξ_{:,d₃}` are holomorphic `σ`-covariant vectors with
`q`-expansions in the exponents `n + t_l - 1/3`, absolutely convergent at every height;
`Ξ_{:,d₃}` has principal part `q^{-7/39}` in the `d₃` coordinate only; the `q^{2/3}` coefficients
of the vacuum coordinates are `6` and `13` (`dim U₁ = 6 + 13γ`); and `Ξ_{:,0}` has the lowest
weights and top dimensions of the table at line 4178 (which fixes in particular its principal
part `q^{-1/3}`). -/
structure EvansGannon (C : CharacterData) : Prop where
  hol₀ : ∀ i, MDiff (fun τ => C.Ξ₀ τ i)
  hol₃ : ∀ i, MDiff (fun τ => C.Ξ₃ τ i)
  cov₀ : ∀ (g : SL(2, ℤ)) (τ : UpperHalfPlane),
    C.Ξ₀ (g • τ) = (C.σ g : Matrix Label Label ℂ) *ᵥ C.Ξ₀ τ
  cov₃ : ∀ (g : SL(2, ℤ)) (τ : UpperHalfPlane),
    C.Ξ₃ (g • τ) = (C.σ g : Matrix Label Label ℂ) *ᵥ C.Ξ₃ τ
  q₀ : ∀ τ l, C.Ξ₀ τ l = ∑' n : ℕ, C.e₀ l n *
    Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) * τ)
  q₃ : ∀ τ l, C.Ξ₃ τ l = ∑' n : ℕ, C.e₃ l n *
    Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) * τ)
  sum₀ : ∀ l (y : ℝ), 0 < y → Summable fun n : ℕ =>
    ‖C.e₀ l n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3)) * y)
  sum₃ : ∀ l (y : ℝ), 0 < y → Summable fun n : ℕ =>
    ‖C.e₃ l n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3)) * y)
  pp₃_o : C.e₃ .o 0 = 0
  pp₃ : ∀ l, (l = .b ∨ l = .a ∨ l = .c0) → C.e₃ l 0 = 0
  pp₃_d3 : C.e₃ .d3 0 = 1
  vac₀ : C.e₀ .o 1 = 6
  vac₃ : C.e₃ .o 1 = 13
  table : ∀ l, (∀ n < lwIndex l, C.e₀ l n = 0) ∧ C.e₀ l (lwIndex l) = (topDim l : ℂ)

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

/-- The proof map with the properness nodes (`ProofMapProperness.concreteNodes`) and the
character nodes made concrete (see the module docstring for the table). -/
def characterNodes (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData) : Nodes :=
  { concreteNodes R D u with
    initialGrades := R.initialGrades ∧ C.a .o 0 = 1
    projectiveVacuum := R.projectiveVacuum ∧ ∀ l, (l = .b ∨ l = .a ∨ l = .c0) → C.a l 0 = 0
    characterVector := C.F = C.Ξ₀ ∧ ∀ l n, (C.a l n : ℂ) = C.e₀ l n
    lowestWeights := ∀ l, C.hw l = lowestWeight l ∧ C.td l = topDim l
    unmixedRestrictions :=
      (∀ s, C.n₁ s .c1 = 1 ∧ ∀ l, l ≠ .c1 → C.n₁ s l = 0) ∧
        (∀ s, C.n₂ s .c2 = 1 ∧ ∀ l, l ≠ .c2 → C.n₂ s l = 0) }

/-! ### The remaining inputs -/

/-- The remaining inputs of `L_characters` and `L_unmixed`, tagged **[external]** (a cited
theorem), **[certificate]** (lattice data), **[definitional]** (the meaning of a concrete
parameter) or **[manuscript step]**.  Inputs that the manuscript draws from a premise node of the
arrow are stated *conditionally on that node of `R`* (which `characterNodes` keeps opaque). -/
structure CharacterInputs (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData) : Prop where
  /-- [external] DLN Theorem I: the modular representation of the modular tensor category
  `Rep(U)` (node `stronglyRational`) has finite image. -/
  fin : R.stronglyRational → (Set.range C.σ).Finite
  /-- [external] Huang: `T` acts on characters by `e^{2πi(h - c/24)}`; the twists are those of the
  modular data (node `modularData`), `c = 8` (node `initialGrades`). -/
  T_diag : R.modularData → R.initialGrades →
    (C.σ ModularGroup.T : Matrix Label Label ℂ) = Matrix.diagonal tEigen
  /-- [external] Huang: Zhu's `S` is the categorical `S` of the modular data, so
  `S_{0,c₁} = d_{c₁}/D ≠ 0`. -/
  S_ne : R.modularData → R.stronglyRational → (C.σ ModularGroup.S : Matrix Label Label ℂ) .o .c1 ≠ 0
  /-- [external] Zhu: the characters are holomorphic on `ℍ`. -/
  hol : R.stronglyRational → ∀ i, MDiff (fun τ => C.F τ i)
  /-- [external] Zhu, Huang: the characters are modular covariant for `σ`. -/
  cov : R.stronglyRational → ∀ (g : SL(2, ℤ)) (τ : UpperHalfPlane),
    C.F (g • τ) = (C.σ g : Matrix Label Label ℂ) *ᵥ C.F τ
  /-- [definitional] the characters are the `q`-series of the graded dimensions; the weights of
  `M_l` lie in `t_l + ℤ_{≥0}` by `θ = e^{2πiL(0)}` (twists of `modularData`) and `h ≥ 0` (node
  `projectiveVacuum`). -/
  qexp : R.projectiveVacuum → R.modularData → ∀ τ l, C.F τ l = ∑' n : ℕ, (C.a l n : ℂ) *
    Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) * τ)
  /-- [external] Zhu: absolute convergence of the characters on `ℍ`. -/
  summ : R.stronglyRational → ∀ l (y : ℝ), 0 < y → Summable fun n : ℕ =>
    ‖(C.a l n : ℂ)‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3)) * y)
  /-- [definitional] `hw l`, `td l` are the lowest weight and top dimension of `M_l`. -/
  low : ∀ l, (∀ n : ℕ, (n : ℚ) + twistExp l < C.hw l → C.a l n = 0) ∧
    (∃ n : ℕ, (n : ℚ) + twistExp l = C.hw l ∧ C.a l n = C.td l) ∧ 0 < C.td l
  /-- [definitional] the `q^{2/3}` coefficient of `ch U` is `dim U₁` (with `U = D.U u`). -/
  U1 : C.a .o 1 = Module.finrank k ↥(D.U u ⊓ A.grade 1)
  /-- [external] Evans–Gannon, for the modular data of `Rep(U)` (node `modularData`). -/
  EG : R.modularData → EvansGannon C
  /-- [certificate] the lattice modules `(0, ±1)` have weights in `1/3 + ℤ_{≥0}` (node
  `certDiscriminant`); [manuscript step] each simple summand of the semisimple restriction (node
  `stronglyRational`) has its lowest weight among them. -/
  res₁ : R.certDiscriminant → R.stronglyRational → ∀ s l, 0 < C.n₁ s l → ∃ j : ℕ,
    C.hw l = 1 / 3 + j
  /-- [certificate] the lowest space of `(0, ±1)` has dimension `3`; [manuscript step] it is the
  sum of the tops of the summands of lowest weight `1/3`. -/
  top₁ : R.certDiscriminant → R.stronglyRational → ∀ s,
    ((allLabels.filter fun l => C.hw l = 1 / 3).map (fun l => C.n₁ s l * C.td l)).sum = 3
  /-- [certificate], [manuscript step] the same for `(±1, 0)`, weights in `2/3 + ℤ_{≥0}`. -/
  res₂ : R.certDiscriminant → R.stronglyRational → ∀ s l, 0 < C.n₂ s l → ∃ j : ℕ,
    C.hw l = 2 / 3 + j
  /-- [certificate], [manuscript step] the same for `(±1, 0)`, lowest space of dimension `27`. -/
  top₂ : R.certDiscriminant → R.stronglyRational → ∀ s,
    ((allLabels.filter fun l => C.hw l = 2 / 3).map (fun l => C.n₂ s l * C.td l)).sum = 27

/-! ### The two arrows -/

/-- **`L_characters`** (Section `sec:characters`, Lemma `lem:haagerup-character-unique`,
lines 4136–4190).

* Concrete nodes: `weightOne` (`U₁ = K`, `dim K = 6`, from properness), `projectiveVacuum`
  (no weight-zero vectors in `b, a, c₀`), `initialGrades` (`dim U₀ = 1`), `characterVector`,
  `lowestWeights`.  `modularData` and `stronglyRational` stay opaque; the inputs drawn from them
  (and from the opaque parts of `projectiveVacuum`, `initialGrades`) are applied to them.
* Concrete theorems: `CharacterUniqueness.haagerup_character_unique` (no invariant vector, then
  `pole_cancellation`) gives `F = Ξ₀ + γ Ξ₃` with `γ` the actual polar coefficient of the `d₃`
  coordinate; `qseries_coeff_eq_zero` compares coefficients; `Characters.gamma_eq_zero` turns
  `dim U₁ = 6 + 13γ` and `dim U₁ = 6` into `γ = 0`.
* Remaining inputs: the fields `fin`, `T_diag`, `S_ne`, `hol`, `cov`, `qexp`, `summ`, `low`,
  `U1`, `EG` of `CharacterInputs` (tagged there). -/
theorem characters_arrow (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData)
    (H : CharacterInputs R D u C) :
    (characterNodes R D u C).modularData → (characterNodes R D u C).weightOne →
      (characterNodes R D u C).projectiveVacuum → (characterNodes R D u C).initialGrades →
      (characterNodes R D u C).stronglyRational →
      (characterNodes R D u C).characterVector ∧ (characterNodes R D u C).lowestWeights := by
  rintro hmd ⟨hW1, hW2, -⟩ ⟨hpvR, hpv⟩ ⟨hinitR, hinit⟩ hsr
  have hfin := H.fin hsr
  have hT := H.T_diag hmd hinitR
  have hS := H.S_ne hmd hsr
  have hF := H.hol hsr
  have hFcov := H.cov hsr
  have hFq := H.qexp hpvR hmd
  have ha := H.summ hsr
  have hlow := H.low
  have hU1 := H.U1
  have EG := H.EG hmd
  -- `γ`: the actual polar coefficient of the twist-`2/13` coordinate
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℕ, γ = C.a .d3 0 := ⟨_, rfl⟩
  -- the comparison vector `Ξ₀ + γ Ξ₃`
  obtain ⟨G, hGdef⟩ : ∃ G : UpperHalfPlane → Label → ℂ,
      ∀ τ, G τ = C.Ξ₀ τ + (γ : ℂ) • C.Ξ₃ τ :=
    ⟨fun τ => C.Ξ₀ τ + (γ : ℂ) • C.Ξ₃ τ, fun _ => rfl⟩
  have hGl : ∀ τ l, G τ l = C.Ξ₀ τ l + (γ : ℂ) * C.Ξ₃ τ l := fun τ l => by
    simp only [hGdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hG : ∀ i, MDiff (fun τ => G τ i) := by
    intro i
    have h : (fun τ => G τ i) = (fun τ => C.Ξ₀ τ i) + (γ : ℂ) • (fun τ => C.Ξ₃ τ i) := by
      funext τ
      simp [hGl]
    rw [h]
    exact (EG.hol₀ i).add ((EG.hol₃ i).const_smul (γ : ℂ))
  have hGcov : ∀ (g : SL(2, ℤ)) (τ : UpperHalfPlane),
      G (g • τ) = (C.σ g : Matrix Label Label ℂ) *ᵥ G τ := by
    intro g τ
    rw [hGdef, hGdef, Matrix.mulVec_add, Matrix.mulVec_smul, EG.cov₀ g τ, EG.cov₃ g τ]
  have hsumb : ∀ l (y : ℝ), 0 < y → Summable fun n : ℕ =>
      ‖C.e₀ l n + (γ : ℂ) * C.e₃ l n‖ *
        Real.exp (-2 * Real.pi * ((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3)) * y) :=
    fun l y hy => summable_norm_add_mul (γ : ℂ) (EG.sum₀ l y hy) (EG.sum₃ l y hy)
      (fun n => (Real.exp_pos _).le)
  have hGq : ∀ τ l, G τ l = ∑' n : ℕ, (C.e₀ l n + (γ : ℂ) * C.e₃ l n) *
      Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) * τ) := by
    intro τ l
    rw [hGl, EG.q₀ τ l, EG.q₃ τ l, ← tsum_mul_left,
      ← Summable.tsum_add (summable_qterm _ _ (EG.sum₀ l) τ)
        ((summable_qterm _ _ (EG.sum₃ l) τ).mul_left _)]
    exact tsum_congr fun n => by ring
  -- the principal parts agree
  have he₀o : C.e₀ .o 0 = 1 := by
    have h := (EG.table .o).2
    simpa [lwIndex, topDim] using h
  have hvac : (C.a .o 0 : ℂ) = C.e₀ .o 0 + (γ : ℂ) * C.e₃ .o 0 := by
    simp [hinit, he₀o, EG.pp₃_o]
  have hpos : ∀ l : Label, (l = .b ∨ l = .a ∨ l = .c0) →
      (C.a l 0 : ℂ) = 0 ∧ C.e₀ l 0 + (γ : ℂ) * C.e₃ l 0 = 0 := by
    intro l hl
    have hlw : 0 < lwIndex l := by rcases hl with rfl | rfl | rfl <;> decide
    exact ⟨by simp [hpv l hl], by simp [(EG.table l).1 0 hlw, EG.pp₃ l hl]⟩
  have hγ : (C.a .d3 0 : ℂ) = C.e₀ .d3 0 + (γ : ℂ) * C.e₃ .d3 0 := by
    rw [(EG.table .d3).1 0 (by decide), EG.pp₃_d3, hγdef]
    ring
  -- Lemma `lem:haagerup-character-unique`
  have hFG : C.F = G := haagerup_character_unique C.σ hfin hT hS C.F G hF hG hFcov hGcov
    (fun l n => (C.a l n : ℂ)) (fun l n => C.e₀ l n + (γ : ℂ) * C.e₃ l n) hFq hGq ha hsumb
    hvac hpos hγ
  -- comparison of coefficients
  have hcoefb : ∀ l n, (C.a l n : ℂ) = C.e₀ l n + (γ : ℂ) * C.e₃ l n := by
    intro l
    have hvan : ∀ τ : UpperHalfPlane,
        ∑' n : ℕ, ((C.a l n : ℂ) - (C.e₀ l n + (γ : ℂ) * C.e₃ l n)) *
          Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) *
            τ) = 0 := by
      intro τ
      simp only [sub_mul]
      rw [Summable.tsum_sub (summable_qterm _ _ (ha l) τ) (summable_qterm _ _ (hsumb l) τ),
        ← hFq τ l, ← hGq τ l, hFG, sub_self]
    have hz := qseries_coeff_eq_zero (((twistExp l : ℚ) : ℝ) - 1 / 3)
      (fun n => (C.a l n : ℂ) - (C.e₀ l n + (γ : ℂ) * C.e₃ l n))
      (fun y hy => summable_norm_sub (ha l y hy) (hsumb l y hy) (fun n => (Real.exp_pos _).le))
      hvan
    intro n
    exact sub_eq_zero.mp (hz n)
  -- `dim U₁ = 6 + 13γ = 6` forces `γ = 0`
  have hv1 := hcoefb .o 1
  rw [EG.vac₀, EG.vac₃] at hv1
  have hdim6 : C.a .o 1 = 6 := by rw [hU1, hW1, hW2]
  have hnat : C.a .o 1 = 6 + 13 * γ := by
    have h : ((C.a .o 1 : ℕ) : ℂ) = ((6 + 13 * γ : ℕ) : ℂ) := by
      rw [hv1]
      push_cast
      ring
    exact_mod_cast h
  have hγ0 : γ = 0 := gamma_eq_zero γ (C.a .o 1) hnat hdim6
  have hcoef : ∀ l n, (C.a l n : ℂ) = C.e₀ l n := fun l n => by
    rw [hcoefb l n, hγ0]
    simp
  have hFΞ : C.F = C.Ξ₀ := by
    funext τ l
    rw [hFG, hGl, hγ0]
    simp
  refine ⟨⟨hFΞ, hcoef⟩, fun l => ?_⟩
  -- the table of lowest weights and top dimensions
  obtain ⟨hbelow, ⟨n₀, hn₀, hatd⟩, htdpos⟩ := hlow l
  obtain ⟨hz, htop⟩ := EG.table l
  have hlt : ∀ n < lwIndex l, C.a l n = 0 := fun n hn => by
    have h := hcoef l n
    rw [hz n hn] at h
    exact_mod_cast h
  have hN : C.a l (lwIndex l) = topDim l := by
    have h := hcoef l (lwIndex l)
    rw [htop] at h
    exact_mod_cast h
  have htopPos : 0 < topDim l := by cases l <;> decide
  have hn₀eq : n₀ = lwIndex l := by
    rcases lt_trichotomy n₀ (lwIndex l) with h | h | h
    · have h0 := hlt n₀ h
      omega
    · exact h
    · have hlt' : ((lwIndex l : ℕ) : ℚ) + twistExp l < C.hw l := by
        rw [← hn₀]
        have : ((lwIndex l : ℕ) : ℚ) < n₀ := by exact_mod_cast h
        linarith
      have h0 := hbelow (lwIndex l) hlt'
      omega
  subst hn₀eq
  refine ⟨?_, ?_⟩
  · rw [← hn₀, lowestWeight_eq_lwIndex]
  · rw [← hatd, hN]

/-- **`L_unmixed`** (Corollary `cor:unmixed-lattice-restrictions`, lines 4191–4206).

* Concrete nodes: `lowestWeights` (the actual `hw`, `td` are the table), `unmixedRestrictions`.
  `stronglyRational` (semisimplicity of the restriction) and `certDiscriminant` (the lattice
  modules) stay opaque; the bookkeeping inputs are applied to them.
* Concrete theorems: `Characters.unmixed_restriction`, `Characters.unmixed_restriction_two`.
* Remaining inputs: the fields `res₁`, `top₁`, `res₂`, `top₂` of `CharacterInputs`, stated with
  the *actual* lowest weights and top dimensions (tagged there). -/
theorem unmixed_arrow (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData)
    (H : CharacterInputs R D u C) :
    (characterNodes R D u C).lowestWeights → (characterNodes R D u C).stronglyRational →
      (characterNodes R D u C).certDiscriminant →
      (characterNodes R D u C).unmixedRestrictions := by
  intro hlw hsr hdisc
  have hres₁ := H.res₁ hdisc hsr
  have htop₁ := H.top₁ hdisc hsr
  have hres₂ := H.res₂ hdisc hsr
  have htop₂ := H.top₂ hdisc hsr
  have hhw : C.hw = lowestWeight := funext fun l => (hlw l).1
  have htd : C.td = topDim := funext fun l => (hlw l).2
  refine ⟨fun s => ?_, fun s => ?_⟩
  · have h1 := hres₁ s
    have h2 := htop₁ s
    rw [hhw] at h1 h2
    rw [htd] at h2
    exact unmixed_restriction (C.n₁ s) h1 h2
  · have h1 := hres₂ s
    have h2 := htop₂ s
    rw [hhw] at h1 h2
    rw [htd] at h2
    exact unmixed_restriction_two (C.n₂ s) h1 h2

/-- **The two character arrows of the proof map are theorems** for `characterNodes R D u C`,
under the inputs `CharacterInputs` (tagged there).  Since
`characterNodes R D u C` agrees with `ProofMapProperness.concreteNodes R D u` on the properness
nodes, `properness_arrows` also applies to it; so in `Inputs (characterNodes R D u C)` the six
fields `L_gates`, `L_recursive`, `L_weightOne`, `L_proper`, `L_characters`, `L_unmixed` need
not be assumed. -/
theorem character_arrows (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData)
    (H : CharacterInputs R D u C) :
    let N := characterNodes R D u C
    (N.modularData → N.weightOne → N.projectiveVacuum → N.initialGrades → N.stronglyRational →
      N.characterVector ∧ N.lowestWeights) ∧
    (N.lowestWeights → N.stronglyRational → N.certDiscriminant → N.unmixedRestrictions) :=
  ⟨characters_arrow R D u C H, unmixed_arrow R D u C H⟩

#print axioms qseries_coeff_eq_zero
#print axioms characters_arrow
#print axioms unmixed_arrow
#print axioms character_arrows

end HaagerupIzumi.C8.ProofMap
