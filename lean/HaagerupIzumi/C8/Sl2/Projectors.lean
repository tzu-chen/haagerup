module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import HaagerupIzumi.CFT.FiniteClosure

@[expose] public section

/-!
# Current-zero-mode projectors from polynomials in `FE`

Formalizes the projector statements of `c8_expanded_20260929/haagerup_c8_expanded.tex`,
after Lemma `lem:current-bounds` (lines 2238–2251) and in Lemma `lem:singlet`
(`eq:projector`, lines 2312–2331).

* `lie_f_lie_e_pow_toEnd_f`: for a primitive vector `v` of weight `μ` of an `sl₂`-triple
  (Mathlib's `IsSl2Triple.HasPrimitiveVectorWith`), `F E (f^k v) = k(μ-k+1) f^k v`
  (the raising operator acts first), and `fe_pow_f_eq_feScalar`: this is
  `(j-m)(j+m+2)/4` with `j = μ`, `m = μ - 2k` (`feScalar`).  `casimir_primitive_smul`
  gives the Casimir `½H² + EF + FE = μ(μ+2)/2` on the primitive vector.
* `fePoly S a = ∏_{ℓ ∈ S} (1 - a_ℓ X)` and `fePoly_apply_sum`: on a finite sum of
  `FE`-eigenvectors, the polynomial in `FE` keeps the component with eigenvalue zero and
  kills every component whose eigenvalue `c` has `a_ℓ c = 1` for some factor `ℓ`.
* The manuscript's polynomials: `leftPoly = ∏_{ℓ=1}^{2}(1 - FE/(ℓ(ℓ+1)))`,
  `rightPoly = ∏_{ℓ=2}^{12}(1 - FE/(ℓ(ℓ+1)-2))`, and the two factors
  `singletLeftPoly`, `singletRightPoly` of `Π` in `eq:projector`.  All denominators are
  nonzero (`leftPoly_denom_ne_zero`, `rightPoly_denom_ne_zero`, `singlet_denom_ne_zero`).
  `leftPoly_apply` (weight `0`, highest weights `j ∈ {0,2,4}`), `rightPoly_apply`
  (weight `2`, `j ∈ {2,4,…,24}`), `singletLeftPoly_apply`, `singletRightPoly_apply`
  and `singletProjector_apply` (weight `(0,0)`, `j_L ∈ {0,2,4}`, `j_R ∈ {0,2,…,24}`) keep
  exactly the lowest component.  `leftPoly_apply_primitive` and `rightPoly_apply_primitive`
  state the same for actual lowering strings of primitive vectors in an `sl₂`-module.
* `singlet_recovery` is Lemma `lem:singlet`: if `W` is stable under the four current
  zero modes, `E_L t, E_R t ∈ W`, and `Π t ∈ W`, then `t ∈ W`; with
  `singlet_recovery_of_normal` for `Π t ∈ Π(N)`, `N ≤ W`.  It uses
  `HaagerupIzumi.CFT.projected_residual_recovery`.

The range of highest weights entering each projector (`|m_L| ≤ 4`, `|m_R| ≤ 24` at weight
four) is Lemma `lem:current-bounds`, formalized in `HaagerupIzumi.C8.Sl2.CurrentBounds`;
here the components are an explicit finite family, which is the hypothesis.  No other
hypotheses are used.
-/

namespace HaagerupIzumi.C8
namespace Sl2

open Polynomial LieModule

/-! ## `FE` on the lowering string of a primitive vector -/

section Primitive

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {h e f : L} {t : IsSl2Triple h e f} {m : M} {μ : R}

/-- `F E (f^k v) = k(μ - k + 1) f^k v` for a primitive vector `v` of weight `μ`. -/
theorem lie_f_lie_e_pow_toEnd_f (P : t.HasPrimitiveVectorWith m μ) (k : ℕ) :
    ⁅f, ⁅e, ((toEnd R L M f) ^ k) m⁆⁆ =
      ((k : R) * (μ - k + 1)) • ((toEnd R L M f) ^ k) m := by
  cases k with
  | zero => simp [P.lie_e]
  | succ n =>
    rw [P.lie_e_pow_succ_toEnd_f n, lie_smul, P.lie_f_pow_toEnd_f n]
    congr 1
    push_cast
    ring

/-- The scalar identity `4 k(j-k+1) = (j-m)(j+m+2)` for `m = j - 2k`. -/
theorem fe_eigenvalue_identity (j : R) (k : ℕ) :
    4 * ((k : R) * (j - k + 1)) = (j - (j - 2 * k)) * (j + (j - 2 * k) + 2) := by
  ring

/-- `H² v = μ² v`, `E F v = μ v`, `F E v = 0` on a primitive vector. -/
theorem casimir_primitive (P : t.HasPrimitiveVectorWith m μ) :
    ⁅h, ⁅h, m⁆⁆ = (μ * μ) • m ∧ ⁅e, ⁅f, m⁆⁆ = μ • m ∧ ⁅f, ⁅e, m⁆⁆ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [P.lie_h, lie_smul, P.lie_h, smul_smul]
  · simpa using P.lie_e_pow_succ_toEnd_f 0
  · rw [P.lie_e, lie_zero]

end Primitive

section Casimir

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {h e f : L} {t : IsSl2Triple h e f} {m : M} {μ : K}

/-- The Casimir `½H² + EF + FE` acts on a primitive vector of weight `μ` by `μ(μ+2)/2`;
dividing by `2(k+2)` gives the Sugawara energy `μ(μ+2)/(4(k+2))`. -/
theorem casimir_primitive_smul (P : t.HasPrimitiveVectorWith m μ) :
    (2 : K)⁻¹ • ⁅h, ⁅h, m⁆⁆ + ⁅e, ⁅f, m⁆⁆ + ⁅f, ⁅e, m⁆⁆ = (μ * (μ + 2) / 2) • m := by
  obtain ⟨h1, h2, h3⟩ := casimir_primitive P
  rw [h1, h2, h3, add_zero, smul_smul, ← add_smul]
  congr 1
  ring

end Casimir

/-! ## Polynomials in `FE` on eigenvector decompositions -/

section Projector

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_apply_of_eigen (T : Module.End K V) (p : K[X]) {c : K} {v : V}
    (hv : T v = c • v) : aeval T p v = p.eval c • v := by
  by_cases h0 : v = 0
  · simp [h0]
  · exact Module.End.aeval_apply_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hv, h0⟩)

theorem aeval_apply_sum_of_eigen (T : Module.End K V) (p : K[X]) {ι : Type*}
    (s : Finset ι) (c : ι → K) (v : ι → V) (hv : ∀ i ∈ s, T (v i) = c i • v i) :
    aeval T p (∑ i ∈ s, v i) = ∑ i ∈ s, p.eval (c i) • v i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i hi => aeval_apply_of_eigen T p (hv i hi)

/-- The product `∏_{ℓ ∈ S} (1 - a_ℓ X)`. -/
noncomputable def fePoly (S : Finset ℕ) (a : ℕ → K) : K[X] := ∏ ℓ ∈ S, (1 - C (a ℓ) * X)

theorem fePoly_eval (S : Finset ℕ) (a : ℕ → K) (c : K) :
    (fePoly S a).eval c = ∏ ℓ ∈ S, (1 - a ℓ * c) := by
  simp [fePoly, eval_prod]

theorem fePoly_eval_zero (S : Finset ℕ) (a : ℕ → K) : (fePoly S a).eval 0 = 1 := by
  rw [fePoly_eval]; simp

/-- A factor with `a_ℓ c = 1` kills the eigenvalue `c`. -/
theorem fePoly_eval_eq_zero {S : Finset ℕ} {a : ℕ → K} {c : K} {ℓ : ℕ} (hℓ : ℓ ∈ S)
    (hc : a ℓ * c = 1) : (fePoly S a).eval c = 0 := by
  rw [fePoly_eval]
  exact Finset.prod_eq_zero hℓ (by rw [hc, sub_self])

/-- General projector statement: on `v = ∑_{i ∈ I} v_i` with `T v_i = c_i v_i`, the
polynomial `∏ (1 - a_ℓ T)` returns the component `v_{i₀}` with `c_{i₀} = 0`, provided every
other eigenvalue is killed by some factor. -/
theorem fePoly_apply_sum (T : Module.End K V) (S : Finset ℕ) (a : ℕ → K) {ι : Type*}
    (I : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ I) (c : ι → K) (v : ι → V)
    (hv : ∀ i ∈ I, T (v i) = c i • v i) (hc₀ : c i₀ = 0)
    (hkill : ∀ i ∈ I, i ≠ i₀ → ∃ ℓ ∈ S, a ℓ * c i = 1) :
    aeval T (fePoly S a) (∑ i ∈ I, v i) = v i₀ := by
  rw [aeval_apply_sum_of_eigen T _ I c v hv, Finset.sum_eq_single i₀]
  · rw [hc₀, fePoly_eval_zero, one_smul]
  · intro i hi hne
    obtain ⟨ℓ, hℓ, hc⟩ := hkill i hi hne
    rw [fePoly_eval_eq_zero hℓ hc, zero_smul]
  · intro hnot
    exact absurd hi₀ hnot

/-- `FE` on the weight-`m` line of the irreducible `sl₂`-module of highest weight `j`. -/
def feScalar (j m : K) : K := (j - m) * (j + m + 2) / 4

/-- `∏_{ℓ=1}^{2} (1 - F_L E_L/(ℓ(ℓ+1)))` (line 2241). -/
noncomputable def leftPoly : K[X] :=
  fePoly (Finset.Icc 1 2) fun ℓ => ((ℓ : K) * (ℓ + 1))⁻¹

/-- `∏_{ℓ=2}^{12} (1 - F_R E_R/(ℓ(ℓ+1)-2))` (line 2243). -/
noncomputable def rightPoly : K[X] :=
  fePoly (Finset.Icc 2 12) fun ℓ => ((ℓ : K) * (ℓ + 1) - 2)⁻¹

/-- `∏_{j ∈ {2,4}} (1 - 4 F_L E_L/(j(j+2)))`, the left factor of `Π` (eq:projector). -/
noncomputable def singletLeftPoly : K[X] :=
  fePoly ((Finset.Icc 1 2).image (2 * ·)) fun j => 4 / ((j : K) * (j + 2))

/-- `∏_{j ∈ {2,4,…,24}} (1 - 4 F_R E_R/(j(j+2)))`, the right factor of `Π`. -/
noncomputable def singletRightPoly : K[X] :=
  fePoly ((Finset.Icc 1 12).image (2 * ·)) fun j => 4 / ((j : K) * (j + 2))

theorem leftPoly_eval_zero : (leftPoly : K[X]).eval 0 = 1 := fePoly_eval_zero _ _

theorem rightPoly_eval_zero : (rightPoly : K[X]).eval 0 = 1 := fePoly_eval_zero _ _

theorem singletLeftPoly_eval_zero : (singletLeftPoly : K[X]).eval 0 = 1 :=
  fePoly_eval_zero _ _

theorem singletRightPoly_eval_zero : (singletRightPoly : K[X]).eval 0 = 1 :=
  fePoly_eval_zero _ _

/-! ### Singlet recovery (Lemma `lem:singlet`) -/

theorem aeval_mem_of_stable (W : Submodule K V) (T : Module.End K V)
    (hW : ∀ x ∈ W, T x ∈ W) (q : K[X]) : ∀ x ∈ W, aeval T q x ∈ W := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro x hx
    rw [aeval_C, Module.algebraMap_end_apply]
    exact W.smul_mem a hx
  | add p q hp hq =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X]
    exact ih (T x) (hW x hx)

/-- If `T v ∈ W` and `W` is `T`-stable, then `p(T) v ≡ p(0) v` modulo `W`. -/
theorem aeval_sub_eval_zero_mem (W : Submodule K V) (T : Module.End K V)
    (hW : ∀ x ∈ W, T x ∈ W) (p : K[X]) {v : V} (hv : T v ∈ W) :
    aeval T p v - p.eval 0 • v ∈ W := by
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := p)
  have key : aeval T p v - p.eval 0 • v = aeval T q (T v) := by
    have h3 : aeval T (p - C (p.coeff 0)) v = aeval T (q * X) v := by rw [hq, mul_comm]
    rw [map_sub, LinearMap.sub_apply, aeval_C, Module.algebraMap_end_apply, map_mul,
      Module.End.mul_apply, aeval_X, coeff_zero_eq_eval_zero] at h3
    exact h3
  rw [key]
  exact aeval_mem_of_stable W T hW q _ hv

/-- Lemma `lem:singlet`: let `W` be stable under the current zero modes `E_L, F_L, E_R, F_R`
and `t` a vector with `E_L t, E_R t ∈ W`.  If `Π t ∈ W`, with `Π` of `eq:projector` and
`FE` meaning `F ∘ E`, then `t ∈ W`. -/
theorem singlet_recovery (W : Submodule K V) (EL FL ER FR : Module.End K V)
    (hFL : ∀ x ∈ W, FL x ∈ W) (hEL : ∀ x ∈ W, EL x ∈ W)
    (hFR : ∀ x ∈ W, FR x ∈ W) (hER : ∀ x ∈ W, ER x ∈ W)
    {t : V} (htL : EL t ∈ W) (htR : ER t ∈ W)
    (hproj : (aeval (FL * EL) (singletLeftPoly : K[X]) *
      aeval (FR * ER) (singletRightPoly : K[X])) t ∈ W) : t ∈ W := by
  have hTL : ∀ x ∈ W, (FL * EL) x ∈ W := fun x hx => hFL _ (hEL x hx)
  have hTR : ∀ x ∈ W, (FR * ER) x ∈ W := fun x hx => hFR _ (hER x hx)
  have hTLt : (FL * EL) t ∈ W := hFL _ htL
  have hTRt : (FR * ER) t ∈ W := hFR _ htR
  have h1 : aeval (FR * ER) (singletRightPoly : K[X]) t - t ∈ W := by
    have h := aeval_sub_eval_zero_mem W _ hTR singletRightPoly hTRt
    rw [singletRightPoly_eval_zero, one_smul] at h
    exact h
  have hTLs : (FL * EL) (aeval (FR * ER) (singletRightPoly : K[X]) t) ∈ W := by
    have e : aeval (FR * ER) (singletRightPoly : K[X]) t =
        (aeval (FR * ER) (singletRightPoly : K[X]) t - t) + t := by abel
    rw [e, map_add]
    exact W.add_mem (hTL _ h1) hTLt
  have h2 : aeval (FL * EL) (singletLeftPoly : K[X]) (aeval (FR * ER) (singletRightPoly : K[X]) t)
      - aeval (FR * ER) (singletRightPoly : K[X]) t ∈ W := by
    have h := aeval_sub_eval_zero_mem W _ hTL singletLeftPoly hTLs
    rw [singletLeftPoly_eval_zero, one_smul] at h
    exact h
  refine HaagerupIzumi.CFT.projected_residual_recovery W
    (aeval (FL * EL) (singletLeftPoly : K[X]) * aeval (FR * ER) (singletRightPoly : K[X])) t
    ?_ hproj
  have e2 : t - (aeval (FL * EL) (singletLeftPoly : K[X]) *
        aeval (FR * ER) (singletRightPoly : K[X])) t =
      -((aeval (FL * EL) (singletLeftPoly : K[X]) (aeval (FR * ER) (singletRightPoly : K[X]) t)
        - aeval (FR * ER) (singletRightPoly : K[X]) t)
        + (aeval (FR * ER) (singletRightPoly : K[X]) t - t)) := by
    rw [Module.End.mul_apply]; abel
  rw [e2]
  exact W.neg_mem (W.add_mem h2 h1)

/-- Lemma `lem:singlet` in the manuscript's form: `Π t` is a combination of `Π n_i` with
`n_i ∈ N ≤ W`, i.e. `Π t ∈ Π(N)`. -/
theorem singlet_recovery_of_normal (W N : Submodule K V) (hNW : N ≤ W)
    (EL FL ER FR : Module.End K V)
    (hFL : ∀ x ∈ W, FL x ∈ W) (hEL : ∀ x ∈ W, EL x ∈ W)
    (hFR : ∀ x ∈ W, FR x ∈ W) (hER : ∀ x ∈ W, ER x ∈ W)
    {t : V} (htL : EL t ∈ W) (htR : ER t ∈ W)
    (hproj : (aeval (FL * EL) (singletLeftPoly : K[X]) *
      aeval (FR * ER) (singletRightPoly : K[X])) t ∈
        N.map (aeval (FL * EL) (singletLeftPoly : K[X]) *
          aeval (FR * ER) (singletRightPoly : K[X]))) : t ∈ W := by
  refine singlet_recovery W EL FL ER FR hFL hEL hFR hER htL htR ?_
  obtain ⟨n, hn, hn'⟩ := Submodule.mem_map.mp hproj
  rw [← hn', Module.End.mul_apply]
  have hTL : ∀ x ∈ W, (FL * EL) x ∈ W := fun x hx => hFL _ (hEL x hx)
  have hTR : ∀ x ∈ W, (FR * ER) x ∈ W := fun x hx => hFR _ (hER x hx)
  exact aeval_mem_of_stable W _ hTL _ _ (aeval_mem_of_stable W _ hTR _ _ (hNW hn))

variable [CharZero K]

/-- On the weight-`m` line of highest weight `m + 2i`, `FE` acts by `i(m+i+1)`. -/
theorem feScalar_shift (m : K) (i : ℕ) : feScalar (m + 2 * i) m = i * (m + i + 1) := by
  unfold feScalar; ring

/-! ### Nonvanishing denominators -/

theorem leftPoly_denom_ne_zero : ∀ ℓ : ℕ, ℓ ∈ Finset.Icc 1 2 → ((ℓ : K) * (ℓ + 1)) ≠ 0 := by
  intro ℓ hℓ
  rw [Finset.mem_Icc] at hℓ
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_add_one_ne_zero ℓ)

theorem rightPoly_denom_ne_zero :
    ∀ ℓ : ℕ, ℓ ∈ Finset.Icc 2 12 → ((ℓ : K) * (ℓ + 1) - 2) ≠ 0 := by
  intro ℓ hℓ
  rw [Finset.mem_Icc] at hℓ
  have hd : ((ℓ : K) * (ℓ + 1) - 2) = (((ℓ - 1) * (ℓ + 2) : ℕ) : K) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ℓ)]
    push_cast
    ring
  rw [hd]
  exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

theorem singlet_denom_ne_zero (N : ℕ) :
    ∀ j : ℕ, j ∈ (Finset.Icc 1 N).image (2 * ·) → ((j : K) * (j + 2)) ≠ 0 := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_Icc] at hi
  have hd : (((2 * i : ℕ) : K) * (((2 * i : ℕ) : K) + 2)) =
      ((2 * i * (2 * i + 2) : ℕ) : K) := by
    push_cast; ring
  rw [hd]
  exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-! ### The `FE` scalars and the killing factors -/

/-- At weight `0`, highest weight `j = 2i`: `FE = i(i+1)`. -/
theorem feScalar_weight_zero (i : ℕ) : feScalar (2 * (i : K)) 0 = (i : K) * (i + 1) := by
  unfold feScalar; ring

/-- At weight `2`, highest weight `j = 2 + 2i`: `FE = i(i+3)`. -/
theorem feScalar_weight_two (i : ℕ) : feScalar (2 + 2 * (i : K)) 2 = (i : K) * (i + 3) := by
  unfold feScalar; ring

/-- The factor `ℓ = i` of `leftPoly` kills highest weight `j = 2i` (`i = 1, 2`). -/
theorem leftPoly_factor_kills (i : ℕ) (hi : i ≠ 0) :
    ((i : K) * ((i : K) + 1))⁻¹ * feScalar (2 * (i : K)) 0 = 1 := by
  rw [feScalar_weight_zero]
  exact inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr hi) (Nat.cast_add_one_ne_zero i))

/-- The factor `ℓ = i + 1` of `rightPoly` kills highest weight `j = 2 + 2i`
(`i = 1, …, 11`, i.e. `j = 4, …, 24`). -/
theorem rightPoly_factor_kills (i : ℕ) (hi : i ≠ 0) :
    (((i + 1 : ℕ) : K) * (((i + 1 : ℕ) : K) + 1) - 2)⁻¹ * feScalar (2 + 2 * (i : K)) 2 = 1 := by
  have hd : ((i + 1 : ℕ) : K) * (((i + 1 : ℕ) : K) + 1) - 2 = (i : K) * (i + 3) := by
    push_cast; ring
  rw [feScalar_weight_two, hd]
  have h3 : (i : K) + 3 ≠ 0 := by exact_mod_cast (show i + 3 ≠ 0 by omega)
  exact inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr hi) h3)

/-! ### The projectors -/

/-- At left weight `0`, with components of highest weight `j = 2i`, `i ∈ {0,1,2}`, the
left projector keeps the singlet. -/
theorem leftPoly_apply (T : Module.End K V) (v : ℕ → V)
    (hv : ∀ i ∈ Finset.range 3, T (v i) = feScalar (2 * (i : K)) 0 • v i) :
    aeval T (leftPoly : K[X]) (∑ i ∈ Finset.range 3, v i) = v 0 := by
  refine fePoly_apply_sum T _ _ (Finset.range 3) 0 (by simp) _ v hv (by simp [feScalar]) ?_
  intro i hi hne
  rw [Finset.mem_range] at hi
  refine ⟨i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  exact leftPoly_factor_kills i hne

/-- At right weight `2`, with components of highest weight `j = 2 + 2i`, `i ∈ {0,…,11}`
(so `j ∈ {2,…,24}`), the right projector keeps highest weight two. -/
theorem rightPoly_apply (T : Module.End K V) (v : ℕ → V)
    (hv : ∀ i ∈ Finset.range 12, T (v i) = feScalar (2 + 2 * (i : K)) 2 • v i) :
    aeval T (rightPoly : K[X]) (∑ i ∈ Finset.range 12, v i) = v 0 := by
  refine fePoly_apply_sum T _ _ (Finset.range 12) 0 (by simp) _ v hv (by simp [feScalar]) ?_
  intro i hi hne
  rw [Finset.mem_range] at hi
  refine ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  exact rightPoly_factor_kills i hne

/-- Shared step for the two singlet factors. -/
theorem singletPoly_kill (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    ∃ ℓ ∈ (Finset.Icc 1 N).image (2 * ·),
      (fun j : ℕ => 4 / ((j : K) * (j + 2))) ℓ * feScalar (2 * (i : K)) 0 = 1 := by
  refine ⟨2 * i, Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hi, hiN⟩, rfl⟩, ?_⟩
  show 4 / (((2 * i : ℕ) : K) * (((2 * i : ℕ) : K) + 2)) * feScalar (2 * (i : K)) 0 = 1
  have hden : ((2 * i : ℕ) : K) * (((2 * i : ℕ) : K) + 2) ≠ 0 := by
    have hd : (((2 * i : ℕ) : K) * (((2 * i : ℕ) : K) + 2)) =
        ((2 * i * (2 * i + 2) : ℕ) : K) := by
      push_cast; ring
    rw [hd]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hden]
  unfold feScalar
  push_cast
  ring

/-- Left factor of `Π`: at left weight `0`, components `j = 2i`, `i ∈ {0,1,2}`. -/
theorem singletLeftPoly_apply (T : Module.End K V) (v : ℕ → V)
    (hv : ∀ i ∈ Finset.range 3, T (v i) = feScalar (2 * (i : K)) 0 • v i) :
    aeval T (singletLeftPoly : K[X]) (∑ i ∈ Finset.range 3, v i) = v 0 := by
  refine fePoly_apply_sum T _ _ (Finset.range 3) 0 (by simp) _ v hv (by simp [feScalar]) ?_
  intro i hi hne
  rw [Finset.mem_range] at hi
  exact singletPoly_kill 2 i (by omega) (by omega)

/-- Right factor of `Π`: at right weight `0`, components `j = 2i`, `i ∈ {0,…,12}`
(so `j ∈ {0,2,…,24}`). -/
theorem singletRightPoly_apply (T : Module.End K V) (v : ℕ → V)
    (hv : ∀ i ∈ Finset.range 13, T (v i) = feScalar (2 * (i : K)) 0 • v i) :
    aeval T (singletRightPoly : K[X]) (∑ i ∈ Finset.range 13, v i) = v 0 := by
  refine fePoly_apply_sum T _ _ (Finset.range 13) 0 (by simp) _ v hv (by simp [feScalar]) ?_
  intro i hi hne
  rw [Finset.mem_range] at hi
  exact singletPoly_kill 12 i (by omega) (by omega)

/-- `Π` (eq:projector) on a weight-`(0,0)` vector decomposed into joint components
`t a b` of highest weights `(2a, 2b)`: it returns the joint singlet `t 0 0`. -/
theorem singletProjector_apply (TL TR : Module.End K V) (t : ℕ → ℕ → V)
    (hL : ∀ a ∈ Finset.range 3, ∀ b ∈ Finset.range 13,
      TL (t a b) = feScalar (2 * (a : K)) 0 • t a b)
    (hR : ∀ a ∈ Finset.range 3, ∀ b ∈ Finset.range 13,
      TR (t a b) = feScalar (2 * (b : K)) 0 • t a b) :
    (aeval TL (singletLeftPoly : K[X]) * aeval TR (singletRightPoly : K[X]))
      (∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 13, t a b) = t 0 0 := by
  have hin : ∀ a ∈ Finset.range 3,
      aeval TR (singletRightPoly : K[X]) (∑ b ∈ Finset.range 13, t a b) = t a 0 :=
    fun a ha => singletRightPoly_apply TR (t a) (hR a ha)
  rw [Module.End.mul_apply, map_sum, Finset.sum_congr rfl hin]
  exact singletLeftPoly_apply TL (fun a => t a 0) fun a ha => hL a ha 0 (by simp)

end Projector

/-! ## The projectors on lowering strings of primitive vectors -/

section PrimitiveProjector

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {h e f : L} {t : IsSl2Triple h e f}

/-- `F E (f^k v) = feScalar μ (μ - 2k) · f^k v` for a primitive `v` of weight `μ`. -/
theorem fe_pow_f_eq_feScalar {w : M} {μ : K} (P : t.HasPrimitiveVectorWith w μ) (k : ℕ) :
    (toEnd K L M f * toEnd K L M e) (((toEnd K L M f) ^ k) w) =
      feScalar μ (μ - 2 * k) • ((toEnd K L M f) ^ k) w := by
  rw [Module.End.mul_apply, toEnd_apply_apply, toEnd_apply_apply, lie_f_lie_e_pow_toEnd_f P k]
  congr 1
  unfold feScalar
  ring

theorem fe_pow_f_of_primitive_or_zero (w : M) (μ : K) (k : ℕ)
    (hw : w = 0 ∨ t.HasPrimitiveVectorWith w μ) :
    (toEnd K L M f * toEnd K L M e) (((toEnd K L M f) ^ k) w) =
      feScalar μ (μ - 2 * k) • ((toEnd K L M f) ^ k) w := by
  rcases hw with rfl | P
  · simp
  · exact fe_pow_f_eq_feScalar P k

/-- The left projector on the weight-zero vectors `f^i w_i`, where each `w_i` is zero or a
primitive vector of weight `2i` (`i ∈ {0,1,2}`), returns `w_0`. -/
theorem leftPoly_apply_primitive (w : ℕ → M)
    (hw : ∀ i ∈ Finset.range 3, w i = 0 ∨ t.HasPrimitiveVectorWith (w i) (2 * (i : K))) :
    aeval (toEnd K L M f * toEnd K L M e) (leftPoly : K[X])
      (∑ i ∈ Finset.range 3, ((toEnd K L M f) ^ i) (w i)) = w 0 := by
  have key := leftPoly_apply (toEnd K L M f * toEnd K L M e)
    (fun i => ((toEnd K L M f) ^ i) (w i)) (fun i hi => by
      have hfe := fe_pow_f_of_primitive_or_zero (t := t) (w i) (2 * (i : K)) i (hw i hi)
      rwa [show (2 * (i : K)) - 2 * (i : K) = 0 by ring] at hfe)
  simpa using key

/-- The right projector on the weight-two vectors `f^i w_i`, where each `w_i` is zero or a
primitive vector of weight `2 + 2i` (`i ∈ {0,…,11}`), returns `w_0`. -/
theorem rightPoly_apply_primitive (w : ℕ → M)
    (hw : ∀ i ∈ Finset.range 12,
      w i = 0 ∨ t.HasPrimitiveVectorWith (w i) (2 + 2 * (i : K))) :
    aeval (toEnd K L M f * toEnd K L M e) (rightPoly : K[X])
      (∑ i ∈ Finset.range 12, ((toEnd K L M f) ^ i) (w i)) = w 0 := by
  have key := rightPoly_apply (toEnd K L M f * toEnd K L M e)
    (fun i => ((toEnd K L M f) ^ i) (w i)) (fun i hi => by
      have hfe := fe_pow_f_of_primitive_or_zero (t := t) (w i) (2 + 2 * (i : K)) i (hw i hi)
      rwa [show (2 + 2 * (i : K)) - 2 * (i : K) = 2 by ring] at hfe)
  simpa using key

end PrimitiveProjector

#print axioms lie_f_lie_e_pow_toEnd_f
#print axioms casimir_primitive_smul
#print axioms fePoly_apply_sum
#print axioms leftPoly_denom_ne_zero
#print axioms rightPoly_denom_ne_zero
#print axioms singlet_denom_ne_zero
#print axioms leftPoly_factor_kills
#print axioms rightPoly_factor_kills
#print axioms leftPoly_apply
#print axioms rightPoly_apply
#print axioms singletLeftPoly_apply
#print axioms singletRightPoly_apply
#print axioms singletProjector_apply
#print axioms singlet_recovery
#print axioms singlet_recovery_of_normal
#print axioms fe_pow_f_eq_feScalar
#print axioms leftPoly_apply_primitive
#print axioms rightPoly_apply_primitive

end Sl2
end HaagerupIzumi.C8
