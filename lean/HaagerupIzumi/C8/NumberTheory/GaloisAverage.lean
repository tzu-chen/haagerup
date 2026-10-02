module

public import HaagerupIzumi.C8.NumberTheory.MultiplicityOne
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Galois averaging for sums of roots of unity

General infrastructure for Lemma `lem:conductor40` (manuscript lines 3950–3995, statement
3950–3955) and the Galois-orbit step of Lemma `lem:six-residual-twists` (lines 4025–4039 of the
lemma 4019–4051).  Everything here is
proved; there are no hypotheses.  The argument avoids abstract Galois groups, Ramanujan sums
and imprimitive Gauss sums: conjugation is realized by substituting `ζ ↦ ζ^j` in a rational
polynomial, and the needed orbit sums are evaluated by elementary reindexing.

Notation: `zetaN n = exp(2πi/n)`; for `j : (ℤ/N)ˣ` the power `z^j` means `z ^ j.val`.  A
*real character of conductor `c`* (`IsRealChar c χ`) is a function `χ : ℕ → ℤ`, periodic modulo
`c`, multiplicative and `±1` on integers prime to `c`, which is *primitive*: for every proper
divisor `d` of `c` some `e ≡ 1 (mod d)` prime to `c` has `χ(e) = -1`.  Its Gauss sum is
`gaussSumC c χ = ∑_{i ∈ (ℤ/c)ˣ} χ(i) ζ_c^i`, and `primSum c = ∑_{i ∈ (ℤ/c)ˣ} ζ_c^i`.

* (A) `aeval_pow_eq_zero_of_coprime`, `conj_sum`: if `P ∈ ℚ[X]` vanishes at a primitive `N`-th
  root `ζ`, it vanishes at `ζ^j` for `j` prime to `N` (the minimal polynomial of `ζ` is `Φ_N`).
  Consequently, if a multiset `s` of `N`-th roots of unity has sum `r₀ + r₁ G` (`r₀, r₁ ∈ ℚ`,
  `G` the Gauss sum), then `∑_{z∈s} z^j = r₀ + r₁ χ(j) G` for every `j` prime to `N`
  (`gauss_twist`: `∑_i χ(i) ζ_c^{ji} = χ(j) G`).
* (B) `trace_identities`: with the twisted traces `T(z) = ∑_{j∈(ℤ/N)ˣ} z^j` and
  `S(z) = ∑_{j∈(ℤ/N)ˣ} χ(j) z^j` (`wtrace`), `∑_{z∈s} T(z) = r₀ φ(N)` and
  `∑_{z∈s} S(z) = r₁ G φ(N)`.
* (C) `wtrace_cases`, the pointwise evaluation, from
  - the fibre lemma `sum_comp_unitsMap` (the reduction `(ℤ/N)ˣ → (ℤ/n)ˣ` is a surjective
    homomorphism, so its fibres have equal size);
  - shift vanishing `sum_units_shift_eq_zero`, `wtrace_eq_zero_of_sq_dvd` (if `p² ∣ ord z`, the
    translation `i ↦ i + n/p` permutes `(ℤ/n)ˣ` since `(n/p)² ≡ 0`, and multiplies `z^i` by
    `z^{n/p} ≠ 1`);
  - character twist vanishing `wtrace_char_eq_zero_of_not_dvd` (if `c ∤ ord z`, a unit
    `e ≡ 1 (mod ord z)` with `χ(e) = -1` exists by primitivity and the Chinese remainder
    theorem);
  - the CRT product `sum_units_mul_crt` (`(ℤ/cu)ˣ ≅ (ℤ/c)ˣ × (ℤ/u)ˣ` for coprime `c, u`).
  Result: either `S(z) = 0` (and `T(z) = 0` when `c ∣ ord z`), or `z = ζ_c^w z₂` with `w` prime
  to `c`, `z₂^u = 1`, `u` prime to `c`, and `S(z) = K χ(w) G R_u(z₂)`,
  `T(z) = K · primSum c · R_u(z₂)`,
  where `R_u(z₂) = ∑_{k<u, (k,u)=1} z₂^k` (`unitSum`) and `K φ(c) φ(u) = φ(N)`.
* Real-part bounds: `neg_card_le_re_sum`, `forall_eq_neg_one_of_re_sum`, `unitSum_bound`,
  `wtrace_one_bound` (a sum of `m` complex numbers of modulus one has real part `≥ -m`, with
  equality only if every term is `-1`).
-/

namespace HaagerupIzumi.C8.NumberTheory

open Polynomial

/-! ### Exponents modulo `n` -/

theorem pow_eq_pow_of_modEq {z : ℂ} {n a b : ℕ} (hz : z ^ n = 1) (h : a ≡ b [MOD n]) :
    z ^ a = z ^ b := by
  have h' : a % n = b % n := h
  calc z ^ a = z ^ (a % n + n * (a / n)) := by rw [Nat.mod_add_div]
    _ = z ^ (b % n + n * (b / n)) := by
        rw [pow_add, pow_add, pow_mul, pow_mul, hz, one_pow, one_pow, h']
    _ = z ^ b := by rw [Nat.mod_add_div]

theorem pow_val_natCast {z : ℂ} {n : ℕ} (hz : z ^ n = 1) (k : ℕ) :
    z ^ (k : ZMod n).val = z ^ k := by
  apply pow_eq_pow_of_modEq hz
  rw [ZMod.val_natCast]
  exact Nat.mod_modEq k n

theorem val_modEq_of_eq {n : ℕ} {a : ZMod n} {k : ℕ} (h : a = (k : ZMod n)) :
    a.val ≡ k [MOD n] := by
  rw [h, ZMod.val_natCast]
  exact Nat.mod_modEq k n

theorem val_units_mul_modEq {n : ℕ} [NeZero n] (a b : (ZMod n)ˣ) :
    ((a * b : (ZMod n)ˣ) : ZMod n).val ≡ (a : ZMod n).val * (b : ZMod n).val [MOD n] := by
  apply val_modEq_of_eq
  rw [Units.val_mul, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem unitsMap_val_modEq {N n : ℕ} [NeZero N] (h : n ∣ N) (j : (ZMod N)ˣ) :
    ((ZMod.unitsMap h j : (ZMod n)ˣ) : ZMod n).val ≡ (j : ZMod N).val [MOD n] := by
  apply val_modEq_of_eq
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]

/-- Every residue prime to `d ∣ N` lifts to a unit modulo `N`. -/
theorem exists_unit_modEq {N d : ℕ} [NeZero N] (hd : d ∣ N) {k : ℕ} (hk : k.Coprime d) :
    ∃ E : (ZMod N)ˣ, (E : ZMod N).val ≡ k [MOD d] := by
  obtain ⟨E, hE⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime k hk)
  refine ⟨E, (unitsMap_val_modEq hd E).symm.trans ?_⟩
  rw [hE, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  exact Nat.mod_modEq k d

/-- Sums over `(ℤ/c)ˣ` as sums over `{k < c : (k, c) = 1}`. -/
theorem sum_units_eq_sum_coprime {c : ℕ} [NeZero c] (f : ℕ → ℂ) :
    ∑ i : (ZMod c)ˣ, f (i : ZMod c).val = ∑ k ∈ (Finset.range c).filter c.Coprime, f k := by
  refine Finset.sum_bij' (fun i _ => (i : ZMod c).val)
    (fun k hk => ZMod.unitOfCoprime k (Finset.mem_filter.mp hk).2.symm) ?_ ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _), (ZMod.val_coe_unit_coprime i).symm⟩
  · intro k _
    exact Finset.mem_univ _
  · intro i _
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
  · intro k hk
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  · intro i _
    rfl

/-! ### Roots of unity `exp(2πi/n)` -/

/-- `ζ_n = exp(2πi/n)`. -/
noncomputable def zetaN (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem zetaN_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (zetaN n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

theorem zetaN_pow_div {c N : ℕ} (hc : 0 < c) (hN : 0 < N) (h : c ∣ N) :
    zetaN N ^ (N / c) = zetaN c := by
  obtain ⟨k, rfl⟩ := h
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hN
      exact absurd hN (lt_irrefl 0)
    · exact h
  rw [Nat.mul_div_cancel_left k hc]
  unfold zetaN
  rw [← Complex.exp_nat_mul]
  congr 1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-! ### (A) The conjugation principle -/

/-- If a rational polynomial vanishes at a primitive `N`-th root of unity `ζ`, it vanishes at
`ζ^j` for every `j` prime to `N` (the minimal polynomial of `ζ` over `ℚ` is `Φ_N`). -/
theorem aeval_pow_eq_zero_of_coprime {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {P : ℚ[X]} (hP : aeval ζ P = 0) {j : ℕ} (hj : j.Coprime N) : aeval (ζ ^ j) P = 0 := by
  have hdvd : minpoly ℚ ζ ∣ P := minpoly.dvd ℚ ζ hP
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hN] at hdvd
  obtain ⟨Q, rfl⟩ := hdvd
  have hroot : aeval (ζ ^ j) (cyclotomic N ℚ) = 0 := by
    have h2 : IsPrimitiveRoot (ζ ^ j) N := hζ.pow_of_coprime j hj
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact h2.isRoot_cyclotomic hN
  rw [map_mul, hroot, zero_mul]

/-- A real primitive character of conductor `c`, as a function on `ℕ`. -/
structure IsRealChar (c : ℕ) (χ : ℕ → ℤ) : Prop where
  periodic : ∀ x y, x ≡ y [MOD c] → χ x = χ y
  mul : ∀ x y, x.Coprime c → y.Coprime c → χ (x * y) = χ x * χ y
  sq : ∀ x, x.Coprime c → χ x * χ x = 1
  primitive : ∀ d, d ∣ c → d ≠ c → ∃ e, e.Coprime c ∧ e ≡ 1 [MOD d] ∧ χ e = -1

/-- The Gauss sum `∑_{i ∈ (ℤ/c)ˣ} χ(i) ζ_c^i`. -/
noncomputable def gaussSumC (c : ℕ) [NeZero c] (χ : ℕ → ℤ) : ℂ :=
  ∑ i : (ZMod c)ˣ, (χ (i : ZMod c).val : ℂ) * zetaN c ^ (i : ZMod c).val

/-- The sum of the primitive `c`-th roots of unity, `∑_{i ∈ (ℤ/c)ˣ} ζ_c^i`. -/
noncomputable def primSum (c : ℕ) [NeZero c] : ℂ :=
  ∑ i : (ZMod c)ˣ, zetaN c ^ (i : ZMod c).val

/-- Reindexing a sum over `(ℤ/c)ˣ` by a unit `w`. -/
theorem sum_units_reindex {c : ℕ} [NeZero c] (F : ℕ → ℂ)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y) {w : ℕ} (hw : w.Coprime c) :
    ∑ i : (ZMod c)ˣ, F (w * (i : ZMod c).val) = ∑ i : (ZMod c)ˣ, F (i : ZMod c).val :=
  Fintype.sum_bijective (ZMod.unitOfCoprime w hw * ·) (Group.mulLeft_bijective _) _ _ fun i => by
    show F (w * (i : ZMod c).val) = F ((ZMod.unitOfCoprime w hw * i : (ZMod c)ˣ) : ZMod c).val
    apply hF
    apply Nat.ModEq.symm
    apply val_modEq_of_eq
    rw [Units.val_mul, ZMod.coe_unitOfCoprime, Nat.cast_mul, ZMod.natCast_zmod_val]

/-- **Twisting the Gauss sum**: `∑_i χ(i) ζ_c^{ji} = χ(j) G` for `j` prime to `c`. -/
theorem gauss_twist {c : ℕ} [NeZero c] {χ : ℕ → ℤ} (hχ : IsRealChar c χ) {j : ℕ}
    (hj : j.Coprime c) :
    ∑ i : (ZMod c)ˣ, (χ (i : ZMod c).val : ℂ) * zetaN c ^ (j * (i : ZMod c).val) =
      χ j * gaussSumC c χ := by
  have hc : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hζ := (zetaN_isPrimitiveRoot hc).pow_eq_one
  have h1 : ∑ i : (ZMod c)ˣ, (χ (j * (i : ZMod c).val) : ℂ) * zetaN c ^ (j * (i : ZMod c).val) =
      gaussSumC c χ :=
    sum_units_reindex (fun x => (χ x : ℂ) * zetaN c ^ x)
      (fun x y h => by
        show (χ x : ℂ) * zetaN c ^ x = (χ y : ℂ) * zetaN c ^ y
        rw [hχ.periodic x y h, pow_eq_pow_of_modEq hζ h]) hj
  have h2 : gaussSumC c χ = (χ j : ℂ) *
      ∑ i : (ZMod c)ˣ, (χ (i : ZMod c).val : ℂ) * zetaN c ^ (j * (i : ZMod c).val) := by
    rw [← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hχ.mul j _ hj (ZMod.val_coe_unit_coprime i)]
    push_cast
    ring
  have hsq : (χ j : ℂ) * χ j = 1 := by exact_mod_cast hχ.sq j hj
  rw [h2, ← mul_assoc, hsq, one_mul]

/-- **Conjugation of a root-of-unity sum** (manuscript: "the Galois group acts").  If a
multiset of `N`-th roots of unity has sum `r₀ + r₁ G` with `r₀, r₁` rational and `G` the Gauss
sum of a real character of conductor `c ∣ N`, then for every `j` prime to `N` the `j`-th powers
sum to `r₀ + r₁ χ(j) G`. -/
theorem conj_sum {c N : ℕ} [NeZero c] (hN : 0 < N) (hcN : c ∣ N) {χ : ℕ → ℤ}
    (hχ : IsRealChar c χ) (s : Multiset ℂ) (hs : ∀ z ∈ s, z ^ N = 1) (r₀ r₁ : ℚ)
    (hsum : s.sum = r₀ + r₁ * gaussSumC c χ) {j : ℕ} (hj : j.Coprime N) :
    (s.map fun z => z ^ j).sum = r₀ + r₁ * χ j * gaussSumC c χ := by
  have hζ : IsPrimitiveRoot (zetaN N) N := zetaN_isPrimitiveRoot hN
  have : NeZero N := ⟨hN.ne'⟩
  have hex : ∀ z ∈ s, ∃ k : ℕ, zetaN N ^ k = z := fun z hz => by
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (hs z hz)
    exact ⟨k, hk⟩
  choose! ex hex using hex
  have hM : zetaN N ^ (N / c) = zetaN c :=
    zetaN_pow_div (Nat.pos_of_ne_zero (NeZero.ne c)) hN hcN
  let P : ℚ[X] := (s.map fun z => (X : ℚ[X]) ^ ex z).sum - C r₀ -
      C r₁ * ∑ i : (ZMod c)ˣ, C ((χ (i : ZMod c).val : ℤ) : ℚ) * X ^ (N / c * (i : ZMod c).val)
  have heval : ∀ y : ℂ, aeval y P = (s.map fun z => y ^ ex z).sum - r₀ -
      r₁ * ∑ i : (ZMod c)ˣ, (χ (i : ZMod c).val : ℂ) * y ^ (N / c * (i : ZMod c).val) := by
    intro y
    simp only [P, map_sub, map_mul, map_sum, map_multiset_sum, Multiset.map_map,
      Function.comp_def, aeval_X_pow, aeval_C, eq_ratCast, Rat.cast_intCast]
  have hP : aeval (zetaN N) P = 0 := by
    rw [heval]
    have h1 : (s.map fun z => zetaN N ^ ex z) = s := by
      conv_rhs => rw [← Multiset.map_id' s]
      exact Multiset.map_congr rfl hex
    have h2 : ∑ i : (ZMod c)ˣ, (χ (i : ZMod c).val : ℂ) * zetaN N ^ (N / c * (i : ZMod c).val) =
        gaussSumC c χ := by
      unfold gaussSumC
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_mul, hM]
    rw [h1, h2, hsum]
    ring
  have hPj := aeval_pow_eq_zero_of_coprime hN hζ hP hj
  rw [heval] at hPj
  have h1 : (s.map fun z => (zetaN N ^ j) ^ ex z) = s.map fun z => z ^ j :=
    Multiset.map_congr rfl fun z hz => by rw [← pow_mul, mul_comm, pow_mul, hex z hz]
  have h2 : ∑ i : (ZMod c)ˣ, (χ (i : ZMod c).val : ℂ) * (zetaN N ^ j) ^ (N / c * (i : ZMod c).val) =
      χ j * gaussSumC c χ := by
    rw [← gauss_twist hχ (Nat.Coprime.coprime_dvd_right hcN hj)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, ← hM, ← pow_mul,
      show j * (N / c * (i : ZMod c).val) = N / c * (j * (i : ZMod c).val) by ring]
  rw [h1, h2] at hPj
  linear_combination hPj

/-! ### Twisted traces and the fibre lemma -/

/-- The weighted trace `∑_{j ∈ (ℤ/N)ˣ} W(j) z^j`. -/
noncomputable def wtrace (N : ℕ) [NeZero N] (W : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ j : (ZMod N)ˣ, W (j : ZMod N).val * z ^ (j : ZMod N).val

/-- The common size of the fibres of `(ℤ/N)ˣ → (ℤ/n)ˣ`. -/
noncomputable def fibreCard (N n : ℕ) [NeZero N] (h : n ∣ N) : ℕ :=
  (Finset.univ.filter fun j : (ZMod N)ˣ => ZMod.unitsMap h j = 1).card

/-- **Fibre lemma**: `(ℤ/N)ˣ → (ℤ/n)ˣ` is a surjective homomorphism, so every fibre has the
same size. -/
theorem sum_comp_unitsMap {N n : ℕ} [NeZero N] [NeZero n] (h : n ∣ N) (F : (ZMod n)ˣ → ℂ) :
    ∑ j : (ZMod N)ˣ, F (ZMod.unitsMap h j) = (fibreCard N n h : ℂ) * ∑ i, F i := by
  rw [Finset.sum_comp F (ZMod.unitsMap h), Finset.mul_sum]
  have himg : (Finset.univ : Finset (ZMod N)ˣ).image (ZMod.unitsMap h) = Finset.univ :=
    Finset.eq_univ_of_forall fun i => by
      obtain ⟨j, rfl⟩ := ZMod.unitsMap_surjective h i
      exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  rw [himg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap h)
    (Set.mem_range.mpr (ZMod.unitsMap_surjective h i))
    (Set.mem_range.mpr (ZMod.unitsMap_surjective h 1))]
  rfl

theorem totient_eq_fibreCard_mul {N n : ℕ} [NeZero N] [NeZero n] (h : n ∣ N) :
    Nat.totient N = fibreCard N n h * Nat.totient n := by
  have := sum_comp_unitsMap h (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ZMod.card_units_eq_totient] at this
  exact_mod_cast this

/-- Passing from level `N` to the level `n` of the root (`W` periodic modulo `m ∣ n`). -/
theorem wtrace_eq_fibre {N n m : ℕ} [NeZero N] [NeZero n] (h : n ∣ N) {z : ℂ}
    (hz : z ^ n = 1) (W : ℕ → ℂ) (hW : ∀ x y, x ≡ y [MOD m] → W x = W y) (hmn : m ∣ n) :
    wtrace N W z = fibreCard N n h *
      ∑ i : (ZMod n)ˣ, W (i : ZMod n).val * z ^ (i : ZMod n).val := by
  unfold wtrace
  rw [← sum_comp_unitsMap h (fun i : (ZMod n)ˣ => W (i : ZMod n).val * z ^ (i : ZMod n).val)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := unitsMap_val_modEq h j
  show W (j : ZMod N).val * z ^ (j : ZMod N).val =
    W ((ZMod.unitsMap h j : (ZMod n)ˣ) : ZMod n).val *
      z ^ ((ZMod.unitsMap h j : (ZMod n)ˣ) : ZMod n).val
  rw [hW _ _ (hj.of_dvd hmn), pow_eq_pow_of_modEq hz hj]

/-! ### (C2) Shift vanishing -/

/-- Translation by a square-zero element of `ℤ/n` maps units to units. -/
def shiftUnit {n : ℕ} (H : ZMod n) (hH : H * H = 0) (i : (ZMod n)ˣ) : (ZMod n)ˣ where
  val := (i : ZMod n) + H
  inv := ((i⁻¹ : (ZMod n)ˣ) : ZMod n) - ((i⁻¹ : (ZMod n)ˣ) : ZMod n) *
    ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * H
  val_inv := by
    have h1 : (i : ZMod n) * ((i⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv i
    linear_combination (1 - ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * H) * h1 -
      ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * hH
  inv_val := by
    have h1 : (i : ZMod n) * ((i⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv i
    linear_combination (1 - ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * H) * h1 -
      ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * ((i⁻¹ : (ZMod n)ˣ) : ZMod n) * hH

theorem shiftUnit_val {n : ℕ} (H : ZMod n) (hH : H * H = 0) (i : (ZMod n)ˣ) :
    (shiftUnit H hH i : ZMod n) = i + H := rfl

/-- Translation by a square-zero element permutes the units. -/
def shiftEquiv {n : ℕ} (H : ZMod n) (hH : H * H = 0) : (ZMod n)ˣ ≃ (ZMod n)ˣ where
  toFun := shiftUnit H hH
  invFun := shiftUnit (-H) (by rw [neg_mul_neg]; exact hH)
  left_inv i := Units.ext (by rw [shiftUnit_val, shiftUnit_val]; ring)
  right_inv i := Units.ext (by rw [shiftUnit_val, shiftUnit_val]; ring)

theorem shiftEquiv_val {n : ℕ} (H : ZMod n) (hH : H * H = 0) (i : (ZMod n)ˣ) :
    ((shiftEquiv H hH i : (ZMod n)ˣ) : ZMod n) = i + H := rfl

/-- **Shift vanishing** at level `n`: if `n ∣ h²`, `z^h ≠ 1` and `W` is periodic modulo
`m ∣ h`, then `∑_{i ∈ (ℤ/n)ˣ} W(i) z^i = 0`. -/
theorem sum_units_shift_eq_zero {n m h : ℕ} [NeZero n] {z : ℂ} (hz : z ^ n = 1)
    (hzh : z ^ h ≠ 1) (hhh : n ∣ h * h) (W : ℕ → ℂ) (hW : ∀ x y, x ≡ y [MOD m] → W x = W y)
    (hmh : m ∣ h) (hmn : m ∣ n) :
    ∑ i : (ZMod n)ˣ, W (i : ZMod n).val * z ^ (i : ZMod n).val = 0 := by
  have hH : (h : ZMod n) * (h : ZMod n) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact hhh
  have key : ∑ i : (ZMod n)ˣ, z ^ h * (W (i : ZMod n).val * z ^ (i : ZMod n).val) =
      ∑ i : (ZMod n)ˣ, W (i : ZMod n).val * z ^ (i : ZMod n).val :=
    Fintype.sum_bijective (shiftEquiv (h : ZMod n) hH) (shiftEquiv (h : ZMod n) hH).bijective
      _ _ fun i => by
        show z ^ h * (W (i : ZMod n).val * z ^ (i : ZMod n).val) =
          W ((shiftEquiv (h : ZMod n) hH i : (ZMod n)ˣ) : ZMod n).val *
            z ^ ((shiftEquiv (h : ZMod n) hH i : (ZMod n)ˣ) : ZMod n).val
        have hv : ((shiftEquiv (h : ZMod n) hH i : (ZMod n)ˣ) : ZMod n).val ≡
            (i : ZMod n).val + h [MOD n] := by
          apply val_modEq_of_eq
          rw [shiftEquiv_val, Nat.cast_add, ZMod.natCast_zmod_val]
        have hm' : (i : ZMod n).val + h ≡ (i : ZMod n).val [MOD m] := by
          have := (Nat.modEq_zero_iff_dvd.mpr hmh).add_left (i : ZMod n).val
          rwa [add_zero] at this
        rw [hW _ _ (hv.of_dvd hmn), hW _ _ hm', pow_eq_pow_of_modEq hz hv, pow_add]
        ring
  rw [← Finset.mul_sum] at key
  have h2 : (z ^ h - 1) * ∑ i : (ZMod n)ˣ, W (i : ZMod n).val * z ^ (i : ZMod n).val = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hzh
  · exact h3

/-- **Shift vanishing** at level `N`: if `z` is a primitive `n`-th root, `p² ∣ n` (`p > 1`) and
`W` is periodic modulo `m ∣ n/p`, the weighted trace vanishes. -/
theorem wtrace_eq_zero_of_sq_dvd {N n m p : ℕ} [NeZero N] (hnN : n ∣ N) {z : ℂ}
    (hz : IsPrimitiveRoot z n) (hp : 1 < p) (hpn : p * p ∣ n) (W : ℕ → ℂ)
    (hW : ∀ x y, x ≡ y [MOD m] → W x = W y) (hm : m ∣ n / p) : wtrace N W z = 0 := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hnN (Nat.pos_of_ne_zero (NeZero.ne N))
  have : NeZero n := ⟨hn0.ne'⟩
  obtain ⟨k, hk⟩ := hpn
  have hp0 : 0 < p := by omega
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hnp : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp0]
  have hmn : m ∣ n := hm.trans ⟨p, by rw [hnp, hk]; ring⟩
  have hz1 : z ^ n = 1 := hz.pow_eq_one
  have hpk : 0 < p * k := Nat.mul_pos hp0 hk0
  have hlt : n / p < n := by
    rw [hnp]
    calc p * k = p * k * 1 := (mul_one _).symm
      _ < p * k * p := Nat.mul_lt_mul_of_pos_left hp hpk
      _ = n := by rw [hk]; ring
  have hzh : z ^ (n / p) ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by rw [hnp]; exact hpk.ne') hlt
  have hnh : n ∣ n / p * (n / p) := ⟨k, by rw [hnp, hk]; ring⟩
  rw [wtrace_eq_fibre hnN hz1 W hW hmn, sum_units_shift_eq_zero hz1 hzh hnh W hW hm hmn,
    mul_zero]

/-! ### (C3) Character twist vanishing -/

/-- If some unit `E` fixes `z` (`z^E = z`) and has `χ(E) = -1`, the `χ`-trace of `z`
vanishes. -/
theorem wtrace_char_eq_zero_of_unit {c N : ℕ} [NeZero N] (hcN : c ∣ N) {χ : ℕ → ℤ}
    (hχ : IsRealChar c χ) {z : ℂ} (hz : z ^ N = 1) (E : (ZMod N)ˣ)
    (hzE : z ^ (E : ZMod N).val = z) (hχE : χ (E : ZMod N).val = -1) :
    wtrace N (fun x => (χ x : ℂ)) z = 0 := by
  have key : ∑ j : (ZMod N)ˣ, -((χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val) =
      ∑ j : (ZMod N)ˣ, (χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val :=
    Fintype.sum_bijective (E * ·) (Group.mulLeft_bijective E) _ _ fun j => by
      show -((χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val) =
        (χ ((E * j : (ZMod N)ˣ) : ZMod N).val : ℂ) * z ^ ((E * j : (ZMod N)ˣ) : ZMod N).val
      have hv := val_units_mul_modEq E j
      have hEc : (E : ZMod N).val.Coprime c :=
        Nat.Coprime.coprime_dvd_right hcN (ZMod.val_coe_unit_coprime E)
      have hjc : (j : ZMod N).val.Coprime c :=
        Nat.Coprime.coprime_dvd_right hcN (ZMod.val_coe_unit_coprime j)
      rw [hχ.periodic _ _ (hv.of_dvd hcN), hχ.mul _ _ hEc hjc, hχE, pow_eq_pow_of_modEq hz hv,
        pow_mul, hzE]
      push_cast
      ring
  rw [Finset.sum_neg_distrib] at key
  show ∑ j : (ZMod N)ˣ, (χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val = 0
  linear_combination (-1 / 2 : ℂ) * key

/-- **Character twist vanishing**: if `z^m = 1` with `m ∣ N` and `c ∤ m`, then
`∑_{j ∈ (ℤ/N)ˣ} χ(j) z^j = 0`. -/
theorem wtrace_char_eq_zero_of_not_dvd {c N m : ℕ} [NeZero N] (hcN : c ∣ N) {χ : ℕ → ℤ}
    (hχ : IsRealChar c χ) {z : ℂ} (hz : z ^ N = 1) (hmN : m ∣ N) (hzm : z ^ m = 1)
    (hcm : ¬ c ∣ m) : wtrace N (fun x => (χ x : ℂ)) z = 0 := by
  have hdc : Nat.gcd m c ∣ c := Nat.gcd_dvd_right m c
  have hdne : Nat.gcd m c ≠ c := fun h => hcm (by rw [← h]; exact Nat.gcd_dvd_left m c)
  obtain ⟨e₀, he₀c, he₀1, hχe₀⟩ := hχ.primitive _ hdc hdne
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' (he₀1.symm : 1 ≡ e₀ [MOD Nat.gcd m c])
  have hkm : k.Coprime m := by
    show Nat.gcd k m = 1
    rw [hk1.gcd_eq]
    exact Nat.gcd_one_left m
  have hkc : k.Coprime c := by
    show Nat.gcd k c = 1
    rw [hk2.gcd_eq]
    exact he₀c
  have hL : Nat.lcm m c ∣ N := Nat.lcm_dvd hmN hcN
  have hkL : k.Coprime (Nat.lcm m c) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul m c) (Nat.Coprime.mul_right hkm hkc)
  obtain ⟨E, hE⟩ := exists_unit_modEq hL hkL
  refine wtrace_char_eq_zero_of_unit hcN hχ hz E ?_ ?_
  · rw [pow_eq_pow_of_modEq hzm ((hE.of_dvd (Nat.dvd_lcm_left m c)).trans hk1), pow_one]
  · rw [hχ.periodic _ _ ((hE.of_dvd (Nat.dvd_lcm_right m c)).trans hk2), hχe₀]

/-- `∑_{j ∈ (ℤ/N)ˣ} χ(j) = 0` for a real primitive character of conductor `c ≠ 1`. -/
theorem sum_char_units_eq_zero {c N : ℕ} [NeZero N] (hcN : c ∣ N) (hc1 : c ≠ 1)
    {χ : ℕ → ℤ} (hχ : IsRealChar c χ) : ∑ j : (ZMod N)ˣ, (χ (j : ZMod N).val : ℂ) = 0 := by
  have h := wtrace_char_eq_zero_of_not_dvd hcN hχ (one_pow N) (one_dvd N) (one_pow 1)
    (fun h => hc1 (Nat.dvd_one.mp h))
  simpa [wtrace] using h

/-! ### (C4) The Chinese remainder product -/

/-- `(ℤ/cu)ˣ → (ℤ/c)ˣ × (ℤ/u)ˣ`. -/
noncomputable def crtUnitsHom (c u : ℕ) : (ZMod (c * u))ˣ →* (ZMod c)ˣ × (ZMod u)ˣ :=
  (ZMod.unitsMap (Nat.dvd_mul_right c u)).prod (ZMod.unitsMap (Nat.dvd_mul_left u c))

theorem crtUnitsHom_bijective {c u : ℕ} [NeZero c] [NeZero u] (hcu : c.Coprime u) :
    Function.Bijective (crtUnitsHom c u) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i i' hii
    simp only [crtUnitsHom, MonoidHom.prod_apply, Prod.mk.injEq] at hii
    obtain ⟨h1, h2⟩ := hii
    have e1 := unitsMap_val_modEq (Nat.dvd_mul_right c u) i
    have e1' := unitsMap_val_modEq (Nat.dvd_mul_right c u) i'
    rw [h1] at e1
    have e2 := unitsMap_val_modEq (Nat.dvd_mul_left u c) i
    have e2' := unitsMap_val_modEq (Nat.dvd_mul_left u c) i'
    rw [h2] at e2
    have hcu' := (Nat.modEq_and_modEq_iff_modEq_mul hcu).mp
      ⟨e1.symm.trans e1', e2.symm.trans e2'⟩
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (i : ZMod (c * u)), ← ZMod.natCast_zmod_val (i' : ZMod (c * u))]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcu'
  · simp only [Fintype.card_prod, ZMod.card_units_eq_totient]
    exact Nat.totient_mul hcu

/-- **CRT product**: for coprime `c, u`, a sum over `(ℤ/cu)ˣ` of a product of a function
periodic modulo `c` and one periodic modulo `u` factors. -/
theorem sum_units_mul_crt {c u : ℕ} [NeZero c] [NeZero u] (hcu : c.Coprime u) (F G : ℕ → ℂ)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y) (hG : ∀ x y, x ≡ y [MOD u] → G x = G y) :
    ∑ i : (ZMod (c * u))ˣ, F (i : ZMod (c * u)).val * G (i : ZMod (c * u)).val =
      (∑ a : (ZMod c)ˣ, F (a : ZMod c).val) * ∑ b : (ZMod u)ˣ, G (b : ZMod u).val := by
  symm
  calc (∑ a : (ZMod c)ˣ, F (a : ZMod c).val) * ∑ b : (ZMod u)ˣ, G (b : ZMod u).val
      = ∑ q : (ZMod c)ˣ × (ZMod u)ˣ, F (q.1 : ZMod c).val * G (q.2 : ZMod u).val := by
        rw [Fintype.sum_mul_sum]
        exact (Fintype.sum_prod_type' (fun (a : (ZMod c)ˣ) (b : (ZMod u)ˣ) =>
          F (a : ZMod c).val * G (b : ZMod u).val)).symm
    _ = ∑ i : (ZMod (c * u))ˣ, F ((crtUnitsHom c u i).1 : ZMod c).val *
          G ((crtUnitsHom c u i).2 : ZMod u).val :=
        (Fintype.sum_bijective (crtUnitsHom c u) (crtUnitsHom_bijective hcu) _ _
          fun _ => rfl).symm
    _ = ∑ i : (ZMod (c * u))ˣ, F (i : ZMod (c * u)).val * G (i : ZMod (c * u)).val := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have e1 : ((crtUnitsHom c u i).1 : ZMod c).val ≡ (i : ZMod (c * u)).val [MOD c] :=
          unitsMap_val_modEq (Nat.dvd_mul_right c u) i
        have e2 : ((crtUnitsHom c u i).2 : ZMod u).val ≡ (i : ZMod (c * u)).val [MOD u] :=
          unitsMap_val_modEq (Nat.dvd_mul_left u c) i
        rw [hF _ _ e1, hG _ _ e2]

/-! ### Sums of moduli-one terms -/

/-- `R_u(z) = ∑_{k < u, (k, u) = 1} z^k`. -/
noncomputable def unitSum (u : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ (Finset.range u).filter u.Coprime, z ^ k

theorem unitSum_eq {u : ℕ} [NeZero u] (z : ℂ) :
    unitSum u z = ∑ b : (ZMod u)ˣ, z ^ (b : ZMod u).val :=
  (sum_units_eq_sum_coprime (fun k => z ^ k)).symm

theorem card_filter_coprime (u : ℕ) :
    ((Finset.range u).filter u.Coprime).card = Nat.totient u :=
  (Nat.totient_eq_card_coprime u).symm

theorem neg_card_le_re_sum {ι : Type*} (t : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ t, ‖f i‖ = 1) :
    -(t.card : ℝ) ≤ (∑ i ∈ t, f i).re := by
  rw [Complex.re_sum]
  calc -(t.card : ℝ) = ∑ i ∈ t, (-1 : ℝ) := by simp
    _ ≤ ∑ i ∈ t, (f i).re := Finset.sum_le_sum fun i hi => by
        have h1 := Complex.abs_re_le_norm (f i)
        rw [hf i hi] at h1
        linarith [neg_abs_le (f i).re]

theorem eq_neg_one_of_norm_of_re {x : ℂ} (hx : ‖x‖ = 1) (hre : x.re = -1) : x = -1 := by
  have h := Complex.sq_norm_sub_sq_re x
  rw [hx, hre] at h
  have h2 : x.im ^ 2 = 0 := by linarith
  have him : x.im = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  exact Complex.ext (by simp [hre]) (by simp [him])

theorem forall_eq_neg_one_of_re_sum {ι : Type*} (t : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ t, ‖f i‖ = 1) (h : (∑ i ∈ t, f i).re = -(t.card : ℝ)) :
    ∀ i ∈ t, f i = -1 := by
  rw [Complex.re_sum] at h
  have hle : ∀ i ∈ t, (-1 : ℝ) ≤ (f i).re := fun i hi => by
    have h1 := Complex.abs_re_le_norm (f i)
    rw [hf i hi] at h1
    linarith [neg_abs_le (f i).re]
  have hsum : ∑ i ∈ t, (-1 : ℝ) = ∑ i ∈ t, (f i).re := by
    rw [h]
    simp
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  exact fun i hi => eq_neg_one_of_norm_of_re (hf i hi) (hall i hi).symm

theorem exists_mem_coprime_pow_eq {u : ℕ} (hu : 0 < u) {z : ℂ} (hz : z ^ u = 1) :
    ∃ k ∈ (Finset.range u).filter u.Coprime, z ^ k = z := by
  refine ⟨1 % u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hu), ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge 1 u with h | h
    · rw [Nat.mod_eq_of_lt h]
      exact Nat.coprime_one_right u
    · obtain rfl : u = 1 := by omega
      exact Nat.coprime_one_left _
  · rw [pow_eq_pow_of_modEq hz (Nat.mod_modEq 1 u), pow_one]

/-- `Re(ε R_u(z)) ≥ -φ(u)` for `|ε| = 1`, with equality only if `ε z = -1`, and then
`ε R_u(z) = -φ(u)`. -/
theorem unitSum_bound {u : ℕ} (hu : 0 < u) {z : ℂ} (hz : z ^ u = 1) {ε : ℂ} (hε : ‖ε‖ = 1) :
    -(Nat.totient u : ℝ) ≤ (ε * unitSum u z).re ∧
      ((ε * unitSum u z).re = -(Nat.totient u : ℝ) →
        ε * z = -1 ∧ ε * unitSum u z = -(Nat.totient u : ℂ)) := by
  have hnorm : ∀ k ∈ (Finset.range u).filter u.Coprime, ‖ε * z ^ k‖ = 1 := fun k _ => by
    rw [norm_mul, norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hu.ne', hε, one_pow, one_mul]
  have hsum : ε * unitSum u z = ∑ k ∈ (Finset.range u).filter u.Coprime, ε * z ^ k := by
    rw [unitSum, Finset.mul_sum]
  rw [hsum]
  refine ⟨?_, fun heq => ?_⟩
  · have := neg_card_le_re_sum _ _ hnorm
    rwa [card_filter_coprime] at this
  · have hall := forall_eq_neg_one_of_re_sum _ _ hnorm (by rw [card_filter_coprime]; exact heq)
    obtain ⟨k, hk, hzk⟩ := exists_mem_coprime_pow_eq hu hz
    refine ⟨?_, ?_⟩
    · have := hall k hk
      rwa [hzk] at this
    · rw [Finset.sum_congr rfl hall, Finset.sum_const, card_filter_coprime, nsmul_eq_mul]
      ring

/-- `Re T(z) ≥ -φ(N)`, with equality only for `z = -1`, and then `T(z) = -φ(N)`. -/
theorem wtrace_one_bound {N : ℕ} [NeZero N] {z : ℂ} (hz : z ^ N = 1) :
    -(Nat.totient N : ℝ) ≤ (wtrace N (fun _ => 1) z).re ∧
      ((wtrace N (fun _ => 1) z).re = -(Nat.totient N : ℝ) →
        z = -1 ∧ wtrace N (fun _ => 1) z = -(Nat.totient N : ℂ)) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hnorm : ∀ j ∈ (Finset.univ : Finset (ZMod N)ˣ), ‖(1 : ℂ) * z ^ (j : ZMod N).val‖ = 1 :=
    fun j _ => by rw [one_mul, norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hN, one_pow]
  have hcard : ((Finset.univ : Finset (ZMod N)ˣ).card : ℝ) = Nat.totient N := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient]
  have hw : wtrace N (fun _ => 1) z = ∑ j : (ZMod N)ˣ, (1 : ℂ) * z ^ (j : ZMod N).val := rfl
  rw [hw]
  refine ⟨?_, fun heq => ?_⟩
  · have := neg_card_le_re_sum Finset.univ _ hnorm
    rwa [hcard] at this
  · have hall := forall_eq_neg_one_of_re_sum Finset.univ _ hnorm (by rw [hcard]; exact heq)
    refine ⟨?_, ?_⟩
    · have h1 := hall 1 (Finset.mem_univ _)
      have h2 : z ^ ((1 : (ZMod N)ˣ) : ZMod N).val = z := by
        rw [Units.val_one]
        have := pow_val_natCast hz 1
        rwa [Nat.cast_one, pow_one] at this
      rwa [one_mul, h2] at h1
    · rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_univ,
        ZMod.card_units_eq_totient, nsmul_eq_mul]
      ring

/-! ### Multisets -/

theorem multiset_sum_finset_sum {ι : Type*} (s : Multiset ℂ) (t : Finset ι) (f : ι → ℂ → ℂ) :
    (s.map fun z => ∑ j ∈ t, f j z).sum = ∑ j ∈ t, (s.map (f j)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih, Finset.sum_add_distrib]

theorem re_multiset_sum (s : Multiset ℂ) (f : ℂ → ℂ) :
    ((s.map f).sum).re = (s.map fun z => (f z).re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, ih]

/-- Termwise `f ≤ g` with equal sums forces `f = g` on the multiset. -/
theorem multiset_eq_of_sum_eq {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (hle : ∀ z ∈ s, f z ≤ g z) (heq : (s.map f).sum = (s.map g).sum) : ∀ z ∈ s, f z = g z := by
  induction s using Multiset.induction_on with
  | empty =>
    intro z hz
    simp at hz
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons] at heq
    have ha := hle a (Multiset.mem_cons.mpr (Or.inl rfl))
    have hs : ∀ z ∈ s, f z ≤ g z := fun z hz => hle z (Multiset.mem_cons_of_mem hz)
    have hsum := Multiset.sum_map_le_sum_map f g hs
    have h1 : f a = g a := by linarith
    have h2 : (s.map f).sum = (s.map g).sum := by linarith
    intro z hz
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact h1
    · exact ih hs h2 z hz

/-- A finite multiset of roots of unity has a common period. -/
theorem exists_common_period (s : Multiset ℂ) (h : ∀ z ∈ s, IsRootOfUnity z) :
    ∃ M : ℕ, 0 < M ∧ ∀ z ∈ s, z ^ M = 1 := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, fun z hz => by simp at hz⟩
  | cons a s ih =>
    obtain ⟨M, hM, hMs⟩ := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    obtain ⟨k, hk, hak⟩ := h a (Multiset.mem_cons.mpr (Or.inl rfl))
    refine ⟨k * M, Nat.mul_pos hk hM, fun z hz => ?_⟩
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · rw [pow_mul, hak, one_pow]
    · rw [mul_comm, pow_mul, hMs z hz, one_pow]

/-! ### (B) Trace identities -/

/-- **Trace identities** (B): summing the conjugation principle over `j ∈ (ℤ/N)ˣ`, unweighted
and weighted by `χ(j)`. -/
theorem trace_identities {c N : ℕ} [NeZero c] [NeZero N] (hcN : c ∣ N) (hc1 : c ≠ 1)
    {χ : ℕ → ℤ} (hχ : IsRealChar c χ) (s : Multiset ℂ) (hs : ∀ z ∈ s, z ^ N = 1)
    (r₀ r₁ : ℚ) (hsum : s.sum = r₀ + r₁ * gaussSumC c χ) :
    (s.map (wtrace N fun _ => 1)).sum = r₀ * Nat.totient N ∧
      (s.map (wtrace N fun x => (χ x : ℂ))).sum = r₁ * gaussSumC c χ * Nat.totient N := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hconj : ∀ j : (ZMod N)ˣ, (s.map fun z => z ^ (j : ZMod N).val).sum =
      r₀ + r₁ * χ (j : ZMod N).val * gaussSumC c χ :=
    fun j => conj_sum hN0 hcN hχ s hs r₀ r₁ hsum (ZMod.val_coe_unit_coprime j)
  have hchi := sum_char_units_eq_zero (N := N) hcN hc1 hχ
  have hsq : ∀ j : (ZMod N)ˣ, (χ (j : ZMod N).val : ℂ) * χ (j : ZMod N).val = 1 := fun j => by
    exact_mod_cast hχ.sq _ (Nat.Coprime.coprime_dvd_right hcN (ZMod.val_coe_unit_coprime j))
  have hcard : ∑ _j : (ZMod N)ˣ, (1 : ℂ) = Nat.totient N := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
  constructor
  · have e : (wtrace N fun _ => (1 : ℂ)) =
        fun z => ∑ j : (ZMod N)ˣ, z ^ (j : ZMod N).val := by
      funext z
      simp only [wtrace, one_mul]
    calc (s.map (wtrace N fun _ => 1)).sum
        = ∑ j : (ZMod N)ˣ, (s.map fun z => z ^ (j : ZMod N).val).sum := by
          rw [e]
          exact multiset_sum_finset_sum s Finset.univ
            (fun (j : (ZMod N)ˣ) z => z ^ (j : ZMod N).val)
      _ = ∑ j : (ZMod N)ˣ, ((r₀ : ℂ) + (r₁ * gaussSumC c χ) * χ (j : ZMod N).val) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hconj j]
          ring
      _ = r₀ * Nat.totient N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hchi, mul_zero, add_zero,
            Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
          ring
  · have e : (wtrace N fun x => (χ x : ℂ)) =
        fun z => ∑ j : (ZMod N)ˣ, (χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val := rfl
    calc (s.map (wtrace N fun x => (χ x : ℂ))).sum
        = ∑ j : (ZMod N)ˣ, (s.map fun z => (χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val).sum := by
          rw [e]
          exact multiset_sum_finset_sum s Finset.univ
            (fun (j : (ZMod N)ˣ) z => (χ (j : ZMod N).val : ℂ) * z ^ (j : ZMod N).val)
      _ = ∑ j : (ZMod N)ˣ, ((r₀ : ℂ) * χ (j : ZMod N).val +
            (r₁ * gaussSumC c χ) * ((χ (j : ZMod N).val : ℂ) * χ (j : ZMod N).val)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Multiset.sum_map_mul_left, hconj j]
          ring
      _ = r₁ * gaussSumC c χ * Nat.totient N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hchi,
            Finset.sum_congr rfl fun j _ => hsq j, hcard]
          ring

/-! ### (C) The pointwise structure theorem -/

/-- **Pointwise evaluation of the twisted traces.**  For `z^N = 1` and a real primitive
character `χ` of conductor `c ∣ N`, either `S(z) = 0` (and also `T(z) = 0` when `c ∣ ord z`),
or `z = ζ_c^w z₂` with `w` prime to `c`, `z₂^u = 1`, `u` prime to `c`, and
`S(z) = K χ(w) G R_u(z₂)`, `T(z) = K · primSum c · R_u(z₂)`, `K φ(c) φ(u) = φ(N)`. -/
theorem wtrace_cases {c N : ℕ} [NeZero c] [NeZero N] (hcN : c ∣ N) {χ : ℕ → ℤ}
    (hχ : IsRealChar c χ) {z : ℂ} (hz : z ^ N = 1) :
    (wtrace N (fun x => (χ x : ℂ)) z = 0 ∧ (c ∣ orderOf z → wtrace N (fun _ => 1) z = 0)) ∨
    ∃ w u K : ℕ, ∃ z₂ : ℂ, w < c ∧ w.Coprime c ∧ 0 < u ∧ u.Coprime c ∧ z₂ ^ u = 1 ∧
      z = zetaN c ^ w * z₂ ∧ K * (Nat.totient c * Nat.totient u) = Nat.totient N ∧
      wtrace N (fun x => (χ x : ℂ)) z = K * χ w * gaussSumC c χ * unitSum u z₂ ∧
      wtrace N (fun _ => 1) z = K * primSum c * unitSum u z₂ := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hnN : orderOf z ∣ N := orderOf_dvd_of_pow_eq_one hz
  have hn0 : 0 < orderOf z := Nat.pos_of_dvd_of_pos hnN hN0
  have hzn : IsPrimitiveRoot z (orderOf z) := IsPrimitiveRoot.orderOf z
  by_cases hcn : c ∣ orderOf z
  swap
  · exact Or.inl ⟨wtrace_char_eq_zero_of_not_dvd hcN hχ hz hnN hzn.pow_eq_one hcn,
      fun h => absurd h hcn⟩
  obtain ⟨u, hu⟩ := hcn
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, mul_zero] at hu
      omega
    · exact h
  have : NeZero u := ⟨hu0.ne'⟩
  have hzcu : IsPrimitiveRoot z (c * u) := by rw [← hu]; exact hzn
  have hcuN : c * u ∣ N := by rw [← hu]; exact hnN
  by_cases hcu : c.Coprime u
  · right
    obtain ⟨x, hx1, hx0⟩ := Nat.chineseRemainder hcu 1 0
    obtain ⟨y, hy0, hy1⟩ := Nat.chineseRemainder hcu 0 1
    have hzcu1 : z ^ (c * u) = 1 := hzcu.pow_eq_one
    obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = z ^ x := ⟨_, rfl⟩
    obtain ⟨z₂, hz₂⟩ : ∃ z₂, z₂ = z ^ y := ⟨_, rfl⟩
    have hz₁c : z₁ ^ c = 1 := by
      obtain ⟨x', hx'⟩ : u ∣ x := Nat.modEq_zero_iff_dvd.mp hx0
      rw [hz₁, ← pow_mul, hx', show u * x' * c = c * u * x' by ring, pow_mul, hzcu1, one_pow]
    have hz₂u : z₂ ^ u = 1 := by
      obtain ⟨y', hy'⟩ : c ∣ y := Nat.modEq_zero_iff_dvd.mp hy0
      rw [hz₂, ← pow_mul, hy', show c * y' * u = c * u * y' by ring, pow_mul, hzcu1, one_pow]
    have hz12 : z = z₁ * z₂ := by
      have h1 : x + y ≡ 1 [MOD c] := by
        have := hx1.add hy0
        rwa [add_zero] at this
      have h2 : x + y ≡ 1 [MOD u] := by
        have := hx0.add hy1
        rwa [zero_add] at this
      have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcu).mp ⟨h1, h2⟩
      rw [hz₁, hz₂, ← pow_add, pow_eq_pow_of_modEq hzcu1 h3, pow_one]
    have hz₁prim : IsPrimitiveRoot z₁ c := by
      refine ⟨hz₁c, fun l hl => ?_⟩
      have h1 : c * u ∣ x * l := hzcu.dvd_of_pow_eq_one _ (by rw [pow_mul, ← hz₁]; exact hl)
      have hxc : Nat.Coprime c x := by
        show Nat.gcd c x = 1
        rw [Nat.gcd_comm, hx1.gcd_eq, Nat.gcd_one_left]
      exact hxc.dvd_of_dvd_mul_left (dvd_trans (Nat.dvd_mul_right c u) h1)
    have hζc := zetaN_isPrimitiveRoot hc0
    obtain ⟨w, hwc, hw⟩ := hζc.eq_pow_of_pow_eq_one hz₁c
    have hwcop : w.Coprime c := (hζc.pow_iff_coprime hc0 w).mp (by rw [hw]; exact hz₁prim)
    have hF : ∀ W : ℕ → ℂ, (∀ a b, a ≡ b [MOD c] → W a = W b) →
        wtrace N W z = fibreCard N (c * u) hcuN *
          ((∑ a : (ZMod c)ˣ, W (a : ZMod c).val * z₁ ^ (a : ZMod c).val) * unitSum u z₂) := by
      intro W hW
      rw [wtrace_eq_fibre hcuN hzcu1 W hW (Nat.dvd_mul_right c u)]
      congr 1
      rw [unitSum_eq, ← sum_units_mul_crt hcu (fun k => W k * z₁ ^ k) (fun k => z₂ ^ k)
        (fun a b h => by
          show W a * z₁ ^ a = W b * z₁ ^ b
          rw [hW a b h, pow_eq_pow_of_modEq hz₁c h])
        (fun a b h => pow_eq_pow_of_modEq hz₂u h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      show W (i : ZMod (c * u)).val * z ^ (i : ZMod (c * u)).val =
        W (i : ZMod (c * u)).val * z₁ ^ (i : ZMod (c * u)).val * z₂ ^ (i : ZMod (c * u)).val
      rw [hz12, mul_pow, mul_assoc]
    refine ⟨w, u, fibreCard N (c * u) hcuN, z₂, hwc, hwcop, hu0, hcu.symm, hz₂u, ?_, ?_, ?_, ?_⟩
    · rw [hz12, hw]
    · rw [totient_eq_fibreCard_mul hcuN, Nat.totient_mul hcu]
    · rw [hF (fun x => (χ x : ℂ)) (fun a b h => by
        show (χ a : ℂ) = χ b
        rw [hχ.periodic a b h])]
      have hg : ∑ a : (ZMod c)ˣ, (χ (a : ZMod c).val : ℂ) * z₁ ^ (a : ZMod c).val =
          χ w * gaussSumC c χ := by
        rw [← hw, ← gauss_twist hχ hwcop]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← pow_mul]
      rw [hg]
      ring
    · rw [hF (fun _ => 1) (fun _ _ _ => rfl)]
      have hre : ∑ i : (ZMod c)ˣ, zetaN c ^ (w * (i : ZMod c).val) = primSum c :=
        sum_units_reindex (fun k => zetaN c ^ k)
          (fun a b h => pow_eq_pow_of_modEq hζc.pow_eq_one h) hwcop
      have hg : ∑ a : (ZMod c)ˣ, (1 : ℂ) * z₁ ^ (a : ZMod c).val = primSum c := by
        rw [← hw, ← hre]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [one_mul, ← pow_mul]
      rw [hg]
      ring
  · left
    obtain ⟨p, hp, hpc, hpu⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcu
    have hpp : p * p ∣ c * u := Nat.mul_dvd_mul hpc hpu
    have hcm : c ∣ c * u / p := by
      rw [Nat.mul_div_assoc c hpu]
      exact Nat.dvd_mul_right c _
    refine ⟨wtrace_eq_zero_of_sq_dvd hcuN hzcu hp.one_lt hpp (fun x => (χ x : ℂ))
      (fun x y h => ?_) hcm, fun _ => wtrace_eq_zero_of_sq_dvd (m := 1) hcuN hzcu hp.one_lt hpp
      (fun _ => 1) (fun _ _ _ => rfl) (one_dvd _)⟩
    show (χ x : ℂ) = χ y
    rw [hχ.periodic x y h]

#print axioms aeval_pow_eq_zero_of_coprime
#print axioms gauss_twist
#print axioms conj_sum
#print axioms sum_comp_unitsMap
#print axioms sum_units_shift_eq_zero
#print axioms wtrace_eq_zero_of_sq_dvd
#print axioms wtrace_char_eq_zero_of_not_dvd
#print axioms sum_units_mul_crt
#print axioms unitSum_bound
#print axioms wtrace_one_bound
#print axioms trace_identities
#print axioms wtrace_cases

end HaagerupIzumi.C8.NumberTheory
