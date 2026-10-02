module

public import HaagerupIzumi.C8.NumberTheory.ThirteenOrbit
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section

/-!
# Larson's root count (H. Larson, arXiv:1401.1879, Theorem 1.3 = Theorem 6.2)

`larsonRootCount : LarsonRootCount`: *for squarefree `c > 1`, if `a + b√c` (`a, b ∈ ℤ`) is a
sum of `n` roots of unity, then `n ≥ |b| φ(2c)`.*  This is the external theorem quoted at
manuscript line 3936; it is proved here, so the multiplicity-one argument and the identification
of the six residual twists hold with **no external hypothesis**.

Proof, through the Galois-averaging machinery of `GaloisAverage.lean`:
* **A real primitive character for `ℚ(√c)`.**  For an odd prime `p`, the Legendre symbol
  `legChar p` is a real primitive character of conductor `p` whose Gauss sum satisfies
  `G² = (-1/p) p` (Mathlib's `gaussSum_sq`).  Products of real primitive characters of coprime
  conductors are real primitive characters (`IsRealChar.mul_char`) with
  `G(χ₁χ₂)² = G(χ₁)² G(χ₂)²` (`gaussSumC_mul_sq`, via the CRT product).  By induction over the
  prime factors (`exists_char_odd_squarefree`), every odd squarefree `m` carries a character
  with `G² = ±m`.  Multiplying by `χ₄` (`G² = -4`), `χ₈` (`G² = 8`) or `χ₈'` (`G² = -8`)
  yields a character of conductor `f ∈ {c, 4c}` with `G² = κ² c`, `κ ∈ {1, 2}`, and
  `φ(f) = κ φ(2c)` in every case.
* **The count** (`card_ge_of_trace`).  With `a + b√c = a + (±b/κ) G`, the χ-trace identity
  gives `∑_z S(z) = (±b/κ) G φ(N)`, while each `|S(z)| ≤ |G| φ(N)/φ(f)` (from
  `wtrace_cases`: `S(z) = 0` or `S(z) = K χ(w) G R_u(z₂)` with `|R_u| ≤ φ(u)` and
  `K φ(f) φ(u) = φ(N)`).  Hence `|b| φ(f)/κ ≤ n`, i.e. `|b| φ(2c) ≤ n`.

## Main results
* `larsonRootCount : LarsonRootCount`.
* `multiplicity_eq_one_unconditional`, `multiplicity_eq_one_of_family_unconditional`
  (manuscript lines 3926–4004) and `rank6_multiplicity_one_and_twists_unconditional` (lines
  3926–4051): no external hypothesis remains; the inputs are the data of
  Lemma `lem:rank6-induction`.
-/

namespace HaagerupIzumi.C8.NumberTheory

/-! ### The count from a character with `G² = κ² c` -/

theorem norm_unitSum_le {u : ℕ} (hu : 0 < u) {z : ℂ} (hz : z ^ u = 1) :
    ‖unitSum u z‖ ≤ Nat.totient u := by
  unfold unitSum
  calc ‖∑ k ∈ (Finset.range u).filter u.Coprime, z ^ k‖
      ≤ ∑ k ∈ (Finset.range u).filter u.Coprime, ‖z ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ (Finset.range u).filter u.Coprime, (1 : ℝ) :=
        Finset.sum_congr rfl fun k _ => by
          rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hu.ne', one_pow]
    _ = Nat.totient u := by
        rw [Finset.sum_const, card_filter_coprime, nsmul_eq_mul, mul_one]

/-- **The root count from a character**: if a multiset of roots of unity has sum
`r₀ + r₁ G` (`r₀, r₁ ∈ ℚ`, `G ≠ 0` the Gauss sum of a real primitive character of conductor
`f ≠ 1`), then it has at least `|r₁| φ(f)` elements. -/
theorem card_ge_of_trace {f : ℕ} [NeZero f] (hf1 : f ≠ 1) {χ : ℕ → ℤ} (hχ : IsRealChar f χ)
    (hG : gaussSumC f χ ≠ 0) (s : Multiset ℂ) (hroots : ∀ z ∈ s, IsRootOfUnity z) (r₀ r₁ : ℚ)
    (hsum : s.sum = r₀ + r₁ * gaussSumC f χ) :
    |(r₁ : ℝ)| * Nat.totient f ≤ Multiset.card s := by
  obtain ⟨M, hM, hMs⟩ := exists_common_period s hroots
  obtain ⟨N, hNdef⟩ : ∃ N, N = f * M := ⟨_, rfl⟩
  have hf0 : 0 < f := Nat.pos_of_ne_zero (NeZero.ne f)
  have hN0 : 0 < N := by rw [hNdef]; exact Nat.mul_pos hf0 hM
  have : NeZero N := ⟨hN0.ne'⟩
  have hfN : f ∣ N := by rw [hNdef]; exact Nat.dvd_mul_right f M
  have hs : ∀ z ∈ s, z ^ N = 1 := fun z hz => by rw [hNdef, pow_mul', hMs z hz, one_pow]
  obtain ⟨-, hS⟩ := trace_identities hfN hf1 hχ s hs r₀ r₁ hsum
  have hφN : (0 : ℝ) < Nat.totient N := by exact_mod_cast Nat.totient_pos.mpr hN0
  have hGpos : 0 < ‖gaussSumC f χ‖ := norm_pos_iff.mpr hG
  have hpt : ∀ z ∈ s, (Nat.totient f : ℝ) * ‖wtrace N (fun x => (χ x : ℂ)) z‖ ≤
      ‖gaussSumC f χ‖ * Nat.totient N := by
    intro z hz
    rcases wtrace_cases hfN hχ (hs z hz) with
      ⟨h0, -⟩ | ⟨w, u, K, z₂, -, hwc, hu0, -, hz₂, -, hK, hSz, -⟩
    · rw [h0, norm_zero, mul_zero]
      positivity
    · have hR := norm_unitSum_le hu0 hz₂
      have hχw : ‖((χ w : ℤ) : ℂ)‖ = 1 := by
        rcases mul_self_eq_one_iff.mp (hχ.sq w hwc) with h | h <;> simp [h]
      have hK' : (K : ℝ) * ((Nat.totient f : ℝ) * Nat.totient u) = Nat.totient N := by
        exact_mod_cast hK
      rw [hSz, norm_mul, norm_mul, norm_mul, hχw, mul_one, Complex.norm_natCast]
      calc (Nat.totient f : ℝ) * (K * ‖gaussSumC f χ‖ * ‖unitSum u z₂‖)
          ≤ (Nat.totient f : ℝ) * (K * ‖gaussSumC f χ‖ * Nat.totient u) := by gcongr
        _ = ‖gaussSumC f χ‖ * Nat.totient N := by rw [← hK']; ring
  have hnorm : ‖(s.map (wtrace N fun x => (χ x : ℂ))).sum‖ =
      |(r₁ : ℝ)| * ‖gaussSumC f χ‖ * Nat.totient N := by
    rw [hS, norm_mul, norm_mul, Complex.norm_ratCast, Complex.norm_natCast]
  have hle1 : ‖(s.map (wtrace N fun x => (χ x : ℂ))).sum‖ ≤
      (s.map fun z => ‖wtrace N (fun x => (χ x : ℂ)) z‖).sum := by
    have h := norm_multiset_sum_le (s.map (wtrace N fun x => (χ x : ℂ)))
    rwa [Multiset.map_map] at h
  have hle2 := Multiset.sum_map_le_sum_map
    (fun z => (Nat.totient f : ℝ) * ‖wtrace N (fun x => (χ x : ℂ)) z‖)
    (fun _ => ‖gaussSumC f χ‖ * Nat.totient N) hpt
  rw [Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate,
    nsmul_eq_mul] at hle2
  have hX : 0 < ‖gaussSumC f χ‖ * Nat.totient N := mul_pos hGpos hφN
  have key : (|(r₁ : ℝ)| * Nat.totient f) * (‖gaussSumC f χ‖ * Nat.totient N) ≤
      (Multiset.card s : ℝ) * (‖gaussSumC f χ‖ * Nat.totient N) := by
    calc (|(r₁ : ℝ)| * Nat.totient f) * (‖gaussSumC f χ‖ * Nat.totient N)
        = (Nat.totient f : ℝ) * ‖(s.map (wtrace N fun x => (χ x : ℂ))).sum‖ := by
          rw [hnorm]
          ring
      _ ≤ (Nat.totient f : ℝ) * (s.map fun z => ‖wtrace N (fun x => (χ x : ℂ)) z‖).sum :=
          mul_le_mul_of_nonneg_left hle1 (Nat.cast_nonneg _)
      _ ≤ _ := hle2
  exact le_of_mul_le_mul_right key hX

/-- If the Gauss sum satisfies `G² = κ² c`, then `G = ±κ√c`, and a sum `a + b√c` of `n`
roots of unity has `|b| φ(f) ≤ κ n`. -/
theorem card_ge_of_gaussSq {f : ℕ} [NeZero f] (hf1 : f ≠ 1) {χ : ℕ → ℤ}
    (hχ : IsRealChar f χ) {c κ : ℕ} (hc : 0 < c) (hκ : 0 < κ)
    (hG : gaussSumC f χ ^ 2 = (κ : ℂ) ^ 2 * c)
    (a b : ℤ) (s : Multiset ℂ) (hroots : ∀ z ∈ s, IsRootOfUnity z)
    (hsum : s.sum = (a : ℂ) + (b : ℂ) * (Real.sqrt c : ℂ)) :
    |(b : ℝ)| * Nat.totient f ≤ κ * Multiset.card s := by
  have hsc : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = c := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg c)
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hκR : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hGne : gaussSumC f χ ≠ 0 := by
    intro h0
    rw [h0] at hG
    have h' : (κ : ℂ) ^ 2 * c = 0 := by rw [← hG]; ring
    exact mul_ne_zero (pow_ne_zero 2 hκC) hcC h'
  have hprod : (gaussSumC f χ - κ * Real.sqrt c) * (gaussSumC f χ + κ * Real.sqrt c) = 0 := by
    linear_combination hG - (κ : ℂ) ^ 2 * hsc
  obtain ⟨ε, hε2, hεabs, hGε⟩ : ∃ ε : ℚ, (ε : ℂ) * ε = 1 ∧ |(ε : ℝ)| = 1 ∧
      gaussSumC f χ = ε * κ * Real.sqrt c := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact ⟨1, by norm_num, by norm_num, by push_cast; linear_combination h⟩
    · exact ⟨-1, by norm_num, by norm_num, by push_cast; linear_combination h⟩
  have hκinv : (κ : ℂ) * (κ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hκC
  have hsum' : s.sum = ((a : ℚ) : ℂ) + (((b : ℚ) * ε / κ : ℚ) : ℂ) * gaussSumC f χ := by
    rw [hsum, hGε]
    push_cast
    linear_combination (-(b : ℂ) * Real.sqrt c * κ * (κ : ℂ)⁻¹) * hε2 +
      (-(b : ℂ) * Real.sqrt c) * hκinv
  have h := card_ge_of_trace hf1 hχ hGne s hroots _ _ hsum'
  have habs : |((((b : ℚ) * ε / κ : ℚ)) : ℝ)| = |(b : ℝ)| / κ := by
    push_cast
    rw [abs_div, abs_mul, hεabs, mul_one, abs_of_pos hκR]
  rw [habs, div_mul_eq_mul_div, div_le_iff₀ hκR] at h
  linarith

/-! ### Products of real primitive characters -/

theorem IsRealChar.map_one {c : ℕ} {χ : ℕ → ℤ} (hχ : IsRealChar c χ) : χ 1 = 1 :=
  calc χ 1 = χ (1 * 1) := by rw [mul_one]
    _ = χ 1 * χ 1 := hχ.mul 1 1 (Nat.coprime_one_left c) (Nat.coprime_one_left c)
    _ = 1 := hχ.sq 1 (Nat.coprime_one_left c)

/-- The product of real primitive characters of coprime conductors is a real primitive
character of the product conductor. -/
theorem IsRealChar.mul_char {c₁ c₂ : ℕ} {χ₁ χ₂ : ℕ → ℤ} (h₁ : IsRealChar c₁ χ₁)
    (h₂ : IsRealChar c₂ χ₂) (hc : c₁.Coprime c₂) :
    IsRealChar (c₁ * c₂) (fun x => χ₁ x * χ₂ x) := by
  refine ⟨fun x y h => ?_, fun x y hx hy => ?_, fun x hx => ?_, fun d hd hne => ?_⟩
  · obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hc).mpr h
    show χ₁ x * χ₂ x = χ₁ y * χ₂ y
    rw [h₁.periodic x y h1, h₂.periodic x y h2]
  · show χ₁ (x * y) * χ₂ (x * y) = χ₁ x * χ₂ x * (χ₁ y * χ₂ y)
    rw [h₁.mul x y (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right c₁ c₂) hx)
      (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right c₁ c₂) hy),
      h₂.mul x y (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left c₂ c₁) hx)
      (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left c₂ c₁) hy)]
    ring
  · show χ₁ x * χ₂ x * (χ₁ x * χ₂ x) = 1
    have e1 := h₁.sq x (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right c₁ c₂) hx)
    have e2 := h₂.sq x (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left c₂ c₁) hx)
    linear_combination (χ₂ x * χ₂ x) * e1 + e2
  · have hdg : d = Nat.gcd d c₁ * Nat.gcd d c₂ := by
      rw [← Nat.Coprime.gcd_mul d hc, Nat.gcd_eq_left hd]
    have hgc : (Nat.gcd d c₁).Coprime (Nat.gcd d c₂) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right d c₁)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right d c₂) hc)
    have h1one : ∀ k : ℕ, k ≡ 1 [MOD Nat.gcd d c₁] → k ≡ 1 [MOD Nat.gcd d c₂] →
        k ≡ 1 [MOD d] := by
      intro k hk1 hk2
      rw [hdg]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hgc).mp ⟨hk1, hk2⟩
    by_cases hd1 : Nat.gcd d c₁ = c₁
    · have hd2 : Nat.gcd d c₂ ≠ c₂ := by
        intro hd2
        apply hne
        rw [hdg, hd1, hd2]
      obtain ⟨e₂, he₂c, he₂1, hχe₂⟩ := h₂.primitive _ (Nat.gcd_dvd_right d c₂) hd2
      obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hc 1 e₂
      refine ⟨k, Nat.Coprime.mul_right ?_ ?_, h1one k (hk1.of_dvd (Nat.gcd_dvd_right d c₁))
        ((hk2.of_dvd (Nat.gcd_dvd_right d c₂)).trans he₂1), ?_⟩
      · show Nat.gcd k c₁ = 1
        rw [hk1.gcd_eq]
        exact Nat.gcd_one_left c₁
      · show Nat.gcd k c₂ = 1
        rw [hk2.gcd_eq]
        exact he₂c
      · show χ₁ k * χ₂ k = -1
        rw [h₁.periodic k 1 hk1, h₂.periodic k e₂ hk2, h₁.map_one, hχe₂]
        ring
    · obtain ⟨e₁, he₁c, he₁1, hχe₁⟩ := h₁.primitive _ (Nat.gcd_dvd_right d c₁) hd1
      obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hc e₁ 1
      refine ⟨k, Nat.Coprime.mul_right ?_ ?_,
        h1one k ((hk1.of_dvd (Nat.gcd_dvd_right d c₁)).trans he₁1)
          (hk2.of_dvd (Nat.gcd_dvd_right d c₂)), ?_⟩
      · show Nat.gcd k c₁ = 1
        rw [hk1.gcd_eq]
        exact he₁c
      · show Nat.gcd k c₂ = 1
        rw [hk2.gcd_eq]
        exact Nat.gcd_one_left c₂
      · show χ₁ k * χ₂ k = -1
        rw [h₁.periodic k e₁ hk1, h₂.periodic k 1 hk2, h₂.map_one, hχe₁]
        ring

theorem isPrimitiveRoot_pow_crt {c u x : ℕ} {z : ℂ}
    (hz : IsPrimitiveRoot z (c * u)) (hx1 : x ≡ 1 [MOD c]) (hx0 : x ≡ 0 [MOD u]) :
    IsPrimitiveRoot (z ^ x) c := by
  refine ⟨?_, fun l hl => ?_⟩
  · obtain ⟨x', hx'⟩ : u ∣ x := Nat.modEq_zero_iff_dvd.mp hx0
    rw [← pow_mul, hx', show u * x' * c = c * u * x' by ring, pow_mul, hz.pow_eq_one, one_pow]
  · have h1 : c * u ∣ x * l := hz.dvd_of_pow_eq_one _ (by rw [pow_mul]; exact hl)
    have hxc : Nat.Coprime c x := by
      show Nat.gcd c x = 1
      rw [Nat.gcd_comm, hx1.gcd_eq, Nat.gcd_one_left]
    exact hxc.dvd_of_dvd_mul_left (dvd_trans (Nat.dvd_mul_right c u) h1)

/-- A primitive `cu`-th root of unity (`c, u` coprime) is `ζ_c^{w₁} ζ_u^{w₂}` with `w₁, w₂`
units. -/
theorem exists_zetaN_decomp {c u : ℕ} [NeZero c] [NeZero u] (hcu : c.Coprime u) {z : ℂ}
    (hz : IsPrimitiveRoot z (c * u)) :
    ∃ w₁ w₂ : ℕ, w₁.Coprime c ∧ w₂.Coprime u ∧ z = zetaN c ^ w₁ * zetaN u ^ w₂ := by
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hu0 : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  obtain ⟨x, hx1, hx0⟩ := Nat.chineseRemainder hcu 1 0
  obtain ⟨y, hy0, hy1⟩ := Nat.chineseRemainder hcu 0 1
  have hz1 := isPrimitiveRoot_pow_crt hz hx1 hx0
  have hz2 := isPrimitiveRoot_pow_crt (by rw [mul_comm]; exact hz) hy1 hy0
  have hζ1 := zetaN_isPrimitiveRoot hc0
  have hζ2 := zetaN_isPrimitiveRoot hu0
  obtain ⟨w₁, -, hw₁⟩ := hζ1.eq_pow_of_pow_eq_one hz1.pow_eq_one
  obtain ⟨w₂, -, hw₂⟩ := hζ2.eq_pow_of_pow_eq_one hz2.pow_eq_one
  refine ⟨w₁, w₂, (hζ1.pow_iff_coprime hc0 w₁).mp (by rw [hw₁]; exact hz1),
    (hζ2.pow_iff_coprime hu0 w₂).mp (by rw [hw₂]; exact hz2), ?_⟩
  have h1 : x + y ≡ 1 [MOD c] := by
    have := hx1.add hy0
    rwa [add_zero] at this
  have h2 : x + y ≡ 1 [MOD u] := by
    have := hx0.add hy1
    rwa [zero_add] at this
  rw [hw₁, hw₂, ← pow_add,
    pow_eq_pow_of_modEq hz.pow_eq_one ((Nat.modEq_and_modEq_iff_modEq_mul hcu).mp ⟨h1, h2⟩),
    pow_one]

/-- **Gauss sums of products**: `G(χ₁χ₂)² = G(χ₁)² G(χ₂)²` for coprime conductors. -/
theorem gaussSumC_mul_sq {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] {χ₁ χ₂ : ℕ → ℤ}
    (h₁ : IsRealChar c₁ χ₁) (h₂ : IsRealChar c₂ χ₂) (hc : c₁.Coprime c₂) :
    gaussSumC (c₁ * c₂) (fun x => χ₁ x * χ₂ x) ^ 2 =
      gaussSumC c₁ χ₁ ^ 2 * gaussSumC c₂ χ₂ ^ 2 := by
  have hc₁ : 0 < c₁ := Nat.pos_of_ne_zero (NeZero.ne c₁)
  have hc₂ : 0 < c₂ := Nat.pos_of_ne_zero (NeZero.ne c₂)
  obtain ⟨w₁, w₂, hw₁, hw₂, hz⟩ :=
    exists_zetaN_decomp hc (zetaN_isPrimitiveRoot (Nat.mul_pos hc₁ hc₂))
  have hζ1 := (zetaN_isPrimitiveRoot hc₁).pow_eq_one
  have hζ2 := (zetaN_isPrimitiveRoot hc₂).pow_eq_one
  have hprod : gaussSumC (c₁ * c₂) (fun x => χ₁ x * χ₂ x) =
      (χ₁ w₁ * gaussSumC c₁ χ₁) * (χ₂ w₂ * gaussSumC c₂ χ₂) := by
    rw [← gauss_twist h₁ hw₁, ← gauss_twist h₂ hw₂,
      ← sum_units_mul_crt hc (fun k => (χ₁ k : ℂ) * zetaN c₁ ^ (w₁ * k))
        (fun k => (χ₂ k : ℂ) * zetaN c₂ ^ (w₂ * k))
        (fun x y h => by
          show (χ₁ x : ℂ) * zetaN c₁ ^ (w₁ * x) = (χ₁ y : ℂ) * zetaN c₁ ^ (w₁ * y)
          rw [h₁.periodic x y h, pow_eq_pow_of_modEq hζ1 (Nat.ModEq.mul_left w₁ h)])
        (fun x y h => by
          show (χ₂ x : ℂ) * zetaN c₂ ^ (w₂ * x) = (χ₂ y : ℂ) * zetaN c₂ ^ (w₂ * y)
          rw [h₂.periodic x y h, pow_eq_pow_of_modEq hζ2 (Nat.ModEq.mul_left w₂ h)])]
    unfold gaussSumC
    refine Finset.sum_congr rfl fun i _ => ?_
    show ((χ₁ (i : ZMod (c₁ * c₂)).val * χ₂ (i : ZMod (c₁ * c₂)).val : ℤ) : ℂ) *
        zetaN (c₁ * c₂) ^ (i : ZMod (c₁ * c₂)).val =
      ((χ₁ (i : ZMod (c₁ * c₂)).val : ℂ) * zetaN c₁ ^ (w₁ * (i : ZMod (c₁ * c₂)).val)) *
        ((χ₂ (i : ZMod (c₁ * c₂)).val : ℂ) * zetaN c₂ ^ (w₂ * (i : ZMod (c₁ * c₂)).val))
    rw [hz, mul_pow, pow_mul, pow_mul]
    push_cast
    ring
  have hs1 : (χ₁ w₁ : ℂ) * χ₁ w₁ = 1 := by exact_mod_cast h₁.sq w₁ hw₁
  have hs2 : (χ₂ w₂ : ℂ) * χ₂ w₂ = 1 := by exact_mod_cast h₂.sq w₂ hw₂
  rw [hprod]
  linear_combination (gaussSumC c₁ χ₁ ^ 2 * gaussSumC c₂ χ₂ ^ 2 * (χ₂ w₂ : ℂ) * χ₂ w₂) * hs1 +
    (gaussSumC c₁ χ₁ ^ 2 * gaussSumC c₂ χ₂ ^ 2) * hs2

/-! ### The trivial character, the Legendre symbol and the characters of `ℚ(i)`, `ℚ(√±2)` -/

theorem one_isRealChar : IsRealChar 1 (fun _ => 1) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => by norm_num, fun _ _ => by norm_num,
    fun _ hd hne => absurd (Nat.dvd_one.mp hd) hne⟩

theorem gaussSumC_one : gaussSumC 1 (fun _ => 1) = 1 := by
  rw [gaussSumC, sum_units_eq_sum_coprime (fun k => ((1 : ℤ) : ℂ) * zetaN 1 ^ k),
    show (Finset.range 1).filter (Nat.Coprime 1) = {0} by decide, Finset.sum_singleton]
  simp

/-- The Legendre symbol modulo a prime `p`, as a function on `ℕ`. -/
noncomputable def legChar (p : ℕ) [Fact p.Prime] (x : ℕ) : ℤ := quadraticChar (ZMod p) (x : ZMod p)

/-- For an odd prime `p`, the Legendre symbol is a real primitive character of conductor
`p`. -/
theorem legChar_isRealChar (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    IsRealChar p (legChar p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨fun x y h => ?_, fun x y _ _ => ?_, fun x hx => ?_, fun d hd hne => ?_⟩
  · unfold legChar
    rw [(ZMod.natCast_eq_natCast_iff x y p).mpr h]
  · unfold legChar
    rw [Nat.cast_mul, map_mul]
  · unfold legChar
    have hx0 : (x : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp hx.symm
    rw [← sq]
    exact quadraticChar_sq_one hx0
  · have hd1 : d = 1 := by
      rcases (Nat.dvd_prime hp.out).mp hd with h | h
      · exact h
      · exact absurd h hne
    subst hd1
    have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [MulChar.map_zero] at ha
      exact absurd ha (by norm_num)
    refine ⟨a.val, ?_, Nat.modEq_one, ?_⟩
    · apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp.out]
      intro hdvd
      have : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt a)
      exact ha0 ((ZMod.val_eq_zero a).mp this)
    · unfold legChar
      rw [ZMod.natCast_zmod_val]
      exact ha

/-- **The quadratic Gauss sum**: `G(legChar p)² = (-1/p) p` (Mathlib's `gaussSum_sq`). -/
theorem gaussSumC_legChar_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    gaussSumC p (legChar p) ^ 2 = ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) * p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let χ' : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hχ' : χ' ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).mpr (quadraticChar_ne_one hF)
  have hq : χ'.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hsq := gaussSum_sq hχ' hq (ZMod.isPrimitive_stdAddChar p)
  have heq : gaussSumC p (legChar p) = gaussSum χ' ZMod.stdAddChar := by
    unfold gaussSumC gaussSum
    calc ∑ i : (ZMod p)ˣ, (legChar p (i : ZMod p).val : ℂ) * zetaN p ^ (i : ZMod p).val
        = ∑ i : (ZMod p)ˣ, χ' (i : ZMod p) * ZMod.stdAddChar (i : ZMod p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          · simp only [χ', MulChar.ringHomComp_apply, legChar, ZMod.natCast_zmod_val, eq_intCast]
          · rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, zetaN, ← Complex.exp_nat_mul]
            congr 1
            ring
      _ = ∑ a ∈ (Finset.univ : Finset (ZMod p)ˣ).map
            ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩,
            χ' a * ZMod.stdAddChar a :=
          (Finset.sum_map Finset.univ ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩
            (fun a => χ' a * ZMod.stdAddChar a)).symm
      _ = ∑ a : ZMod p, χ' a * ZMod.stdAddChar a := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro a _ ha
          have hnu : ¬ IsUnit a := fun hu =>
            ha (Finset.mem_map.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩)
          rw [MulChar.map_nonunit χ' hnu, zero_mul]
  rw [heq, hsq, ZMod.card]
  simp only [χ', MulChar.ringHomComp_apply, eq_intCast]

/-- The odd character `χ₄` of conductor `4` (of `ℚ(i)`). -/
def chi4 (x : ℕ) : ℤ := if x % 4 = 1 then 1 else -1

/-- The odd character `χ₈' = χ₈ χ₄` of conductor `8` (of `ℚ(√-2)`). -/
def chi8m (x : ℕ) : ℤ := if x % 8 = 1 ∨ x % 8 = 3 then 1 else -1

theorem odd_of_coprime_of_two_dvd {x m : ℕ} (h : x.Coprime m) (h2 : 2 ∣ m) : x % 2 = 1 := by
  have : ¬ 2 ∣ x := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (Nat.Coprime.coprime_dvd_right h2 h).symm hd
  omega

theorem chi4_isRealChar : IsRealChar 4 chi4 := by
  refine ⟨fun x y h => ?_, fun x y hx hy => ?_, fun x _ => ?_, fun d hd hne => ?_⟩
  · have h' : x % 4 = y % 4 := h
    simp only [chi4, h']
  · have hx2 := odd_of_coprime_of_two_dvd hx (by norm_num)
    have hy2 := odd_of_coprime_of_two_dvd hy (by norm_num)
    have key : ∀ a < 4, ∀ b < 4, a % 2 = 1 → b % 2 = 1 → chi4 (a * b) = chi4 a * chi4 b := by
      decide
    have hm : ∀ t, chi4 (t % 4) = chi4 t := fun t => by simp only [chi4, Nat.mod_mod]
    rw [← hm (x * y), Nat.mul_mod, hm, ← hm x, ← hm y]
    exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
  · unfold chi4
    split_ifs <;> norm_num
  · have key : ∀ d < 5, d ∣ 4 → d ≠ 4 → 3 ≡ 1 [MOD d] := by decide
    exact ⟨3, by decide, key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd)) hd hne,
      by decide⟩

theorem chi8_isRealChar : IsRealChar 8 chi8 := by
  refine ⟨fun x y h => ?_, fun x y hx hy => ?_, fun x _ => ?_, fun d hd hne => ?_⟩
  · have h' : x % 8 = y % 8 := h
    simp only [chi8, h']
  · exact chi8_mul (odd_of_coprime_of_two_dvd hx (by norm_num))
      (odd_of_coprime_of_two_dvd hy (by norm_num))
  · unfold chi8
    split_ifs <;> norm_num
  · have key : ∀ d < 9, d ∣ 8 → d ≠ 8 → 5 ≡ 1 [MOD d] := by decide
    exact ⟨5, by decide, key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd)) hd hne,
      by decide⟩

theorem chi8m_isRealChar : IsRealChar 8 chi8m := by
  refine ⟨fun x y h => ?_, fun x y hx hy => ?_, fun x _ => ?_, fun d hd hne => ?_⟩
  · have h' : x % 8 = y % 8 := h
    simp only [chi8m, h']
  · have hx2 := odd_of_coprime_of_two_dvd hx (by norm_num)
    have hy2 := odd_of_coprime_of_two_dvd hy (by norm_num)
    have key : ∀ a < 8, ∀ b < 8, a % 2 = 1 → b % 2 = 1 →
        chi8m (a * b) = chi8m a * chi8m b := by
      decide
    have hm : ∀ t, chi8m (t % 8) = chi8m t := fun t => by simp only [chi8m, Nat.mod_mod]
    rw [← hm (x * y), Nat.mul_mod, hm, ← hm x, ← hm y]
    exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
  · unfold chi8m
    split_ifs <;> norm_num
  · have key : ∀ d < 9, d ∣ 8 → d ≠ 8 → 5 ≡ 1 [MOD d] := by decide
    exact ⟨5, by decide, key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd)) hd hne,
      by decide⟩

theorem zetaN_four_sq : zetaN 4 ^ 2 = -1 := by
  have hζ := zetaN_isPrimitiveRoot (n := 4) (by norm_num)
  have hne : zetaN 4 ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h : (zetaN 4 ^ 2 - 1) * (zetaN 4 ^ 2 + 1) = 0 := by linear_combination hζ.pow_eq_one
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

theorem zetaN_eight_four : zetaN 8 ^ 4 = -1 := by
  have hζ := zetaN_isPrimitiveRoot (n := 8) (by norm_num)
  have hne : zetaN 8 ^ 4 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h : (zetaN 8 ^ 4 - 1) * (zetaN 8 ^ 4 + 1) = 0 := by linear_combination hζ.pow_eq_one
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

theorem gauss4_sq : gaussSumC 4 chi4 ^ 2 = -4 := by
  rw [gaussSumC, sum_units_eq_sum_coprime (fun k => (chi4 k : ℂ) * zetaN 4 ^ k),
    show (Finset.range 4).filter (Nat.Coprime 4) = {1, 3} by decide,
    Finset.sum_pair (by norm_num), show chi4 1 = 1 by decide, show chi4 3 = -1 by decide]
  push_cast
  linear_combination (zetaN 4 ^ 4 - 3 * zetaN 4 ^ 2 + 4) * zetaN_four_sq

theorem sum_1357 (f : ℕ → ℂ) : ∑ k ∈ ({1, 3, 5, 7} : Finset ℕ), f k = f 1 + f 3 + f 5 + f 7 := by
  simp [Finset.sum_insert, add_assoc]

theorem gauss8_sq : gaussSumC 8 chi8 ^ 2 = 8 := by
  rw [gaussSumC, sum_units_eq_sum_coprime (fun k => (chi8 k : ℂ) * zetaN 8 ^ k),
    show (Finset.range 8).filter (Nat.Coprime 8) = {1, 3, 5, 7} by decide, sum_1357,
    show chi8 1 = 1 by decide, show chi8 3 = -1 by decide, show chi8 5 = -1 by decide,
    show chi8 7 = 1 by decide]
  push_cast
  linear_combination (-8 + zetaN 8 ^ 2 + 6 * zetaN 8 ^ 4 - 2 * zetaN 8 ^ 6 - 2 * zetaN 8 ^ 8 +
    zetaN 8 ^ 10) * zetaN_eight_four

theorem gauss8m_sq : gaussSumC 8 chi8m ^ 2 = -8 := by
  rw [gaussSumC, sum_units_eq_sum_coprime (fun k => (chi8m k : ℂ) * zetaN 8 ^ k),
    show (Finset.range 8).filter (Nat.Coprime 8) = {1, 3, 5, 7} by decide, sum_1357,
    show chi8m 1 = 1 by decide, show chi8m 3 = 1 by decide, show chi8m 5 = -1 by decide,
    show chi8m 7 = -1 by decide]
  push_cast
  linear_combination (8 + zetaN 8 ^ 2 - 6 * zetaN 8 ^ 4 - 2 * zetaN 8 ^ 6 + 2 * zetaN 8 ^ 8 +
    zetaN 8 ^ 10) * zetaN_eight_four

/-! ### Odd squarefree conductors -/

/-- Every odd squarefree `m` is the conductor of a real primitive character with
`G² = ±m` (product of Legendre symbols). -/
theorem exists_char_odd_squarefree (m : ℕ) (hsf : Squarefree m) (hodd : m % 2 = 1) :
    ∃ χ : ℕ → ℤ, IsRealChar m χ ∧
      ∀ [NeZero m], (gaussSumC m χ ^ 2 = (m : ℂ) ∨ gaussSumC m χ ^ 2 = -(m : ℂ)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨fun _ => 1, one_isRealChar, ?_⟩
    intro _
    left
    rw [gaussSumC_one]
    norm_num
  · obtain ⟨p, hp_def⟩ : ∃ p, p = m.minFac := ⟨_, rfl⟩
    have hp : p.Prime := by rw [hp_def]; exact Nat.minFac_prime hm1
    obtain ⟨m', hm'⟩ : p ∣ m := by rw [hp_def]; exact Nat.minFac_dvd m
    subst hm'
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hm'0 : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · rw [h, mul_zero] at hodd
        omega
      · exact h
    have hcop : p.Coprime m' := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      rintro ⟨k, rfl⟩
      have hu := hsf p ⟨k, by ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
    have hlt : m' < p * m' := by
      have := hp.two_le
      nlinarith
    have hsf' : Squarefree m' := Squarefree.squarefree_of_dvd (Dvd.intro_left p rfl) hsf
    have hodd' : m' % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp (Nat.odd_iff.mpr hodd)).2
    obtain ⟨χ', hχ', hG'⟩ := ih m' hlt hsf' hodd'
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨fun x => legChar p x * χ' x, (legChar_isRealChar p hp2).mul_char hχ' hcop, ?_⟩
    intro _
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero m' := ⟨hm'0.ne'⟩
    have hG'' : gaussSumC m' χ' ^ 2 = (m' : ℂ) ∨ gaussSumC m' χ' ^ 2 = -(m' : ℂ) := hG'
    rw [gaussSumC_mul_sq (legChar_isRealChar p hp2) hχ' hcop, gaussSumC_legChar_sq p hp2]
    have hq := quadraticChar_dichotomy (F := ZMod p) (a := -1) (neg_ne_zero.mpr one_ne_zero)
    rcases hq with hq | hq <;> rcases hG'' with h | h
    · left
      rw [hq, h]
      push_cast
      ring
    · right
      rw [hq, h]
      push_cast
      ring
    · right
      rw [hq, h]
      push_cast
      ring
    · left
      rw [hq, h]
      push_cast
      ring

/-! ### Larson's theorem -/

/-- **Larson, Theorem 1.3** (arXiv:1401.1879), proved for squarefree `c > 1`. -/
theorem larsonRootCount : LarsonRootCount := by
  intro c hsf hc a b s hroots hsum
  suffices h : |(b : ℝ)| * Nat.totient (2 * c) ≤ Multiset.card s by
    have h' : ((|b| * (Nat.totient (2 * c) : ℤ) : ℤ) : ℝ) ≤ ((Multiset.card s : ℤ) : ℝ) := by
      push_cast
      exact h
    exact_mod_cast h'
  rcases Nat.even_or_odd c with ⟨m, hm⟩ | hodd
  · -- `c = 2m` with `m` odd: conductor `8m`
    have hc2 : c = 2 * m := by omega
    have hm0 : 0 < m := by omega
    have hmodd : m % 2 = 1 := by
      by_contra hcon
      have h4 : 2 * 2 ∣ c := ⟨m / 2, by omega⟩
      exact absurd (Nat.isUnit_iff.mp (hsf 2 h4)) (by norm_num)
    have hsfm : Squarefree m := Squarefree.squarefree_of_dvd ⟨2, by omega⟩ hsf
    obtain ⟨χ, hχ, hG⟩ := exists_char_odd_squarefree m hsfm hmodd
    have : NeZero m := ⟨hm0.ne'⟩
    have : NeZero (8 * m) := ⟨by omega⟩
    have h2m : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have h4m : Nat.Coprime 4 m := by simpa using Nat.Coprime.pow_left 2 h2m
    have h8m : Nat.Coprime 8 m := by simpa using Nat.Coprime.pow_left 3 h2m
    have hφ : Nat.totient (8 * m) = 2 * Nat.totient (2 * c) := by
      rw [hc2, show 2 * (2 * m) = 4 * m by ring, Nat.totient_mul h8m, Nat.totient_mul h4m,
        show Nat.totient 8 = 4 by decide, show Nat.totient 4 = 2 by decide]
      ring
    have hG' : gaussSumC m χ ^ 2 = (m : ℂ) ∨ gaussSumC m χ ^ 2 = -(m : ℂ) := hG
    rcases hG' with h | h
    · have hχ8 := chi8_isRealChar.mul_char hχ h8m
      have hG8 : gaussSumC (8 * m) (fun x => chi8 x * χ x) ^ 2 = ((2 : ℕ) : ℂ) ^ 2 * c := by
        rw [gaussSumC_mul_sq chi8_isRealChar hχ h8m, gauss8_sq, h, hc2]
        push_cast
        ring
      have key := card_ge_of_gaussSq (by omega) hχ8 (by omega) (by norm_num) hG8 a b s
        hroots hsum
      rw [hφ] at key
      push_cast at key
      linarith
    · have hχ8 := chi8m_isRealChar.mul_char hχ h8m
      have hG8 : gaussSumC (8 * m) (fun x => chi8m x * χ x) ^ 2 = ((2 : ℕ) : ℂ) ^ 2 * c := by
        rw [gaussSumC_mul_sq chi8m_isRealChar hχ h8m, gauss8m_sq, h, hc2]
        push_cast
        ring
      have key := card_ge_of_gaussSq (by omega) hχ8 (by omega) (by norm_num) hG8 a b s
        hroots hsum
      rw [hφ] at key
      push_cast at key
      linarith
  · -- `c` odd: conductor `c` or `4c`
    have hcodd : c % 2 = 1 := Nat.odd_iff.mp hodd
    obtain ⟨χ, hχ, hG⟩ := exists_char_odd_squarefree c hsf hcodd
    have : NeZero c := ⟨by omega⟩
    have hφ2 : Nat.totient (2 * c) = Nat.totient c := Nat.totient_two_mul_of_odd hodd
    rw [hφ2]
    have hG' : gaussSumC c χ ^ 2 = (c : ℂ) ∨ gaussSumC c χ ^ 2 = -(c : ℂ) := hG
    rcases hG' with h | h
    · have hG1 : gaussSumC c χ ^ 2 = ((1 : ℕ) : ℂ) ^ 2 * c := by
        rw [h]
        push_cast
        ring
      have key := card_ge_of_gaussSq (by omega) hχ (by omega) (by norm_num) hG1 a b s
        hroots hsum
      push_cast at key
      linarith
    · have h2c : Nat.Coprime 2 c := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      have h4c : Nat.Coprime 4 c := by simpa using Nat.Coprime.pow_left 2 h2c
      have : NeZero (4 * c) := ⟨by omega⟩
      have hχ4 := chi4_isRealChar.mul_char hχ h4c
      have hG4 : gaussSumC (4 * c) (fun x => chi4 x * χ x) ^ 2 = ((2 : ℕ) : ℂ) ^ 2 * c := by
        rw [gaussSumC_mul_sq chi4_isRealChar hχ h4c, gauss4_sq, h]
        push_cast
        ring
      have hφ4 : Nat.totient (4 * c) = 2 * Nat.totient c := by
        rw [Nat.totient_mul h4c, show Nat.totient 4 = 2 by decide]
      have key := card_ge_of_gaussSq (by omega) hχ4 (by omega) (by norm_num) hG4 a b s
        hroots hsum
      rw [hφ4] at key
      push_cast at key
      linarith

/-! ### Unconditional corollaries -/

/-- **Multiplicity one** (manuscript lines 3926–4004) with no external hypothesis: Larson's
Theorem 1.3 and Lemma `lem:conductor40` are both proved. -/
theorem multiplicity_eq_one_unconditional
    {m : ℕ} (hm : 1 ≤ m) (s : Multiset ℂ) (hroots : ∀ z ∈ s, IsRootOfUnity z)
    (hcard : Multiset.card s = 4 * m ^ 2 + 2)
    (hfirst : s.sum = -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : (s.map (fun z => z ^ 2)).sum =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 :=
  multiplicity_eq_one larsonRootCount conductor40Bound hm s hroots hcard hfirst hε hsecond

/-- **Multiplicity one in the notation of Lemma `lem:rank6-induction`** (manuscript lines
3842–3858 and 3926–4004), with no external hypothesis. -/
theorem multiplicity_eq_one_of_family_unconditional
    {m : ℕ} (hm : 1 ≤ m) {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ)
    (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 4 * m ^ 2 + 2)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j =
      -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 :=
  multiplicity_eq_one_of_family larsonRootCount conductor40Bound hm n θ hθ hdim hfirst hε
    hsecond

/-- **Multiplicity one and the six residual twists** (manuscript lines 3926–4051) with no
external hypothesis; the inputs are the data of Lemma `lem:rank6-induction`. -/
theorem rank6_multiplicity_one_and_twists_unconditional
    {m : ℕ} (hm : 1 ≤ m) {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ j, 0 < n j)
    (θ : ι → ℂ) (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 4 * m ^ 2 + 2)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j =
      -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 ∧ (∀ j, n j = 1) ∧ Function.Injective θ ∧
      (∀ e ∈ nonresidues13, ∃ j, θ j = zeta13 ^ e) ∧ ε = 1 :=
  rank6_multiplicity_one_and_twists larsonRootCount conductor40Bound nonresidueOrbitStep hm n hn
    θ hθ hdim hfirst hε hsecond

#print axioms card_ge_of_trace
#print axioms card_ge_of_gaussSq
#print axioms IsRealChar.mul_char
#print axioms gaussSumC_mul_sq
#print axioms legChar_isRealChar
#print axioms gaussSumC_legChar_sq
#print axioms gauss4_sq
#print axioms gauss8_sq
#print axioms gauss8m_sq
#print axioms exists_char_odd_squarefree
#print axioms larsonRootCount
#print axioms multiplicity_eq_one_unconditional
#print axioms multiplicity_eq_one_of_family_unconditional
#print axioms rank6_multiplicity_one_and_twists_unconditional

end HaagerupIzumi.C8.NumberTheory
