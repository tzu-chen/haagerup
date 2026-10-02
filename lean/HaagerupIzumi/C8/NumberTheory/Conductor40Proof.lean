module

public import HaagerupIzumi.C8.NumberTheory.GaloisAverage
public import HaagerupIzumi.C8.NumberTheory.Conductor40

@[expose] public section

/-!
# Proof of Lemma `lem:conductor40` (manuscript lines 3950–3995, statement 3950–3955)

`conductor40Bound : Conductor40Bound`: *if a multiset `s` of roots of unity has sum
`-a - b√10` (`a, b ∈ ℤ_{≥0}`), then `|s| ≥ a + 8b`; if equality holds and the sum of the
squared roots lies in `ℚ(√10)`, that second sum is `a`.*  No hypotheses remain.

Proof (via `GaloisAverage.lean`).  Choose `N` with `40 ∣ N` and `z^N = 1` for all `z ∈ s`.
For `j ∈ (ℤ/N)ˣ` conjugation gives `∑_{z∈s} z^j = -a - b χ₄₀(j) √10`, where
`√10 = G/2`, `G = ∑_{i∈(ℤ/40)ˣ} χ₄₀(i) ζ₄₀^i = 2√10` (`gauss40`, from `orbitPlus40_eq`,
`orbitMinus40_eq`).  Summing, `∑ T(z) = -a φ(N)` and `∑ S(z) = -b √10 φ(N)` with
`T(z) = ∑_j z^j`, `S(z) = ∑_j χ₄₀(j) z^j`.  Pointwise (`pointwise40`),
`Re(√10 T(z) + 8 S(z)) ≥ -√10 φ(N)`, with equality only for `z = -1` (then `T = -φ(N)`) or
`z = ζ₄₀^w`, `w ∈ O₋` (then `T = 0`):
* if `40 ∤ ord z`, `S(z) = 0` and `Re T(z) ≥ -φ(N)`, equality only if `z = -1`;
* if `40 ∣ ord z`, `T(z) = 0`, and either `S(z) = 0` or `ord z = 40u`, `(u, 40) = 1`,
  `z = ζ₄₀^w z₂`, `S(z) = K χ₄₀(w) 2√10 R_u(z₂)` with `16 K φ(u) = φ(N)`; equality forces
  `χ₄₀(w) z₂ = -1`, and `u` odd excludes `z₂ = -1`.
Summing the bound gives `|s| ≥ a + 8b`.  In the equality case every root is `-1` or in `O₋`;
then `T(z²) = -T(z)` and `S(z²) = 0` for every root, and the trace identities for the squared
multiset (sum `x + y√10`, `x, y ∈ ℚ`) give `x = a`, `y = 0`.

## Main results
* `chi40_isRealChar`, `gauss40`, `primSum40`: `χ₄₀` is a real primitive character of
  conductor `40` with Gauss sum `2√10`, and the primitive fortieth roots sum to `0`.
* `pointwise40`, `conductor40Bound`.
* `multiplicity_eq_one_of_larson`, `multiplicity_eq_one_of_family_of_larson`: multiplicity one
  (manuscript lines 3926–4004) with `LarsonRootCount` (Larson, arXiv:1401.1879, Theorem 1.3,
  an **external theorem**) as the only hypothesis.
-/

namespace HaagerupIzumi.C8.NumberTheory

/-! ### The character `χ₄₀` -/

/-- The character `(2/·)` modulo `8`. -/
def chi8 (x : ℕ) : ℤ := if x % 8 = 1 ∨ x % 8 = 7 then 1 else -1

/-- The character `(·/5)` modulo `5`. -/
def chi5 (x : ℕ) : ℤ := if x % 5 = 1 ∨ x % 5 = 4 then 1 else -1

theorem chi40_eq_mul (x : ℕ) : chi40 x = chi8 x * chi5 x := rfl

theorem chi8_mod (x : ℕ) : chi8 (x % 8) = chi8 x := by simp only [chi8, Nat.mod_mod]

theorem chi5_mod (x : ℕ) : chi5 (x % 5) = chi5 x := by simp only [chi5, Nat.mod_mod]

theorem chi8_mul_aux : ∀ a < 8, ∀ b < 8, a % 2 = 1 → b % 2 = 1 →
    chi8 (a * b) = chi8 a * chi8 b := by decide

theorem chi5_mul_aux : ∀ a < 5, ∀ b < 5, a ≠ 0 → b ≠ 0 →
    chi5 (a * b) = chi5 a * chi5 b := by decide

theorem chi8_mul {x y : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    chi8 (x * y) = chi8 x * chi8 y := by
  rw [← chi8_mod (x * y), Nat.mul_mod, chi8_mod, ← chi8_mod x, ← chi8_mod y]
  exact chi8_mul_aux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (by omega) (by omega)

theorem chi5_mul {x y : ℕ} (hx : x % 5 ≠ 0) (hy : y % 5 ≠ 0) :
    chi5 (x * y) = chi5 x * chi5 y := by
  rw [← chi5_mod (x * y), Nat.mul_mod, chi5_mod, ← chi5_mod x, ← chi5_mod y]
  exact chi5_mul_aux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (by omega) (by omega)

theorem coprime40_mod {x : ℕ} (h : x.Coprime 40) : x % 2 = 1 ∧ x % 5 ≠ 0 := by
  have h2 : ¬ 2 ∣ x := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (Nat.Coprime.coprime_dvd_right (show 2 ∣ 40 by norm_num) h).symm hd
  have h5 : ¬ 5 ∣ x := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp
      (Nat.Coprime.coprime_dvd_right (show 5 ∣ 40 by norm_num) h).symm hd
  omega

theorem chi40_cases (x : ℕ) : chi40 x = 1 ∨ chi40 x = -1 := by
  unfold chi40
  split_ifs <;> norm_num

/-- `χ₄₀` is a real primitive character of conductor `40`. -/
theorem chi40_isRealChar : IsRealChar 40 chi40 where
  periodic x y h := by
    have h' : x % 40 = y % 40 := h
    have h8 : x % 8 = y % 8 := by omega
    have h5 : x % 5 = y % 5 := by omega
    simp only [chi40, h8, h5]
  mul x y hx hy := by
    obtain ⟨hx2, hx5⟩ := coprime40_mod hx
    obtain ⟨hy2, hy5⟩ := coprime40_mod hy
    rw [chi40_eq_mul, chi40_eq_mul, chi40_eq_mul, chi8_mul hx2 hy2, chi5_mul hx5 hy5]
    ring
  sq x _ := by
    rcases chi40_cases x with h | h <;> rw [h] <;> norm_num
  primitive d hd hne := by
    have key : ∀ d < 41, d ∣ 40 → d ≠ 40 → (21 ≡ 1 [MOD d] ∨ 17 ≡ 1 [MOD d]) := by decide
    rcases key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd)) hd hne with h | h
    · exact ⟨21, by decide, h, by decide⟩
    · exact ⟨17, by decide, h, by decide⟩

/-! ### The Gauss sum and the primitive-root sum at level `40` -/

theorem zetaN_forty : zetaN 40 = zeta40 := by
  simp only [zetaN, zeta40, Nat.cast_ofNat]

theorem coprime40_filter : (Finset.range 40).filter (Nat.Coprime 40) = plus40 ∪ minus40 := by
  decide

theorem disjoint_plus40_minus40 : Disjoint plus40 minus40 := by
  have h : ∀ a ∈ plus40, a ∉ minus40 := by decide
  exact Finset.disjoint_left.mpr fun a ha => h a ha

theorem chi40_plus : ∀ k ∈ plus40, chi40 k = 1 := by decide

theorem chi40_minus : ∀ k ∈ minus40, chi40 k = -1 := by decide

theorem sum_plus40_eq : ∑ k ∈ plus40, zeta40 ^ k = orbitPlus40 := by
  simp [plus40, orbitPlus40, add_assoc]

theorem sum_minus40_eq : ∑ k ∈ minus40, zeta40 ^ k = orbitMinus40 := by
  simp [minus40, orbitMinus40, add_assoc]

/-- The Gauss sum of `χ₄₀` is `2√10`. -/
theorem gauss40 : gaussSumC 40 chi40 = 2 * (Real.sqrt 10 : ℂ) := by
  rw [gaussSumC, sum_units_eq_sum_coprime (fun k => (chi40 k : ℂ) * zetaN 40 ^ k),
    coprime40_filter, Finset.sum_union disjoint_plus40_minus40, zetaN_forty]
  have h1 : ∑ k ∈ plus40, (chi40 k : ℂ) * zeta40 ^ k = ∑ k ∈ plus40, zeta40 ^ k :=
    Finset.sum_congr rfl fun k hk => by rw [chi40_plus k hk, Int.cast_one, one_mul]
  have h2 : ∑ k ∈ minus40, (chi40 k : ℂ) * zeta40 ^ k = -∑ k ∈ minus40, zeta40 ^ k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k hk => by rw [chi40_minus k hk]; push_cast; ring
  rw [h1, h2, sum_plus40_eq, sum_minus40_eq, orbitPlus40_eq, orbitMinus40_eq]
  ring

/-- The primitive fortieth roots of unity sum to `0`. -/
theorem primSum40 : primSum 40 = 0 := by
  rw [primSum, sum_units_eq_sum_coprime (fun k => zetaN 40 ^ k), coprime40_filter,
    Finset.sum_union disjoint_plus40_minus40, zetaN_forty, sum_plus40_eq, sum_minus40_eq,
    orbit40_add]

theorem totient_forty : Nat.totient 40 = 16 := by decide

/-! ### The pointwise bound -/

/-- The combined functional `√10·T(z) + 8·S(z)`. -/
noncomputable def phi40 (N : ℕ) [NeZero N] (z : ℂ) : ℂ :=
  (Real.sqrt 10 : ℂ) * wtrace N (fun _ => 1) z + 8 * wtrace N (fun x => (chi40 x : ℂ)) z

/-- **Pointwise bound** for conductor `40`: `Re(√10 T(z) + 8 S(z)) ≥ -√10 φ(N)`, with equality
only for `z = -1` (where `T(z) = -φ(N)`) or `z = ζ₄₀^w`, `w ∈ O₋` (where `T(z) = 0`). -/
theorem pointwise40 {N : ℕ} [NeZero N] (h40 : 40 ∣ N) {z : ℂ} (hz : z ^ N = 1) :
    -(Real.sqrt 10 * Nat.totient N) ≤ (phi40 N z).re ∧
      ((phi40 N z).re = -(Real.sqrt 10 * Nat.totient N) →
        (z = -1 ∧ wtrace N (fun _ => 1) z = -(Nat.totient N : ℂ)) ∨
          ((∃ w ∈ minus40, z = zeta40 ^ w) ∧ wtrace N (fun _ => 1) z = 0)) := by
  have hs10 : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have hφ : (0 : ℝ) < Nat.totient N := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rcases wtrace_cases h40 chi40_isRealChar hz with
    ⟨hS, -⟩ | ⟨w, u, K, z₂, hw40, hwc, hu0, huc, hz₂, hzeq, hK, hS, hT⟩
  · obtain ⟨hlow, heq⟩ := wtrace_one_bound hz
    have hre : (phi40 N z).re = Real.sqrt 10 * (wtrace N (fun _ => 1) z).re := by
      rw [phi40, hS, mul_zero, add_zero, Complex.re_ofReal_mul]
    rw [hre]
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left hlow hs10.le], fun h => Or.inl (heq ?_)⟩
    exact mul_left_cancel₀ hs10.ne'
      (show Real.sqrt 10 * (wtrace N (fun _ => 1) z).re = Real.sqrt 10 * -(Nat.totient N : ℝ) by
        linarith)
  · rw [totient_forty] at hK
    have hT0 : wtrace N (fun _ => 1) z = 0 := by rw [hT, primSum40, mul_zero, zero_mul]
    have hexpr : phi40 N z =
        ((16 * K * Real.sqrt 10 : ℝ) : ℂ) * ((chi40 w : ℂ) * unitSum u z₂) := by
      rw [phi40, hT0, hS, gauss40]
      push_cast
      ring
    have hε : ‖(chi40 w : ℂ)‖ = 1 := by
      rcases chi40_cases w with h | h <;> simp [h]
    obtain ⟨hlow, heq⟩ := unitSum_bound hu0 hz₂ hε
    have hK0 : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · rw [h, zero_mul] at hK
        have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
        omega
      · exact h
    have hKpos : (0 : ℝ) < 16 * K * Real.sqrt 10 :=
      mul_pos (mul_pos (by norm_num) (by exact_mod_cast hK0)) hs10
    have hK' : (K : ℝ) * (16 * (Nat.totient u : ℝ)) = Nat.totient N := by exact_mod_cast hK
    have hKφ : (16 * K * Real.sqrt 10 : ℝ) * Nat.totient u = Real.sqrt 10 * Nat.totient N := by
      linear_combination Real.sqrt 10 * hK'
    rw [hexpr, Complex.re_ofReal_mul]
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left hlow hKpos.le], fun h => Or.inr ⟨?_, hT0⟩⟩
    have h' : ((chi40 w : ℂ) * unitSum u z₂).re = -(Nat.totient u : ℝ) := by
      apply mul_left_cancel₀ hKpos.ne'
      rw [h]
      linarith [hKφ]
    obtain ⟨hεz, -⟩ := heq h'
    rcases chi40_cases w with hw1 | hw1
    · exfalso
      rw [hw1, Int.cast_one, one_mul] at hεz
      rw [hεz] at hz₂
      have hodd : Odd u := by
        have := (coprime40_mod huc).1
        exact ⟨u / 2, by omega⟩
      rw [hodd.neg_one_pow] at hz₂
      norm_num at hz₂
    · rw [hw1] at hεz
      push_cast at hεz
      have hz₂1 : z₂ = 1 := by linear_combination -hεz
      refine ⟨w, ?_, ?_⟩
      · obtain ⟨h2, h5⟩ := coprime40_mod hwc
        exact (minus40_spec w hw40).mpr ⟨h2, h5, hw1⟩
      · rw [hzeq, hz₂1, mul_one, zetaN_forty]

/-! ### Lemma `lem:conductor40` -/

theorem minus40_coprime20 : ∀ w ∈ minus40, Nat.Coprime w 20 := by decide

/-- **Lemma `lem:conductor40`** (manuscript lines 3950–3995, statement 3950–3955), proved. -/
theorem conductor40Bound : Conductor40Bound := by
  intro a b s hroots hsum
  obtain ⟨M, hM, hMs⟩ := exists_common_period s hroots
  obtain ⟨N, hNdef⟩ : ∃ N, N = 40 * M := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hNdef]; positivity
  have : NeZero N := ⟨hN0.ne'⟩
  have h40N : 40 ∣ N := by rw [hNdef]; exact Nat.dvd_mul_right 40 M
  have hs : ∀ z ∈ s, z ^ N = 1 := fun z hz => by rw [hNdef, pow_mul', hMs z hz, one_pow]
  have hs10 : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have hφ : (0 : ℝ) < Nat.totient N := by exact_mod_cast Nat.totient_pos.mpr hN0
  have hsum' : s.sum = ((-(a : ℚ) : ℚ) : ℂ) + ((-(b : ℚ) / 2 : ℚ) : ℂ) * gaussSumC 40 chi40 := by
    rw [hsum, gauss40]
    push_cast
    ring
  obtain ⟨hT, hS⟩ := trace_identities h40N (by norm_num) chi40_isRealChar s hs _ _ hsum'
  have hsumT : (s.map (wtrace N fun _ => 1)).sum = -(a : ℂ) * Nat.totient N := by
    rw [hT]
    push_cast
    ring
  have hsumS : (s.map (wtrace N fun x => (chi40 x : ℂ))).sum =
      -(b : ℂ) * Real.sqrt 10 * Nat.totient N := by
    rw [hS, gauss40]
    push_cast
    ring
  have hcombC : (s.map (phi40 N)).sum =
      ((-((a + 8 * b : ℝ) * (Real.sqrt 10 * Nat.totient N)) : ℝ) : ℂ) := by
    have e : (s.map (phi40 N)).sum = (s.map fun z => (Real.sqrt 10 : ℂ) *
        wtrace N (fun _ => 1) z + 8 * wtrace N (fun x => (chi40 x : ℂ)) z).sum := rfl
    rw [e, Multiset.sum_map_add, Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, hsumT,
      hsumS]
    push_cast
    ring
  have hcomb : (s.map fun z => (phi40 N z).re).sum =
      -((a + 8 * b : ℝ) * (Real.sqrt 10 * Nat.totient N)) := by
    rw [← re_multiset_sum s (phi40 N), hcombC, Complex.ofReal_re]
  have hlow : ∀ z ∈ s, -(Real.sqrt 10 * Nat.totient N) ≤ (phi40 N z).re :=
    fun z hz => (pointwise40 h40N (hs z hz)).1
  have hsum_le := Multiset.sum_map_le_sum_map (fun _ => -(Real.sqrt 10 * Nat.totient N))
    (fun z => (phi40 N z).re) hlow
  rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hcomb] at hsum_le
  have hX : 0 < Real.sqrt 10 * Nat.totient N := mul_pos hs10 hφ
  have hineq : ((a + 8 * b : ℕ) : ℝ) ≤ Multiset.card s := by
    push_cast
    exact le_of_mul_le_mul_right (by linarith) hX
  refine ⟨by exact_mod_cast hineq, fun hcard hrat => ?_⟩
  obtain ⟨x, y, hxy⟩ := hrat
  have heqsum : (s.map fun _ => -(Real.sqrt 10 * Nat.totient N)).sum =
      (s.map fun z => (phi40 N z).re).sum := by
    rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hcomb, hcard]
    push_cast
    ring
  have hall := multiset_eq_of_sum_eq s _ _ hlow heqsum
  have hcase : ∀ z ∈ s, (z = -1 ∧ wtrace N (fun _ => 1) z = -(Nat.totient N : ℂ)) ∨
      ((∃ w ∈ minus40, z = zeta40 ^ w) ∧ wtrace N (fun _ => 1) z = 0) :=
    fun z hz => (pointwise40 h40N (hs z hz)).2 (hall z hz).symm
  have h20N : 20 ∣ N := dvd_trans (by norm_num) h40N
  -- the squared roots
  have hsq : ∀ z ∈ s, wtrace N (fun _ => 1) (z ^ 2) = -1 * wtrace N (fun _ => 1) z ∧
      wtrace N (fun x => (chi40 x : ℂ)) (z ^ 2) = 0 := by
    intro z hz
    rcases hcase z hz with ⟨rfl, hTz⟩ | ⟨⟨w, hw, rfl⟩, hTz⟩
    · have h1 : ((-1 : ℂ)) ^ 2 = 1 := by norm_num
      rw [h1, hTz]
      constructor
      · simp [wtrace, ZMod.card_units_eq_totient]
      · have := sum_char_units_eq_zero (N := N) h40N (by norm_num) chi40_isRealChar
        simpa [wtrace] using this
    · rw [hTz, mul_zero]
      have h20 : IsPrimitiveRoot (zeta40 ^ 2) 20 := by
        have := zeta40_isPrimitiveRoot.pow_of_dvd (p := 2) (by norm_num) (by norm_num)
        norm_num at this
        exact this
      have hprim : IsPrimitiveRoot ((zeta40 ^ w) ^ 2) 20 := by
        rw [← pow_mul, mul_comm, pow_mul]
        exact h20.pow_of_coprime w (minus40_coprime20 w hw)
      have hpowN : ((zeta40 ^ w) ^ 2) ^ N = 1 := by
        obtain ⟨k, hk⟩ := h20N
        rw [hk, pow_mul, hprim.pow_eq_one, one_pow]
      exact ⟨wtrace_eq_zero_of_sq_dvd (m := 1) (p := 2) h20N hprim (by norm_num) (by norm_num) _
          (fun _ _ _ => rfl) (one_dvd _),
        wtrace_char_eq_zero_of_not_dvd h40N chi40_isRealChar hpowN h20N hprim.pow_eq_one
          (by norm_num)⟩
  have hs₂ : ∀ z' ∈ s.map (fun z => z ^ 2), z' ^ N = 1 := by
    intro z' hz'
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hz'
    rw [← pow_mul, mul_comm, pow_mul, hs z hz, one_pow]
  have hxy' : (s.map fun z => z ^ 2).sum =
      ((x : ℚ) : ℂ) + ((y / 2 : ℚ) : ℂ) * gaussSumC 40 chi40 := by
    rw [hxy, gauss40]
    push_cast
    ring
  obtain ⟨hT₂, hS₂⟩ := trace_identities h40N (by norm_num) chi40_isRealChar _ hs₂ _ _ hxy'
  rw [Multiset.map_map] at hT₂ hS₂
  have e1 : (s.map ((wtrace N fun _ => 1) ∘ fun z => z ^ 2)).sum =
      -1 * (s.map (wtrace N fun _ => 1)).sum := by
    rw [← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun z hz => (hsq z hz).1)
  have e2 : (s.map ((wtrace N fun x => (chi40 x : ℂ)) ∘ fun z => z ^ 2)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hv
    exact (hsq z hz).2
  have hφC : (Nat.totient N : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN0).ne'
  have hxC : (x : ℂ) = a := by
    have h := hT₂.symm.trans e1
    rw [hT] at h
    push_cast at h
    have h' : ((x : ℂ) - a) * Nat.totient N = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' hφC
  have hyC : (y : ℂ) = 0 := by
    have h := hS₂.symm.trans e2
    rw [gauss40] at h
    push_cast at h
    have hs10C : (Real.sqrt 10 : ℂ) ≠ 0 := by exact_mod_cast hs10.ne'
    have h' : (y : ℂ) * ((Real.sqrt 10 : ℂ) * Nat.totient N) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' (mul_ne_zero hs10C hφC)
  rw [hxy, hxC, hyC, zero_mul, add_zero]

/-! ### Multiplicity one with Larson's theorem as the only hypothesis -/

/-- **Multiplicity one** (manuscript lines 3926–4004), with Lemma `lem:conductor40` proved:
only Larson's Theorem 1.3 (`LarsonRootCount`, external) remains as a hypothesis. -/
theorem multiplicity_eq_one_of_larson (hLarson : LarsonRootCount)
    {m : ℕ} (hm : 1 ≤ m) (s : Multiset ℂ) (hroots : ∀ z ∈ s, IsRootOfUnity z)
    (hcard : Multiset.card s = 4 * m ^ 2 + 2)
    (hfirst : s.sum = -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : (s.map (fun z => z ^ 2)).sum =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 :=
  multiplicity_eq_one hLarson conductor40Bound hm s hroots hcard hfirst hε hsecond

/-- **Multiplicity one in the notation of Lemma `lem:rank6-induction`** (manuscript lines
3842–3858 and 3926–4004), with only `LarsonRootCount` (external) as a hypothesis. -/
theorem multiplicity_eq_one_of_family_of_larson (hLarson : LarsonRootCount)
    {m : ℕ} (hm : 1 ≤ m) {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ)
    (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 4 * m ^ 2 + 2)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j =
      -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 :=
  multiplicity_eq_one_of_family hLarson conductor40Bound hm n θ hθ hdim hfirst hε hsecond

#print axioms chi40_isRealChar
#print axioms gauss40
#print axioms primSum40
#print axioms pointwise40
#print axioms conductor40Bound
#print axioms multiplicity_eq_one_of_larson
#print axioms multiplicity_eq_one_of_family_of_larson

end HaagerupIzumi.C8.NumberTheory
