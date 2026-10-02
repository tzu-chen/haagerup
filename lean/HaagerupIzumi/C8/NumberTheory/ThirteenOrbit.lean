module

public import HaagerupIzumi.C8.NumberTheory.Conductor40Proof
public import HaagerupIzumi.C8.NumberTheory.Thirteen

@[expose] public section

/-!
# The Galois-orbit step of Lemma `lem:six-residual-twists` (manuscript lines 4025–4039)

`nonresidueOrbitStep : NonresidueOrbitStep`: *every root in a multiset of six roots of unity
with sum `(-1-√13)/2` is one of the six nonresidue thirteenth roots `ζ₁₃^e`,
`e ∈ {2,5,6,7,8,11}`.*  No hypotheses remain.

Proof (via `GaloisAverage.lean`), with `χ₁₃` the Legendre symbol modulo `13` and Gauss sum
`∑_{i∈(ℤ/13)ˣ} χ₁₃(i) ζ₁₃^i = S_R - S_N = √13` (`gauss13`, from `periodR_eq`, `periodN_eq`).
Choose `N` with `13 ∣ N` and `z^N = 1` on the multiset.  The trace identities give
`∑ T(z) = -φ(N)/2` and `∑ S(z) = -√13 φ(N)/2`.  Pointwise (`pointwise13`),
`Re(12 S(z)) ≥ -√13 φ(N)`, with equality only if `z = -χ₁₃(w) ζ₁₃^w` (`w` prime to `13`; order
`13` if `χ₁₃(w) = -1`, order `26` if `χ₁₃(w) = 1`), and then `12 T(z) = χ₁₃(w) φ(N)`.  Six
terms sum to `-6√13 φ(N)`, so every root is of that form; then `∑ 12 T(z) = -6 φ(N)` forces
`χ₁₃(w) = -1` for every root: the orbit of order `26` (sum `(1-√13)/2`) is excluded by the
rational part, exactly as in the manuscript.

## Main results
* `chi13_isRealChar`, `gauss13`, `primSum13`, `pointwise13`, `nonresidueOrbitStep`.
* `six_residual_twists_proved`: Lemma `lem:six-residual-twists` (lines 4019–4051) with no
  unproved hypotheses (the `lem:rank6-induction` data at `m = 1` remain inputs);
  `six_residual_twists_literal`: the same in the manuscript's wording (six objects, every twist
  a nonresidue thirteenth root).
* `rank6_multiplicity_one_and_twists_of_larson`: multiplicity one and the six residual twists
  (manuscript lines 3926–4051) with `LarsonRootCount` (Larson, arXiv:1401.1879, Theorem 1.3,
  an **external theorem**) as the only hypothesis.
-/

namespace HaagerupIzumi.C8.NumberTheory

/-! ### The Legendre symbol modulo `13` -/

/-- The Legendre symbol `(·/13)` (value `-1` on multiples of `13`, which never occur). -/
def chi13 (x : ℕ) : ℤ := if x % 13 ∈ residues13 then 1 else -1

theorem chi13_mod (x : ℕ) : chi13 (x % 13) = chi13 x := by simp only [chi13, Nat.mod_mod]

theorem chi13_mul_aux : ∀ a < 13, ∀ b < 13, a ≠ 0 → b ≠ 0 →
    chi13 (a * b) = chi13 a * chi13 b := by decide

theorem coprime13_mod {x : ℕ} (h : x.Coprime 13) : x % 13 ≠ 0 := by
  have : ¬ 13 ∣ x := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp h.symm
  omega

theorem chi13_cases (x : ℕ) : chi13 x = 1 ∨ chi13 x = -1 := by
  unfold chi13
  split_ifs <;> simp

/-- The Legendre symbol modulo `13` is a real primitive character of conductor `13`. -/
theorem chi13_isRealChar : IsRealChar 13 chi13 where
  periodic x y h := by
    have h' : x % 13 = y % 13 := h
    simp only [chi13, h']
  mul x y hx hy := by
    have hx' := coprime13_mod hx
    have hy' := coprime13_mod hy
    rw [← chi13_mod (x * y), Nat.mul_mod, chi13_mod, ← chi13_mod x, ← chi13_mod y]
    exact chi13_mul_aux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
      (by omega) (by omega)
  sq x _ := by
    rcases chi13_cases x with h | h <;> rw [h] <;> norm_num
  primitive d hd hne := by
    have h1 : d = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hd with h | h
      · exact h
      · exact absurd h hne
    subst h1
    exact ⟨2, by decide, Nat.modEq_one, by decide⟩

/-! ### The Gauss sum and the primitive-root sum at level `13` -/

theorem zetaN_thirteen : zetaN 13 = zeta13 := by
  simp only [zetaN, zeta13, Nat.cast_ofNat]

theorem coprime13_filter :
    (Finset.range 13).filter (Nat.Coprime 13) = residues13 ∪ nonresidues13 := by
  decide

theorem disjoint_residues13 : Disjoint residues13 nonresidues13 := by
  have h : ∀ a ∈ residues13, a ∉ nonresidues13 := by decide
  exact Finset.disjoint_left.mpr fun a ha => h a ha

theorem chi13_res : ∀ k ∈ residues13, chi13 k = 1 := by decide

theorem chi13_nonres : ∀ k ∈ nonresidues13, chi13 k = -1 := by decide

theorem sum_residues13_eq : ∑ k ∈ residues13, zeta13 ^ k = periodR := by
  simp [residues13, periodR, add_assoc]

theorem sum_nonresidues13_eq' : ∑ k ∈ nonresidues13, zeta13 ^ k = periodN := by
  rw [sum_nonresidues13]
  rfl

/-- The Gauss sum of the Legendre symbol modulo `13` is `√13`. -/
theorem gauss13 : gaussSumC 13 chi13 = (Real.sqrt 13 : ℂ) := by
  rw [gaussSumC, sum_units_eq_sum_coprime (fun k => (chi13 k : ℂ) * zetaN 13 ^ k),
    coprime13_filter, Finset.sum_union disjoint_residues13, zetaN_thirteen]
  have h1 : ∑ k ∈ residues13, (chi13 k : ℂ) * zeta13 ^ k = ∑ k ∈ residues13, zeta13 ^ k :=
    Finset.sum_congr rfl fun k hk => by rw [chi13_res k hk, Int.cast_one, one_mul]
  have h2 : ∑ k ∈ nonresidues13, (chi13 k : ℂ) * zeta13 ^ k =
      -∑ k ∈ nonresidues13, zeta13 ^ k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k hk => by rw [chi13_nonres k hk]; push_cast; ring
  rw [h1, h2, sum_residues13_eq, sum_nonresidues13_eq', periodR_eq, periodN_eq]
  ring

/-- The primitive thirteenth roots of unity sum to `-1`. -/
theorem primSum13 : primSum 13 = -1 := by
  rw [primSum, sum_units_eq_sum_coprime (fun k => zetaN 13 ^ k), coprime13_filter,
    Finset.sum_union disjoint_residues13, zetaN_thirteen, sum_residues13_eq,
    sum_nonresidues13_eq', periodR_add_periodN]

theorem nonres_of_chi13 : ∀ w < 13, w ≠ 0 → chi13 w = -1 → w ∈ nonresidues13 := by decide

theorem re_intCast_mul_natCast (k : ℤ) (n : ℕ) : ((k : ℂ) * (n : ℂ)).re = (k : ℝ) * n := by
  rw [show ((k : ℂ) * (n : ℂ)) = (((k : ℝ) * n : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-! ### The pointwise bound -/

/-- **Pointwise bound** for conductor `13`: `Re(12 S(z)) ≥ -√13 φ(N)`; in the equality case
`z = -χ₁₃(w) ζ₁₃^w` with `w` prime to `13`, and `12 T(z) = χ₁₃(w) φ(N)`. -/
theorem pointwise13 {N : ℕ} [NeZero N] (h13 : 13 ∣ N) {z : ℂ} (hz : z ^ N = 1) :
    -(Real.sqrt 13 * Nat.totient N) ≤ (12 * wtrace N (fun x => (chi13 x : ℂ)) z).re ∧
      ((12 * wtrace N (fun x => (chi13 x : ℂ)) z).re = -(Real.sqrt 13 * Nat.totient N) →
        ∃ w, w < 13 ∧ w.Coprime 13 ∧ z = -(chi13 w : ℂ) * zeta13 ^ w ∧
          12 * wtrace N (fun _ => 1) z = (chi13 w : ℂ) * Nat.totient N) := by
  have hs13 : 0 < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  have hφ : (0 : ℝ) < Nat.totient N := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rcases wtrace_cases h13 chi13_isRealChar hz with
    ⟨hS, -⟩ | ⟨w, u, K, z₂, hw13, hwc, hu0, huc, hz₂, hzeq, hK, hS, hT⟩
  · rw [hS, mul_zero, Complex.zero_re]
    refine ⟨by nlinarith, fun h => ?_⟩
    exfalso
    nlinarith
  · have hφ13 : Nat.totient 13 = 12 := Nat.totient_prime (by norm_num)
    rw [hφ13] at hK
    have hε : ‖(chi13 w : ℂ)‖ = 1 := by
      rcases chi13_cases w with h | h <;> simp [h]
    obtain ⟨hlow, heq⟩ := unitSum_bound hu0 hz₂ hε
    have hK0 : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · rw [h, zero_mul] at hK
        have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
        omega
      · exact h
    have hKpos : (0 : ℝ) < 12 * K * Real.sqrt 13 :=
      mul_pos (mul_pos (by norm_num) (by exact_mod_cast hK0)) hs13
    have hK' : (K : ℝ) * (12 * (Nat.totient u : ℝ)) = Nat.totient N := by exact_mod_cast hK
    have hKφ : (12 * K * Real.sqrt 13 : ℝ) * Nat.totient u = Real.sqrt 13 * Nat.totient N := by
      linear_combination Real.sqrt 13 * hK'
    have hexpr : 12 * wtrace N (fun x => (chi13 x : ℂ)) z =
        ((12 * K * Real.sqrt 13 : ℝ) : ℂ) * ((chi13 w : ℂ) * unitSum u z₂) := by
      rw [hS, gauss13]
      push_cast
      ring
    rw [hexpr, Complex.re_ofReal_mul]
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left hlow hKpos.le], fun h => ?_⟩
    have h' : ((chi13 w : ℂ) * unitSum u z₂).re = -(Nat.totient u : ℝ) := by
      apply mul_left_cancel₀ hKpos.ne'
      rw [h]
      linarith [hKφ]
    obtain ⟨hεz, hεR⟩ := heq h'
    have hsq : (chi13 w : ℂ) * chi13 w = 1 := by exact_mod_cast chi13_isRealChar.sq w hwc
    refine ⟨w, hw13, hwc, ?_, ?_⟩
    · have hz₂' : z₂ = -(chi13 w : ℂ) := by
        linear_combination (chi13 w : ℂ) * hεz - z₂ * hsq
      rw [hzeq, hz₂', zetaN_thirteen]
      ring
    · rw [hT, primSum13]
      have hR : unitSum u z₂ = -(chi13 w : ℂ) * Nat.totient u := by
        linear_combination (chi13 w : ℂ) * hεR - unitSum u z₂ * hsq
      rw [hR]
      have hK'C : (K : ℂ) * (12 * (Nat.totient u : ℂ)) = Nat.totient N := by exact_mod_cast hK
      linear_combination (chi13 w : ℂ) * hK'C

/-! ### The Galois-orbit step -/

/-- **The Galois-averaging step of Lemma `lem:six-residual-twists`** (manuscript lines
4025–4039 of the lemma 4019–4051), proved: six roots of unity with sum `(-1-√13)/2` are
nonresidue thirteenth roots. -/
theorem nonresidueOrbitStep : NonresidueOrbitStep := by
  intro s hroots hcard hsum
  obtain ⟨M, hM, hMs⟩ := exists_common_period s hroots
  obtain ⟨N, hNdef⟩ : ∃ N, N = 13 * M := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hNdef]; positivity
  have : NeZero N := ⟨hN0.ne'⟩
  have h13N : 13 ∣ N := by rw [hNdef]; exact Nat.dvd_mul_right 13 M
  have hs : ∀ z ∈ s, z ^ N = 1 := fun z hz => by rw [hNdef, pow_mul', hMs z hz, one_pow]
  have hφ : (0 : ℝ) < Nat.totient N := by exact_mod_cast Nat.totient_pos.mpr hN0
  have hsum' : s.sum = ((-1 / 2 : ℚ) : ℂ) + ((-1 / 2 : ℚ) : ℂ) * gaussSumC 13 chi13 := by
    rw [hsum, gauss13]
    push_cast
    ring
  obtain ⟨hT, hS⟩ := trace_identities h13N (by norm_num) chi13_isRealChar s hs _ _ hsum'
  -- stage 1: every root realizes the bound for `S`
  have hSre : (s.map fun z => (12 * wtrace N (fun x => (chi13 x : ℂ)) z).re).sum =
      -(6 * (Real.sqrt 13 * Nat.totient N)) := by
    rw [← re_multiset_sum s (fun z => 12 * wtrace N (fun x => (chi13 x : ℂ)) z),
      Multiset.sum_map_mul_left, hS, gauss13]
    have e : (12 : ℂ) * (((-1 / 2 : ℚ) : ℂ) * (Real.sqrt 13 : ℂ) * Nat.totient N) =
        ((-(6 * (Real.sqrt 13 * Nat.totient N)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.ofReal_re]
  have hlow : ∀ z ∈ s, -(Real.sqrt 13 * Nat.totient N) ≤
      (12 * wtrace N (fun x => (chi13 x : ℂ)) z).re :=
    fun z hz => (pointwise13 h13N (hs z hz)).1
  have heq1 : (s.map fun _ => -(Real.sqrt 13 * Nat.totient N)).sum =
      (s.map fun z => (12 * wtrace N (fun x => (chi13 x : ℂ)) z).re).sum := by
    rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hSre, hcard]
    push_cast
    ring
  have hall1 := multiset_eq_of_sum_eq s _ _ hlow heq1
  have hdata : ∀ z ∈ s, ∃ w, w < 13 ∧ w.Coprime 13 ∧ z = -(chi13 w : ℂ) * zeta13 ^ w ∧
      12 * wtrace N (fun _ => 1) z = (chi13 w : ℂ) * Nat.totient N :=
    fun z hz => (pointwise13 h13N (hs z hz)).2 (hall1 z hz).symm
  -- stage 2: the rational part excludes the orbit of order `26`
  have hTre : (s.map fun z => (12 * wtrace N (fun _ => 1) z).re).sum =
      -(6 * (Nat.totient N : ℝ)) := by
    rw [← re_multiset_sum s (fun z => 12 * wtrace N (fun _ => 1) z),
      Multiset.sum_map_mul_left, hT]
    have e : (12 : ℂ) * (((-1 / 2 : ℚ) : ℂ) * Nat.totient N) =
        ((-(6 * (Nat.totient N : ℝ)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.ofReal_re]
  have hlow2 : ∀ z ∈ s, -(Nat.totient N : ℝ) ≤ (12 * wtrace N (fun _ => 1) z).re := by
    intro z hz
    obtain ⟨w, -, -, -, hTw⟩ := hdata z hz
    rw [hTw, re_intCast_mul_natCast]
    rcases chi13_cases w with h | h <;> rw [h] <;> push_cast <;> linarith
  have heq2 : (s.map fun _ => -(Nat.totient N : ℝ)).sum =
      (s.map fun z => (12 * wtrace N (fun _ => 1) z).re).sum := by
    rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hTre, hcard]
    push_cast
    ring
  have hall2 := multiset_eq_of_sum_eq s _ _ hlow2 heq2
  intro z hz
  obtain ⟨w, hw13, hwc, hzw, hTw⟩ := hdata z hz
  have h2 := hall2 z hz
  rw [hTw, re_intCast_mul_natCast] at h2
  have hχ : chi13 w = -1 := by
    rcases chi13_cases w with h | h
    · rw [h] at h2
      push_cast at h2
      linarith
    · exact h
  refine ⟨w, ?_, ?_⟩
  · have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hwc
    exact nonres_of_chi13 w hw13 hw0 hχ
  · rw [hzw, hχ]
    push_cast
    ring

/-! ### Lemma `lem:six-residual-twists` and the assembled rank-six statement -/

/-- **Lemma `lem:six-residual-twists`** (manuscript lines 4019–4051), with no unproved
hypotheses (the `lem:rank6-induction` data at `m = 1` remain inputs). -/
theorem six_residual_twists_proved
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ j, 0 < n j) (θ : ι → ℂ)
    (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 6)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j = -((1 : ℂ) + (Real.sqrt 13 : ℂ)) / 2)
    {ε : ℤ} (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-1 + (2 * (ε : ℂ) - 1) * (Real.sqrt 13 : ℂ)) / 2) :
    (∀ j, n j = 1) ∧ Function.Injective θ ∧
      (∀ e ∈ nonresidues13, ∃ j, θ j = zeta13 ^ e) ∧ ε = 1 :=
  six_residual_twists nonresidueOrbitStep n hn θ hθ hdim hfirst hsecond

/-- **Lemma `lem:six-residual-twists` in the manuscript's wording** (line 4019): there are
exactly six residual central simples, each with `n_j = 1`; their twists are distinct, every twist
is a nonresidue thirteenth root, every nonresidue thirteenth root occurs, and `ε = ν₂(ρ) = 1`.
The `lem:rank6-induction` data at `m = 1` are the inputs. -/
theorem six_residual_twists_literal
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ j, 0 < n j) (θ : ι → ℂ)
    (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 6)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j = -((1 : ℂ) + (Real.sqrt 13 : ℂ)) / 2)
    {ε : ℤ} (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-1 + (2 * (ε : ℂ) - 1) * (Real.sqrt 13 : ℂ)) / 2) :
    Fintype.card ι = 6 ∧ (∀ j, n j = 1) ∧ Function.Injective θ ∧
      (∀ j, ∃ e ∈ nonresidues13, θ j = zeta13 ^ e) ∧
      (∀ e ∈ nonresidues13, ∃ j, θ j = zeta13 ^ e) ∧ ε = 1 := by
  obtain ⟨hn1, hinj, hsurj, hε⟩ := six_residual_twists_proved n hn θ hθ hdim hfirst hsecond
  have hcard : Fintype.card ι = 6 := by
    rw [← hdim]
    simp [hn1]
  refine ⟨hcard, hn1, hinj, fun j => ?_, hsurj, hε⟩
  have hmem : θ j ∈ rootMultiset n θ := Multiset.mem_bind.mpr ⟨j, Finset.mem_univ _,
    Multiset.mem_replicate.mpr ⟨(pow_pos (hn j) 2).ne', rfl⟩⟩
  exact nonresidueOrbitStep _ (rootMultiset_roots hθ) (by rw [rootMultiset_card, hdim])
    (by rw [rootMultiset_sum, hfirst]; ring) _ hmem

/-- **Multiplicity one and the six residual twists** (manuscript lines 3926–4051), with
Lemma `lem:conductor40` and the Galois-orbit step proved: only Larson's Theorem 1.3
(`LarsonRootCount`, external) remains as a hypothesis. -/
theorem rank6_multiplicity_one_and_twists_of_larson (hLarson : LarsonRootCount)
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
  rank6_multiplicity_one_and_twists hLarson conductor40Bound nonresidueOrbitStep hm n hn θ hθ
    hdim hfirst hε hsecond

#print axioms chi13_isRealChar
#print axioms gauss13
#print axioms primSum13
#print axioms pointwise13
#print axioms nonresidueOrbitStep
#print axioms six_residual_twists_proved
#print axioms six_residual_twists_literal
#print axioms rank6_multiplicity_one_and_twists_of_larson

end HaagerupIzumi.C8.NumberTheory
