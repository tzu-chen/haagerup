module

public import HaagerupIzumi.CFT.TopBound
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The fourteen core tops and the universal top bound 17/10

Appendix G (lines 3044–3198 of the expanded draft) bounds the lowest weight of every
simple `U`-module by `17/10` using the order-thirteen core `A_L ⊂ U`, whose fourteen
simple modules `x_a = (1,a)`, `y_a = (τ,a)` (`0 ≤ a ≤ 6`) have tops given by the charge
formulas

* lattice–Potts: `m²/156 + [m odd]/4 + p_ε(m)` with `p_1(m) = 0, 2/3` and
  `p_τ(m) = 2/5, 1/15` according as `3 ∣ m` or not (eq:core-charge-minimum);
* parafermion: `h_PF(a,k) = a(a+1)/15 - k²/13 + max(0,|k|-a)`, `-6 ≤ k ≤ 6`
  (eq:pf-charge-minimum);

joined along the isotropic line `k = -5j`, `j = m mod 13`.  A state of right Cartan charge
`m` carries a left affine singlet (`m` even) or doublet (`m` odd).

Everything below is kernel-checked from these formulas:

* `minimizers_spec`: for each of the fourteen modules, the printed lowest weight `h` is the
  minimum of the energy over **all** integers `m`, and the minimizing charges are exactly the
  listed certificate `minsOf`;
* `dims_and_traces`: the top dimensions and the weighted traces `4680 W` of eq:top-W are the
  printed ones; `row_identities` checks `hD = L + Q/156 + P + Z` and the second formula of
  line 3181;
* `sl2_inequalities`: monotonicity of `𝔰𝔩₂` weight multiplicities gives `y₂ ≥ x₅`,
  `y₄ ≥ x₅ + x₆`;
* `universal_top_bound`: `10·(4680 W_total) ≤ 17·4680·D`, via
  `HaagerupIzumi.CFT.core_top_bound`, i.e. `W_total ≤ (17/10) D`.

Inputs that remain external: the embedding of `A_L` and its charge realization (Certificate
`cert:structural-inputs`, item 3), the module classification `Rep(A_L) ≃ Fib ⊠ SO(3)₁₃` and
the top formulas behind the two charge formulas (ALY §2.4), and the trace identity
`W_total = h D` (eq:top-trace).  Lemma `lem:compatible-top` is a manuscript lemma whose
algebraic core is formalized in `Regularity/CompatibleTop`.
-/

namespace HaagerupIzumi.C8.CoreTops

/-- The balanced representative of `n` modulo `13`, in `[-6, 6]`. -/
def bal13 (n : ℤ) : ℤ := (n + 6) % 13 - 6

/-- The Potts contribution `p_ε(m)`; `false` is `ε = 1` (the `x` modules), `true` is `ε = τ`. -/
def potts (tau : Bool) (m : ℤ) : ℚ :=
  if tau then (if m % 3 = 0 then 2 / 5 else 1 / 15) else (if m % 3 = 0 then 0 else 2 / 3)

/-- The left affine contribution: `0` for a singlet (`m` even), `1/4` for a doublet. -/
def leftE (m : ℤ) : ℚ := if m % 2 = 0 then 0 else 1 / 4

/-- The left multiplicity of a state of right charge `m`. -/
def mult (m : ℤ) : ℕ := if m % 2 = 0 then 1 else 2

/-- The parafermion lowest weight `h_PF(a,k)` (eq:pf-charge-minimum). -/
def hPF (a : ℕ) (k : ℤ) : ℚ :=
  (a * (a + 1) : ℚ) / 15 - (k ^ 2 : ℚ) / 13 + ((max 0 ((k.natAbs : ℤ) - a) : ℤ) : ℚ)

/-- The parafermion contribution of the state of right charge `m`: `k = -5j`. -/
def pfE (a : ℕ) (m : ℤ) : ℚ := hPF a (bal13 (-5 * bal13 m))

/-- The energy of the state of right charge `m` in the module `(ε, a)`. -/
def energy (tau : Bool) (a : ℕ) (m : ℤ) : ℚ :=
  (m ^ 2 : ℚ) / 156 + leftE m + potts tau m + pfE a m

/-- The charge window `[-12, 12]`. -/
def window : List ℤ := (List.range 25).map fun i : ℕ => (i : ℤ) - 12

theorem mem_window (m : ℤ) : m ∈ window ↔ -12 ≤ m ∧ m ≤ 12 := by
  simp only [window, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨(m + 12).toNat, by omega, by omega⟩

/-- The printed lowest weights `h_{A_L}` (table at lines 3167–3177). -/
def hOf : Bool → ℕ → ℚ
  | false, 0 => 0 | false, 1 => 2 / 15 | false, 2 => 2 / 5 | false, 3 => 4 / 5
  | false, 4 => 1 / 3 | false, 5 => 1 | false, 6 => 4 / 5
  | true, 0 => 2 / 5 | true, 1 => 8 / 15 | true, 2 => 4 / 5 | true, 3 => 1 / 5
  | true, 4 => 11 / 15 | true, 5 => 2 / 5 | true, 6 => 1 / 5
  | _, _ => 0

/-- The certificate: the minimizing right charges of each top. -/
def minsOf : Bool → ℕ → List ℤ
  | false, 0 => [0]
  | false, 1 => [0]
  | false, 2 => [-3, 0, 3]
  | false, 3 => [-6, -3, -2, 0, 2, 3, 6]
  | false, 4 => [-6, 6]
  | false, 5 => [-12, -9, -6, -4, -1, 1, 4, 6, 9, 12]
  | false, 6 => [-9, -4, 4, 9]
  | true, 0 => [0]
  | true, 1 => [-8, -5, 0, 5, 8]
  | true, 2 => [-10, -8, -5, -3, -2, 0, 2, 3, 5, 8, 10]
  | true, 3 => [-2, 2]
  | true, 4 => [-7, -6, -4, -2, -1, 1, 2, 4, 6, 7]
  | true, 5 => [-4, -1, 1, 4]
  | true, 6 => [-4, 4]
  | _, _ => []

/-- The certificate is correct on the window: `h` is a lower bound for every windowed
energy, and the energy equals `h` exactly on the listed charges. -/
theorem window_certificate :
    ∀ tau ∈ [false, true], ∀ a ∈ List.range 7,
      (∀ m ∈ window, hOf tau a ≤ energy tau a m) ∧
      (∀ m ∈ window, energy tau a m = hOf tau a ↔ m ∈ minsOf tau a) ∧
      (∀ m ∈ minsOf tau a, m ∈ window) := by
  decide +kernel

/-- The parafermion lowest weights are nonnegative. -/
theorem hPF_nonneg : ∀ a ∈ List.range 7, ∀ k ∈ (List.range 13).map (fun i : ℕ => (i : ℤ) - 6),
    0 ≤ hPF a k := by
  decide +kernel

theorem bal13_mem (n : ℤ) : bal13 n ∈ (List.range 13).map (fun i : ℕ => (i : ℤ) - 6) := by
  simp only [List.mem_map, List.mem_range, bal13]
  have h0 : 0 ≤ (n + 6) % 13 := Int.emod_nonneg _ (by norm_num)
  have h1 : (n + 6) % 13 < 13 := Int.emod_lt_of_pos _ (by norm_num)
  exact ⟨((n + 6) % 13).toNat, by omega, by omega⟩

theorem pfE_nonneg (a : ℕ) (ha : a < 7) (m : ℤ) : 0 ≤ pfE a m :=
  hPF_nonneg a (List.mem_range.2 ha) _ (bal13_mem _)

theorem leftE_nonneg (m : ℤ) : 0 ≤ leftE m := by
  unfold leftE; split_ifs <;> norm_num

theorem potts_nonneg (tau : Bool) (m : ℤ) : 0 ≤ potts tau m := by
  unfold potts; split_ifs <;> norm_num

/-- Charges with `|m| ≥ 13` have energy at least `169/156`. -/
theorem energy_large (tau : Bool) (a : ℕ) (ha : a < 7) (m : ℤ) (hm : 13 ≤ |m|) :
    (169 : ℚ) / 156 ≤ energy tau a m := by
  have h1 : (169 : ℤ) ≤ m ^ 2 := by
    have := abs_mul_abs_self m
    nlinarith [abs_nonneg m]
  have h2 : (169 : ℚ) ≤ (m : ℚ) ^ 2 := by exact_mod_cast h1
  unfold energy
  have := leftE_nonneg m
  have := potts_nonneg tau m
  have := pfE_nonneg a ha m
  linarith

theorem hOf_le_one : ∀ tau ∈ [false, true], ∀ a ∈ List.range 7, hOf tau a ≤ 1 := by
  decide +kernel

/-- **The printed lowest weights are the minima over all integer charges, and the
certificate lists exactly the minimizers.** -/
theorem minimizers_spec (tau : Bool) (a : ℕ) (ha : a < 7) (m : ℤ) :
    hOf tau a ≤ energy tau a m ∧ (energy tau a m = hOf tau a ↔ m ∈ minsOf tau a) := by
  have htau : tau ∈ [false, true] := by cases tau <;> simp
  have ha' : a ∈ List.range 7 := List.mem_range.2 ha
  obtain ⟨hlow, hiff, hsub⟩ := window_certificate tau htau a ha'
  by_cases hw : m ∈ window
  · exact ⟨hlow m hw, hiff m hw⟩
  · have hm : 13 ≤ |m| := by
      rw [mem_window] at hw
      rcases le_or_gt 0 m with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    have hbig := energy_large tau a ha m hm
    have hle := hOf_le_one tau htau a ha'
    refine ⟨by linarith, ⟨fun h => ?_, fun h => absurd (hsub m h) hw⟩⟩
    linarith

/-- Top dimension `D = ∑ mult` over the minimizers. -/
def dimOf (tau : Bool) (a : ℕ) : ℕ := ((minsOf tau a).map mult).sum

/-- The traces over the top: left energy `L`, `Q = Tr H_R(0)²`, Potts `P`, parafermion `Z`. -/
def traceL (tau : Bool) (a : ℕ) : ℚ := ((minsOf tau a).map fun m => (mult m : ℚ) * leftE m).sum
def traceQ (tau : Bool) (a : ℕ) : ℚ := ((minsOf tau a).map fun m => (mult m : ℚ) * m ^ 2).sum
def traceP (tau : Bool) (a : ℕ) : ℚ :=
  ((minsOf tau a).map fun m => (mult m : ℚ) * potts tau m).sum
def traceZ (tau : Bool) (a : ℕ) : ℚ := ((minsOf tau a).map fun m => (mult m : ℚ) * pfE a m).sum

/-- The stress-trace contribution `W = L + (83/6084) Q + (25/6) P + (25/26) Z` (eq:top-W). -/
def topW (tau : Bool) (a : ℕ) : ℚ :=
  traceL tau a + 83 / 6084 * traceQ tau a + 25 / 6 * traceP tau a + 25 / 26 * traceZ tau a

/-- **The printed dimensions and weighted traces** (table at lines 3153–3162). -/
theorem dims_and_traces :
    ((List.range 7).map fun a => (dimOf false a, 4680 * topW false a)) =
      [(1, 0), (1, 600), (5, 10440), (9, 56640), (2, 5520), (14, 148560), (6, 54240)] ∧
    ((List.range 7).map fun a => (dimOf true a, 4680 * topW true a)) =
      [(1, 7800), (7, 36960), (15, 110880), (2, 4080), (14, 81480), (6, 18240), (2, 4920)] := by
  decide +kernel

/-- The two row checks of line 3181:
`h D = L + Q/156 + P + Z` and `W = L/26 + 7Q/936 + 125P/39 + (25/26) h D`. -/
theorem row_identities :
    ∀ tau ∈ [false, true], ∀ a ∈ List.range 7,
      hOf tau a * dimOf tau a = traceL tau a + traceQ tau a / 156 + traceP tau a + traceZ tau a ∧
      topW tau a = traceL tau a / 26 + 7 / 936 * traceQ tau a + 125 / 39 * traceP tau a
        + 25 / 26 * (hOf tau a * dimOf tau a) := by
  decide +kernel

/-- The minimizing `|j|` of the printed table. -/
theorem minimal_abs_j :
    ((List.range 7).map fun a =>
        (List.range 7).filter fun n => (minsOf false a).any fun m => (bal13 m).natAbs == n) =
      [[0], [0], [0, 3], [0, 2, 3, 6], [6], [1, 4, 6], [4]] ∧
    ((List.range 7).map fun a =>
        (List.range 7).filter fun n => (minsOf true a).any fun m => (bal13 m).natAbs == n) =
      [[0], [0, 5], [0, 2, 3, 5], [2], [1, 2, 4, 6], [1, 4], [4]] := by
  decide +kernel

/-- The multiplicity of right charge `c` in a top. -/
def charMult (tau : Bool) (a : ℕ) (c : ℤ) : ℕ := (((minsOf tau a).filter fun m => m = c).map mult).sum

/-- Differences `char(10) - char(12)` and `char(7) - char(9)` per top. -/
def d10 (tau : Bool) (a : ℕ) : ℤ := (charMult tau a 10 : ℤ) - charMult tau a 12
def d7 (tau : Bool) (a : ℕ) : ℤ := (charMult tau a 7 : ℤ) - charMult tau a 9

theorem d_values :
    d10 false 0 = 0 ∧ d10 false 1 = 0 ∧ d10 false 2 = 0 ∧ d10 false 3 = 0 ∧ d10 false 4 = 0 ∧
    d10 false 5 = -1 ∧ d10 false 6 = 0 ∧
    d10 true 0 = 0 ∧ d10 true 1 = 0 ∧ d10 true 2 = 1 ∧ d10 true 3 = 0 ∧ d10 true 4 = 0 ∧
    d10 true 5 = 0 ∧ d10 true 6 = 0 ∧
    d7 false 0 = 0 ∧ d7 false 1 = 0 ∧ d7 false 2 = 0 ∧ d7 false 3 = 0 ∧ d7 false 4 = 0 ∧
    d7 false 5 = -2 ∧ d7 false 6 = -2 ∧
    d7 true 0 = 0 ∧ d7 true 1 = 0 ∧ d7 true 2 = 0 ∧ d7 true 3 = 0 ∧ d7 true 4 = 2 ∧
    d7 true 5 = 0 ∧ d7 true 6 = 0 := by
  decide +kernel

/-- Right-charge multiplicity of a top containing `x_a, y_a` with multiplicities `x a, y a`. -/
def nMult (x y : ℕ → ℕ) (c : ℤ) : ℤ :=
  ∑ a ∈ Finset.range 7, ((x a : ℤ) * charMult false a c + (y a : ℤ) * charMult true a c)

/-- **The two `𝔰𝔩₂` character inequalities** (line 3185).  For a finite-dimensional
`𝔰𝔩₂`-module the weight multiplicities satisfy `n(c+2) ≤ n(c)` for `c ≥ 0`; at `c = 10`
and `c = 7` this gives `y₂ ≥ x₅` and `y₄ ≥ x₅ + x₆`. -/
theorem sl2_inequalities (x y : ℕ → ℕ)
    (hmono : ∀ c : ℤ, 0 ≤ c → nMult x y (c + 2) ≤ nMult x y c) :
    x 5 ≤ y 2 ∧ x 5 + x 6 ≤ y 4 := by
  have h10 := hmono 10 (by norm_num)
  have h7 := hmono 7 (by norm_num)
  have e10 : nMult x y 10 - nMult x y (10 + 2) =
      ∑ a ∈ Finset.range 7, ((x a : ℤ) * d10 false a + (y a : ℤ) * d10 true a) := by
    simp only [nMult, d10, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    norm_num
    ring
  have e7 : nMult x y 7 - nMult x y (7 + 2) =
      ∑ a ∈ Finset.range 7, ((x a : ℤ) * d7 false a + (y a : ℤ) * d7 true a) := by
    simp only [nMult, d7, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    norm_num
    ring
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6,
    c0, c1, c2, c3, c4, c5, c6, f0, f1, f2, f3, f4, f5, f6⟩ := d_values
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5, a6,
    b0, b1, b2, b3, b4, b5, b6, c0, c1, c2, c3, c4, c5, c6, f0, f1, f2, f3, f4, f5, f6] at e10 e7
  constructor <;> omega

/-- **The universal top bound** (eq:sharp-top-bound).  For a top containing the fourteen
core tops with multiplicities `x a, y a` whose right-charge multiplicities are those of an
`𝔰𝔩₂`-module, the weighted trace satisfies `10·(4680 W_total) ≤ 17·4680·D`, where
`W_total = ∑ x_a W(x_a) + ∑ y_a W(y_a)` and `D = ∑ x_a dim(x_a) + ∑ y_a dim(y_a)` are
computed from the charge formulas.  With `W_total = h D` this is `h ≤ 17/10`. -/
theorem universal_top_bound (x y : ℕ → ℕ)
    (hmono : ∀ c : ℤ, 0 ≤ c → nMult x y (c + 2) ≤ nMult x y c) :
    10 * ∑ a ∈ Finset.range 7, ((x a : ℚ) * (4680 * topW false a) + (y a : ℚ) * (4680 * topW true a)) ≤
      17 * 4680 * ∑ a ∈ Finset.range 7, ((x a : ℚ) * dimOf false a + (y a : ℚ) * dimOf true a) := by
  obtain ⟨h52, h564⟩ := sl2_inequalities x y hmono
  have key := HaagerupIzumi.CFT.core_top_bound (fun i : Fin 7 => (x i : ℝ)) (fun i : Fin 7 => (y i : ℝ))
    (fun i => by positivity) (fun i => by positivity) (by exact_mod_cast h52)
    (by exact_mod_cast h564)
  obtain ⟨hx, hy⟩ := dims_and_traces
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, Prod.mk.injEq] at hx hy
  obtain ⟨⟨dx0, wx0⟩, ⟨dx1, wx1⟩, ⟨dx2, wx2⟩, ⟨dx3, wx3⟩, ⟨dx4, wx4⟩, ⟨dx5, wx5⟩, ⟨dx6, wx6⟩, -⟩ := hx
  obtain ⟨⟨dy0, wy0⟩, ⟨dy1, wy1⟩, ⟨dy2, wy2⟩, ⟨dy3, wy3⟩, ⟨dy4, wy4⟩, ⟨dy5, wy5⟩, ⟨dy6, wy6⟩, -⟩ := hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, dx0, dx1, dx2, dx3, dx4, dx5, dx6,
    dy0, dy1, dy2, dy3, dy4, dy5, dy6, wx0, wx1, wx2, wx3, wx4, wx5, wx6,
    wy0, wy1, wy2, wy3, wy4, wy5, wy6]
  simp only [HaagerupIzumi.CFT.coreTopScaledTrace, HaagerupIzumi.CFT.coreTopDimension] at key
  have key' : (10 : ℚ) * (600 * x 1 + 10440 * x 2 + 56640 * x 3 + 5520 * x 4
      + 148560 * x 5 + 54240 * x 6 + 7800 * y 0 + 36960 * y 1
      + 110880 * y 2 + 4080 * y 3 + 81480 * y 4 + 18240 * y 5 + 4920 * y 6) ≤
      17 * 4680 * (x 0 + x 1 + 5 * x 2 + 9 * x 3 + 2 * x 4 + 14 * x 5 + 6 * x 6
      + y 0 + 7 * y 1 + 15 * y 2 + 2 * y 3 + 14 * y 4 + 6 * y 5 + 2 * y 6) := by
    exact_mod_cast key
  push_cast
  linarith [key']


/-- **eq:sharp-top-bound for the lowest weight.**  If the top-trace identity
`W_total = h · D` (eq:top-trace, Lemma `lem:vacuum-projective`) holds for a top with
multiplicities `x a, y a` whose right-charge multiplicities are those of an `𝔰𝔩₂`-module, and
`D > 0`, then `h ≤ 17/10`. -/
theorem lowest_weight_le_of_trace (x y : ℕ → ℕ)
    (hmono : ∀ c : ℤ, 0 ≤ c → nMult x y (c + 2) ≤ nMult x y c) (h : ℚ)
    (htrace : ∑ a ∈ Finset.range 7, ((x a : ℚ) * topW false a + (y a : ℚ) * topW true a) =
      h * ∑ a ∈ Finset.range 7, ((x a : ℚ) * dimOf false a + (y a : ℚ) * dimOf true a))
    (hD : 0 < ∑ a ∈ Finset.range 7, ((x a : ℚ) * dimOf false a + (y a : ℚ) * dimOf true a)) :
    h ≤ 17 / 10 := by
  have hb := universal_top_bound x y hmono
  have e : ∑ a ∈ Finset.range 7,
      ((x a : ℚ) * (4680 * topW false a) + (y a : ℚ) * (4680 * topW true a)) =
      4680 * ∑ a ∈ Finset.range 7, ((x a : ℚ) * topW false a + (y a : ℚ) * topW true a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e, htrace] at hb
  nlinarith

#print axioms lowest_weight_le_of_trace
#print axioms minimizers_spec
#print axioms dims_and_traces
#print axioms universal_top_bound

end HaagerupIzumi.C8.CoreTops
