module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# Lowest weights of the order-thirteen core tops

Kernel-checked computation of the charge minimizations of Section `sec:branching`
(lines 3096–3198 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).

* `coreTerm ε m = m²/156 + [m odd]/4 + p_ε(m)` (eq:core-charge-minimum), with
  `ε = false` for the label `1` and `ε = true` for `τ`.  `hT ε j` is its minimum over the
  window `-12 ≤ m ≤ 12`, `m ≡ j (mod 13)`, computed exactly (`hTScaled`).  It is the minimum
  over the *whole* residue class (`hT_le`, `hT_attained`): every residue has a representative
  with `|m| ≤ 6` and value at most `14/13` (`small_representative`), while `|m| ≥ 13` gives
  `m²/156 > 14/13` (`large_charge`).
* `hPF a k = a(a+1)/15 - k²/13 + max(0,|k|-a)` (eq:pf-charge-minimum), evaluated at the
  representative `rep13 k ∈ [-6, 6]`.
* `hAL ε a = min_{j ∈ ℤ/13} (h_T(ε,j) + h_PF(a,-5j))`; `hAL_table` gives the fourteen
  values `h_{A_L}` of `x_a` (`ε = false`) and `y_a` (`ε = true`) printed at lines 3167–3177,
  `hAL_le_all` that they are lower bounds for every `j`, and `hAL_minimizers` the printed
  sets of minimizing absolute charges `|j|`.
* `topDim_eq_table`, `topW13_eq_table`: summing over all minimizing `j` and all tied
  minimizing `m` (left singlet for even `m`, doublet for odd `m`; one-dimensional Potts
  and parafermion tops, as stated at lines 3111 and 3123) reproduces the printed top
  dimensions `d` and trace contributions `4680 W` (lines 3153–3162), with
  `W = L + 83Q/6084 + 25P/6 + 25Z/26`; `topEnergy_eq` is the check `W_total = h D`.

All quantities are computed exactly with the common denominator `780`; the rational
statements follow by casting.  There are no hypotheses.  The identification of these
formulas with the actual lowest weights of the lattice–Potts and parafermion modules is the
input cited in the manuscript (`ALY`, the core-extension certificate) and is not asserted.
-/

namespace HaagerupIzumi.C8
namespace CoreCharges

/-! ## Integer computation (scaled by `780`) -/

/-- `780 p_ε(m)`. -/
def pScaled (ε : Bool) (m : ℤ) : ℤ :=
  if ε then (if m % 3 = 0 then 312 else 52) else (if m % 3 = 0 then 0 else 520)

/-- `780 (m²/156 + [m odd]/4 + p_ε(m))`. -/
def termScaled (ε : Bool) (m : ℤ) : ℤ :=
  5 * m ^ 2 + (if m % 2 = 1 then 195 else 0) + pScaled ε m

/-- The window `-12 ≤ m ≤ 12`. -/
def window : List ℤ := (List.range 25).map fun i : ℕ => (i : ℤ) - 12

theorem mem_window (m : ℤ) : m ∈ window ↔ -12 ≤ m ∧ m ≤ 12 := by
  simp only [window, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hm
    exact ⟨(m + 12).toNat, by omega, by omega⟩

/-- `780 h_T(ε,j)`: minimum of `termScaled ε m` over the window with `m ≡ j (mod 13)`. -/
def hTScaled (ε : Bool) (j : Fin 13) : ℤ :=
  ((window.filter fun m => decide ((m - ((j : ℕ) : ℤ)) % 13 = 0)).map (termScaled ε)).foldr
    min 1000000

theorem hTScaled_le : ∀ p : Bool × Fin 13, ∀ m ∈ window,
    (m - ((p.2 : ℕ) : ℤ)) % 13 = 0 → hTScaled p.1 p.2 ≤ termScaled p.1 m := by
  decide +kernel

theorem hTScaled_attained : ∀ p : Bool × Fin 13, ∃ m ∈ window,
    (m - ((p.2 : ℕ) : ℤ)) % 13 = 0 ∧ termScaled p.1 m = hTScaled p.1 p.2 := by
  decide +kernel

/-- Every residue has a representative `|m| ≤ 6` of value at most `840 = 780 · 14/13`. -/
theorem small_representative_scaled : ∀ p : Bool × Fin 13, ∃ m ∈ window,
    -6 ≤ m ∧ m ≤ 6 ∧ (m - ((p.2 : ℕ) : ℤ)) % 13 = 0 ∧ termScaled p.1 m ≤ 840 := by
  decide +kernel

theorem hTScaled_le_840 : ∀ p : Bool × Fin 13, hTScaled p.1 p.2 ≤ 840 := by
  decide +kernel

theorem five_mul_sq_le_termScaled (ε : Bool) (m : ℤ) : 5 * m ^ 2 ≤ termScaled ε m := by
  unfold termScaled pScaled
  split_ifs <;> linarith

/-- The window contains every minimizer: the minimum over the window is a lower bound on
the whole residue class. -/
theorem hTScaled_le_all (ε : Bool) (j : Fin 13) (m : ℤ)
    (hm : (m - ((j : ℕ) : ℤ)) % 13 = 0) : hTScaled ε j ≤ termScaled ε m := by
  by_cases hw : -12 ≤ m ∧ m ≤ 12
  · exact hTScaled_le (ε, j) m ((mem_window m).mpr hw) hm
  · have h1 : hTScaled ε j ≤ 840 := hTScaled_le_840 (ε, j)
    have h2 := five_mul_sq_le_termScaled ε m
    have h3 : 169 ≤ m ^ 2 := by
      rcases (show 13 ≤ m ∨ m ≤ -13 by omega) with h | h <;> nlinarith
    linarith

/-- Representative of `k mod 13` in `[-6, 6]`. -/
def rep13 (k : ℤ) : ℤ := if k % 13 ≤ 6 then k % 13 else k % 13 - 13

theorem rep13_spec (k : ℤ) : -6 ≤ rep13 k ∧ rep13 k ≤ 6 ∧ (k - rep13 k) % 13 = 0 := by
  unfold rep13
  split_ifs <;> omega

/-- `780 h_PF(a,k)`. -/
def hPFScaled (a : ℕ) (k : ℤ) : ℤ := 52 * a * (a + 1) - 60 * k ^ 2 + 780 * max 0 (|k| - a)

/-- `780 h_{A_L}`: minimum over `j ∈ ℤ/13` of `780 (h_T(ε,j) + h_PF(a,-5j))`. -/
def hALScaled (ε : Bool) (a : ℕ) : ℤ :=
  ((List.finRange 13).map fun j =>
    hTScaled ε j + hPFScaled a (rep13 (-5 * ((j : ℕ) : ℤ)))).foldr min 1000000

/-- The printed values `780 h_{A_L}` (lines 3169–3175). -/
def hALTable : Bool → Fin 7 → ℤ
  | false => ![0, 104, 312, 624, 260, 780, 624]
  | true => ![312, 416, 624, 156, 572, 312, 156]

theorem hALScaled_eq_table : ∀ p : Bool × Fin 7, hALScaled p.1 (p.2 : ℕ) = hALTable p.1 p.2 := by
  decide +kernel

theorem hAL_le_scaled : ∀ q : (Bool × Fin 7) × Fin 13,
    hALTable q.1.1 q.1.2 ≤
      hTScaled q.1.1 q.2 + hPFScaled (q.1.2 : ℕ) (rep13 (-5 * ((q.2 : ℕ) : ℤ))) := by
  decide +kernel

/-- The printed sets of minimizing absolute charges `|j|` (lines 3169–3175). -/
def minimizers : Bool → Fin 7 → List ℕ
  | false => ![[0], [0], [0, 3], [0, 2, 3, 6], [6], [1, 4, 6], [4]]
  | true => ![[0], [0, 5], [0, 2, 3, 5], [2], [1, 2, 4, 6], [1, 4], [4]]

/-- `j` attains the minimum exactly when `|j|` is in the printed set. -/
theorem hAL_minimizers : ∀ q : (Bool × Fin 7) × Fin 13,
    (hTScaled q.1.1 q.2 + hPFScaled (q.1.2 : ℕ) (rep13 (-5 * ((q.2 : ℕ) : ℤ))) =
        hALTable q.1.1 q.1.2 ↔
      min (q.2 : ℕ) (13 - (q.2 : ℕ)) ∈ minimizers q.1.1 q.1.2) := by
  decide +kernel

/-! ## The rational statements -/

/-- `p_ε(m)` (line 3099). -/
def pQ (ε : Bool) (m : ℤ) : ℚ :=
  if ε then (if m % 3 = 0 then 2 / 5 else 1 / 15) else (if m % 3 = 0 then 0 else 2 / 3)

/-- `m²/156 + [m odd]/4 + p_ε(m)` (eq:core-charge-minimum); `m % 2 = 1` means `m` odd. -/
def coreTerm (ε : Bool) (m : ℤ) : ℚ :=
  (m : ℚ) ^ 2 / 156 + (if m % 2 = 1 then 1 / 4 else 0) + pQ ε m

theorem coreTerm_eq (ε : Bool) (m : ℤ) : coreTerm ε m = (termScaled ε m : ℚ) / 780 := by
  unfold coreTerm pQ termScaled pScaled
  split_ifs <;> push_cast <;> ring

/-- `h_T(ε,j)`. -/
def hT (ε : Bool) (j : Fin 13) : ℚ := (hTScaled ε j : ℚ) / 780

/-- `h_T(ε,j)` bounds the charge function on the whole residue class `m ≡ j (mod 13)`. -/
theorem hT_le (ε : Bool) (j : Fin 13) (m : ℤ) (hm : (m - ((j : ℕ) : ℤ)) % 13 = 0) :
    hT ε j ≤ coreTerm ε m := by
  rw [coreTerm_eq, hT]
  have h := hTScaled_le_all ε j m hm
  have h' : (hTScaled ε j : ℚ) ≤ (termScaled ε m : ℚ) := by exact_mod_cast h
  linarith

/-- ... and is attained in the window `-12 ≤ m ≤ 12`. -/
theorem hT_attained (ε : Bool) (j : Fin 13) :
    ∃ m : ℤ, -12 ≤ m ∧ m ≤ 12 ∧ (m - ((j : ℕ) : ℤ)) % 13 = 0 ∧ coreTerm ε m = hT ε j := by
  obtain ⟨m, hmw, hm, heq⟩ := hTScaled_attained (ε, j)
  have heq' : termScaled ε m = hTScaled ε j := heq
  refine ⟨m, ((mem_window m).mp hmw).1, ((mem_window m).mp hmw).2, hm, ?_⟩
  rw [coreTerm_eq, hT, heq']

/-- `|m| ≥ 13` gives `m²/156 > 14/13`. -/
theorem large_charge (m : ℤ) (hm : 13 ≤ |m|) : (14 : ℚ) / 13 < (m : ℚ) ^ 2 / 156 := by
  have h13 : (13 : ℚ) ≤ |(m : ℚ)| := by exact_mod_cast hm
  have h : (169 : ℚ) ≤ (m : ℚ) ^ 2 := by
    nlinarith [abs_nonneg (m : ℚ), sq_abs (m : ℚ)]
  linarith

/-- Choosing `|m| ≤ 6` bounds the minimum by `14/13`. -/
theorem small_representative (ε : Bool) (j : Fin 13) :
    ∃ m : ℤ, |m| ≤ 6 ∧ (m - ((j : ℕ) : ℤ)) % 13 = 0 ∧ coreTerm ε m ≤ 14 / 13 := by
  obtain ⟨m, -, hlo, hhi, hm, hle⟩ := small_representative_scaled (ε, j)
  refine ⟨m, abs_le.mpr ⟨hlo, hhi⟩, hm, ?_⟩
  rw [coreTerm_eq]
  have h' : (termScaled ε m : ℚ) ≤ 840 := by exact_mod_cast hle
  linarith

/-- `h_PF(a,k) = a(a+1)/15 - k²/13 + max(0,|k|-a)` (eq:pf-charge-minimum). -/
def hPF (a : ℕ) (k : ℤ) : ℚ :=
  (a : ℚ) * (a + 1) / 15 - (k : ℚ) ^ 2 / 13 + ((max 0 (|k| - (a : ℤ)) : ℤ) : ℚ)

theorem hPF_eq (a : ℕ) (k : ℤ) : hPF a k = (hPFScaled a k : ℚ) / 780 := by
  unfold hPF hPFScaled
  push_cast
  ring

/-- `h_{A_L}` for `x_a` (`ε = false`) and `y_a` (`ε = true`). -/
def hAL (ε : Bool) (a : ℕ) : ℚ := (hALScaled ε a : ℚ) / 780

/-- The printed table of `h_{A_L}` (lines 3167–3177). -/
def hALTableQ : Bool → Fin 7 → ℚ
  | false => ![0, 2 / 15, 2 / 5, 4 / 5, 1 / 3, 1, 4 / 5]
  | true => ![2 / 5, 8 / 15, 4 / 5, 1 / 5, 11 / 15, 2 / 5, 1 / 5]

theorem hALTableQ_eq : ∀ p : Bool × Fin 7, hALTableQ p.1 p.2 = (hALTable p.1 p.2 : ℚ) / 780 := by
  decide +kernel

/-- The fourteen values `h_{A_L}(x_a)`, `h_{A_L}(y_a)` agree with the printed table. -/
theorem hAL_table (ε : Bool) (a : Fin 7) : hAL ε a = hALTableQ ε a := by
  have h1 : hALScaled ε a = hALTable ε a := hALScaled_eq_table (ε, a)
  have h2 : hALTableQ ε a = (hALTable ε a : ℚ) / 780 := hALTableQ_eq (ε, a)
  rw [hAL, h1, h2]

/-- Each printed value is at most `h_T(ε,j) + h_PF(a,-5j)` for every `j`. -/
theorem hAL_le_all (ε : Bool) (a : Fin 7) (j : Fin 13) :
    hALTableQ ε a ≤ hT ε j + hPF a (rep13 (-5 * ((j : ℕ) : ℤ))) := by
  have h1 : hALTableQ ε a = (hALTable ε a : ℚ) / 780 := hALTableQ_eq (ε, a)
  have h2 : hALTable ε a ≤ hTScaled ε j + hPFScaled a (rep13 (-5 * ((j : ℕ) : ℤ))) :=
    hAL_le_scaled ((ε, a), j)
  have h3 : ((hALTable ε a : ℤ) : ℚ) ≤
      ((hTScaled ε j + hPFScaled a (rep13 (-5 * ((j : ℕ) : ℤ))) : ℤ) : ℚ) :=
    Int.cast_le.mpr h2
  push_cast at h3
  rw [h1, hT, hPF_eq]
  linarith


/-! ## Top dimensions and stress traces (lines 3134–3163) -/

/-- Whether the charge `j` attains `h_{A_L}(ε,a)`. -/
def isMinCharge (ε : Bool) (a : ℕ) (j : Fin 13) : Bool :=
  decide (hTScaled ε j + hPFScaled a (rep13 (-5 * ((j : ℕ) : ℤ))) = hALScaled ε a)

/-- The minimizing representatives `m ∈ [-12,12]` of the residue `j` (ties included). -/
def minReps (ε : Bool) (j : Fin 13) : List ℤ :=
  window.filter fun m => decide ((m - ((j : ℕ) : ℤ)) % 13 = 0 ∧ termScaled ε m = hTScaled ε j)

/-- Left affine multiplicity: an even minimizing `m` gives a left singlet, an odd one a
left doublet (line 3111). -/
def leftMult (m : ℤ) : ℤ := if m % 2 = 1 then 2 else 1

/-- Sum of `f j m` over the top: minimizing charges `j` and their minimizing `m`. -/
def topSum (ε : Bool) (a : ℕ) (f : Fin 13 → ℤ → ℤ) : ℤ :=
  ((List.finRange 13).map fun j =>
    if isMinCharge ε a j then ((minReps ε j).map (f j)).sum else 0).sum

/-- Dimension of the `A_L` top, assuming one-dimensional Potts and parafermion tops. -/
def topDim (ε : Bool) (a : ℕ) : ℤ := topSum ε a fun _ m => leftMult m

/-- `13 · 4680 W`, where each state contributes `L = [m odd]/4`, `Q = m²`, `P = p_ε(m)`
and `Z = h_PF(a,-5j)` to `W = L + 83Q/6084 + 25P/6 + 25Z/26` (eq:top-W). -/
def topW13 (ε : Bool) (a : ℕ) : ℤ := topSum ε a fun j m =>
  leftMult m * (15210 * (if m % 2 = 1 then 1 else 0) + 830 * m ^ 2 + 325 * pScaled ε m
    + 75 * hPFScaled a (rep13 (-5 * ((j : ℕ) : ℤ))))

/-- The printed top dimensions `d` (line 3153). -/
def topDimTable : Bool → Fin 7 → ℤ
  | false => ![1, 1, 5, 9, 2, 14, 6]
  | true => ![1, 7, 15, 2, 14, 6, 2]

/-- The printed trace contributions `4680 W` (line 3153). -/
def topWTable : Bool → Fin 7 → ℤ
  | false => ![0, 600, 10440, 56640, 5520, 148560, 54240]
  | true => ![7800, 36960, 110880, 4080, 81480, 18240, 4920]

theorem topDim_eq_table : ∀ p : Bool × Fin 7, topDim p.1 (p.2 : ℕ) = topDimTable p.1 p.2 := by
  decide +kernel

theorem topW13_eq_table :
    ∀ p : Bool × Fin 7, topW13 p.1 (p.2 : ℕ) = 13 * topWTable p.1 p.2 := by
  decide +kernel

/-- The total energy check `W_total = h D` at the level of the core: every state of the top
has core-plus-parafermion energy `h_{A_L}`, i.e. `Z = h d - L - Q/156 - P` (line 3181). -/
theorem topEnergy_eq : ∀ p : Bool × Fin 7,
    topSum p.1 (p.2 : ℕ) (fun j m =>
      leftMult m * (termScaled p.1 m + hPFScaled (p.2 : ℕ) (rep13 (-5 * ((j : ℕ) : ℤ))))) =
      hALScaled p.1 (p.2 : ℕ) * topDim p.1 (p.2 : ℕ) := by
  decide +kernel

#print axioms hTScaled_le
#print axioms hTScaled_attained
#print axioms hTScaled_le_all
#print axioms hT_le
#print axioms hT_attained
#print axioms large_charge
#print axioms small_representative
#print axioms hALScaled_eq_table
#print axioms hAL_minimizers
#print axioms hAL_table
#print axioms hAL_le_all
#print axioms topDim_eq_table
#print axioms topW13_eq_table
#print axioms topEnergy_eq

end CoreCharges
end HaagerupIzumi.C8
