module

public import HaagerupIzumi.C8.Lattice.Model

@[expose] public section

/-!
# The transported PCT involution `θ_g` on the Fock model

The map of manuscript `eq:pct` (`c8_expanded_20260929/haagerup_c8_expanded.tex`, lines
1975–1989, "the transported involution `θ_g = g θ g⁻¹`"): with `c̃ = (5, 8, 9, 8, 5, 1, 2, 2)`,
```
θ_g (h₁(-n₁) ⋯ h_r(-n_r) e^α) = (-1)^r (∏ᵢ c̃ᵢ^{αᵢ}) h₁(-n₁) ⋯ h_r(-n_r) e^{-α},
```
antilinear on coefficients (it fixes `√13` and negates `√-3`).  This is also the function
`pct` of `hi_cft_20260923_c8_exact_check.py` (record
`hi_cft_20260923_c8_exact_unitary_certificate.json`, `exact_PCT_preservation`) used by
`lean/tools/lattice_export/export_pct.py`; the oscillator codes `k` stand for `h_{k%8}(-(k/8+1))`
in the simple-root basis, as everywhere in `Lattice/`.

* Computable side (for kernel checks): `pctGauge`, `pctSign`, `pctState`, `pctCoef`, `pctVec`
  (rational vectors), `pct4` (vectors over `ℚ(√13, √-3)`: components `1, s, t, st` go to
  `1, s, -t, -st`), and `sort4` (re-sorting by balanced merging, since `α ↦ -α` reverses the
  order of momenta).
* Semantic side: `pctV : V →+ V`, the additive map with
  `pctV (single s c) = single (θ s) (conj c · (-1)^r ∏ c̃ᵢ^{αᵢ})` (`pctV_single`); it is
  conjugate-linear (`pctV_smul`) and an involution (`pctV_pctV`, the manuscript's "squares to
  the identity").
* Links: `pctV_toV`, `pctV_toV4` (`pctV (toV4 x) = toV4 (pct4 x)` on canonical states) and
  `toV4_sort4`.

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## The computable map -/

/-- `c ^ n` for `n : ℤ`, by structural recursion (kernel-evaluable). -/
def zp (c : ℚ) : ℤ → ℚ
  | .ofNat n => c ^ n
  | .negSucc n => (c ^ (n + 1))⁻¹

/-- The gauge factor `∏ᵢ c̃ᵢ^{αᵢ}`, `c̃ = (5, 8, 9, 8, 5, 1, 2, 2)`. -/
def pctGauge (a : Mom) : ℚ :=
  zp 5 a.x0 * zp 8 a.x1 * zp 9 a.x2 * zp 8 a.x3 * zp 5 a.x4 * zp 1 a.x5 * zp 2 a.x6 * zp 2 a.x7

/-- `(-1)^r` for `r` oscillators. -/
def pctSign (osc : List ℕ) : ℚ := if osc.length % 2 = 0 then 1 else -1

/-- `h(-n) ⋯ e^α ↦ h(-n) ⋯ e^{-α}`. -/
def pctState (s : State) : State := (Mom.neg s.1, s.2)

/-- The rational factor `(-1)^r ∏ c̃ᵢ^{αᵢ}` of `eq:pct`. -/
def pctCoef (s : State) : ℚ := pctSign s.2 * pctGauge s.1

/-- `θ_g` on rational sparse vectors (unsorted output). -/
def pctVec (v : Vec) : Vec := v.map fun p => (pctState p.1, pctCoef p.1 * p.2)

/-- `θ_g` on vectors over `ℚ(√13, √-3)`: antilinear, `√-3 ↦ -√-3`. -/
def pct4 (x : Vec4) : Vec4 :=
  ⟨pctVec x.c0, pctVec x.c1, smul (-1) (pctVec x.c2), smul (-1) (pctVec x.c3)⟩

/-- Sorting (and merging) a sparse vector by balanced merging of its terms. -/
def sortVec (v : Vec) : Vec := mergeAll v.length (v.map fun p => [p])

def sort4 (x : Vec4) : Vec4 := ⟨sortVec x.c0, sortVec x.c1, sortVec x.c2, sortVec x.c3⟩

/-! ## The map on `V` -/

/-- `θ_g` on canonical monomials. -/
def pctValid (s : ValidState) : ValidState := ⟨pctState s.1, s.2⟩

/-- **The transported PCT involution `θ_g` on `V`** (additive, conjugate-linear). -/
noncomputable def pctV : V →+ V :=
  Finsupp.liftAddHom fun s : ValidState =>
    (Finsupp.singleAddHom (pctValid s)).comp
      ((AddMonoidHom.mulRight ((pctCoef s.1 : ℚ) : ℂ)).comp (starRingEnd ℂ).toAddMonoidHom)

theorem pctV_single (s : ValidState) (c : ℂ) :
    pctV (Finsupp.single s c) =
      Finsupp.single (pctValid s) (starRingEnd ℂ c * ((pctCoef s.1 : ℚ) : ℂ)) := by
  rw [pctV, Finsupp.liftAddHom_apply_single]
  rfl

theorem pctV_smul (z : ℂ) (f : V) : pctV (z • f) = starRingEnd ℂ z • pctV f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, smul_add]
  | single s c =>
    rw [Finsupp.smul_single, pctV_single, pctV_single, Finsupp.smul_single, smul_eq_mul,
      smul_eq_mul, map_mul, mul_assoc]

theorem conj_sC : starRingEnd ℂ sC = sC := by
  rw [sC, Complex.conj_ofReal]

theorem conj_tC : starRingEnd ℂ tC = -tC := by
  rw [tC, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-! ## Links with the computable map -/

theorem toFock_sortVec (v : Vec) : toFock (sortVec v) = toFock v := by
  rw [sortVec, toFock_mergeAll, List.map_map]
  induction v with
  | nil => simp
  | cons p v ih => simp [ih, toFock_cons]

theorem toV_sortVec (v : Vec) : toV (sortVec v) = toV v := by
  unfold toV
  rw [toFock_sortVec]

theorem toV4_sort4 (x : Vec4) : toV4 (sort4 x) = toV4 x := by
  simp only [toV4, sort4, toV_sortVec]

theorem pctV_toV : ∀ v : Vec, (∀ p ∈ v, Valid p.1) → pctV (toV v) = toV (pctVec v)
  | [], _ => by simp [pctVec]
  | (s, c) :: v, hv => by
    have hs : Valid s := hv (s, c) List.mem_cons_self
    have hs' : Valid (pctState s) := hs
    have ih := pctV_toV v fun q hq => hv q (List.mem_cons_of_mem _ hq)
    rw [toV_cons_mk, map_add, ih, canon_of_valid hs, pctV_single]
    simp only [pctVec, List.map_cons]
    rw [toV_cons_mk, canon_of_valid hs', map_ratCast, Rat.cast_mul, mul_comm]
    rfl

theorem pctV_toV4 (x : Vec4) (hx : x.AllStates Valid) : pctV (toV4 x) = toV4 (pct4 x) := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  simp only [toV4, pct4, map_add]
  rw [pctV_smul, pctV_smul, pctV_smul, map_mul, conj_sC, conj_tC, pctV_toV _ h0, pctV_toV _ h1,
    pctV_toV _ h2, pctV_toV _ h3, toV_smul, toV_smul]
  push_cast
  module

/-! ## `θ_g` is an involution -/

theorem zp_neg_mul (c : ℚ) (hc : c ≠ 0) : ∀ n : ℤ, zp c (-n) * zp c n = 1
  | .ofNat 0 => by simp [zp]
  | .ofNat (m + 1) => by
    show (c ^ (m + 1))⁻¹ * c ^ (m + 1) = 1
    exact inv_mul_cancel₀ (pow_ne_zero _ hc)
  | .negSucc m => by
    show c ^ (m + 1) * (c ^ (m + 1))⁻¹ = 1
    exact mul_inv_cancel₀ (pow_ne_zero _ hc)

theorem pctGauge_neg_mul (a : Mom) : pctGauge (Mom.neg a) * pctGauge a = 1 := by
  simp only [pctGauge, Mom.neg]
  calc _ = (zp 5 (-a.x0) * zp 5 a.x0) * (zp 8 (-a.x1) * zp 8 a.x1) * (zp 9 (-a.x2) * zp 9 a.x2) *
        (zp 8 (-a.x3) * zp 8 a.x3) * (zp 5 (-a.x4) * zp 5 a.x4) * (zp 1 (-a.x5) * zp 1 a.x5) *
        (zp 2 (-a.x6) * zp 2 a.x6) * (zp 2 (-a.x7) * zp 2 a.x7) := by ring
    _ = 1 := by
      rw [zp_neg_mul 5 (by norm_num), zp_neg_mul 8 (by norm_num), zp_neg_mul 9 (by norm_num),
        zp_neg_mul 8 (by norm_num), zp_neg_mul 5 (by norm_num), zp_neg_mul 1 (by norm_num),
        zp_neg_mul 2 (by norm_num), zp_neg_mul 2 (by norm_num)]
      norm_num

theorem pctCoef_pctState_mul (s : State) : pctCoef (pctState s) * pctCoef s = 1 := by
  have hg := pctGauge_neg_mul s.1
  have hs : pctSign s.2 * pctSign s.2 = 1 := by
    unfold pctSign
    split_ifs <;> norm_num
  simp only [pctCoef, pctState]
  calc _ = (pctSign s.2 * pctSign s.2) * (pctGauge (Mom.neg s.1) * pctGauge s.1) := by ring
    _ = 1 := by rw [hs, hg, one_mul]

theorem pctState_pctState (s : State) : pctState (pctState s) = s := by
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7⟩, osc⟩ := s
  simp [pctState, Mom.neg]

/-- **`θ_g` squares to the identity** (manuscript, after `eq:pct`). -/
theorem pctV_pctV (f : V) : pctV (pctV f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single s c =>
    have hidx : pctValid (pctValid s) = s := Subtype.ext (pctState_pctState s.1)
    have hw : ((pctCoef s.1 : ℚ) : ℂ) * ((pctCoef (pctValid s).1 : ℚ) : ℂ) = 1 := by
      rw [← Rat.cast_mul, mul_comm]
      exact_mod_cast pctCoef_pctState_mul s.1
    rw [pctV_single, pctV_single, hidx, map_mul, map_ratCast, starRingEnd_self_apply, mul_assoc,
      hw, mul_one]

/-- The vacuum and `ω` are `θ_g`-fixed: `θ_g` acts on states of momentum `0` with an even
number of oscillators trivially. -/
example : pctVec [((Mom.zero, [0, 1]), 2 / 3)] = [((Mom.zero, [0, 1]), 2 / 3)] := by
  decide +kernel

#print axioms pctV_toV4
#print axioms pctV_pctV

end LatticeVOA
end HaagerupIzumi.C8
