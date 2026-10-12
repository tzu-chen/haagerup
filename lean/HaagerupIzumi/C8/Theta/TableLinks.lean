module

public import HaagerupIzumi.C8.Theta.M3ReverseCancellation
public import HaagerupIzumi.C8.Theta.M6FirstCancellation

@[expose] public section

/-!
# Links between the even-block coefficients and the integer-label table functions

W6 (`Theta/W6_PLAN.md`), final step for the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  The capstones `m*_hcancel_of_voa` express the
VOA coefficients on the even blocks (orbit representatives `ιE e`); the obstruction theorems of
`Theta/M3First` … `M6Reverse` use the integer-label table functions.  Here:

* combinatorial invariances of theta coefficients: translation by `ℤ⁴` (`thetaCoeff_cosetPt`)
  and `g ↦ -g` for even weights (`thetaCoeff_neg`), hence for `thetaCount` and for
  `minusSixD2Coeff (thetaCount G ·)`;
* an analytic congruence (`thetaCoeff_congr_of_latticeThetaQ`: equal theta series and congruent
  energies give equal coefficients), used for the isometry `r ↦ -r` of `L₇ ⊕ A₂`;
* for each lattice, the reduction of an integer label to its orbit representative
  (`orbit_link_L7A2`, `orbit_link_A1A1A2`, `sepEven_link_G7m`, `avgNeg_link_G6m`), and the
  resulting links
  - `thetaCoeff_L7A2_link`: `[q^x] Θ_{H,(r,s)} = [q^x] Θ_{H, ιE(π(r mod 7, s mod 3))}`;
  - `PThetaA1A1A2_link`;
  - `PFG7m_link`, `PThetaG7m_link`: the separately even projection of Table 2 equals the
    `O(D)` average `FcEG7m`, `HcEG7m` at the label `9r + 7s`;
  - `PFG6m_link`, `PThetaG6m_link`: the `±` projection of Table 4 at any coset `g + L`,
    `g ∈ cosetG6m p + ℤ⁴`.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Combinatorial invariances -/

theorem cosetPt_cosetPt (g : Fin 4 → ℚ) (n m : Fin 4 → ℤ) :
    cosetPt (cosetPt g n) m = cosetPt g (n + m) := by
  funext i
  simp only [cosetPt, Pi.add_apply, Int.cast_add]
  ring

/-- **Translation invariance**: `[q^e] Θ_{H, g+n+L} = [q^e] Θ_{H, g+L}` for `n ∈ ℤ⁴`. -/
theorem thetaCoeff_cosetPt (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (n : Fin 4 → ℤ)
    (H : (Fin 4 → ℚ) → ℚ) (e : ℚ) : thetaCoeff Gz (cosetPt g n) H e = thetaCoeff Gz g H e := by
  unfold thetaCoeff
  refine finsum_mem_eq_of_bijOn (fun m => n + m) ⟨?_, ?_, ?_⟩ ?_
  · intro m hm
    show energy Gz (cosetPt g (n + m)) = e
    rw [← cosetPt_cosetPt]
    exact hm
  · intro m _ m' _ h
    exact add_left_cancel h
  · intro m hm
    refine ⟨-n + m, ?_, ?_⟩
    · show energy Gz (cosetPt (cosetPt g n) (-n + m)) = e
      rw [cosetPt_cosetPt, add_neg_cancel_left]
      exact hm
    · show n + (-n + m) = m
      rw [add_neg_cancel_left]
  · intro m _
    show H (cosetPt (cosetPt g n) m) = H (cosetPt g (n + m))
    rw [cosetPt_cosetPt]

theorem neg_cosetPt (g : Fin 4 → ℚ) (m : Fin 4 → ℤ) : cosetPt (-g) m = -cosetPt g (-m) := by
  funext i
  simp only [cosetPt, Pi.neg_apply, Int.cast_neg]
  ring

theorem energy_neg (Gz : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℚ) :
    energy Gz (-x) = energy Gz x := by
  simp only [energy, gramNorm, gramBil, Pi.neg_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Negation**: `[q^e] Θ_{H, -g+L} = [q^e] Θ_{H, g+L}` for even `H`. -/
theorem thetaCoeff_neg (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (H : (Fin 4 → ℚ) → ℚ)
    (hH : ∀ v, H (-v) = H v) (e : ℚ) : thetaCoeff Gz (-g) H e = thetaCoeff Gz g H e := by
  unfold thetaCoeff
  refine finsum_mem_eq_of_bijOn (fun m => -m) ⟨?_, ?_, ?_⟩ ?_
  · intro m hm
    show energy Gz (cosetPt g (-m)) = e
    have hm' : energy Gz (cosetPt (-g) m) = e := hm
    rwa [neg_cosetPt, energy_neg] at hm'
  · intro m _ m' _ h
    exact neg_inj.1 h
  · intro m hm
    refine ⟨-m, ?_, neg_neg m⟩
    show energy Gz (cosetPt (-g) (-m)) = e
    rw [neg_cosetPt, energy_neg, neg_neg]
    exact hm
  · intro m _
    show H (cosetPt (-g) m) = H (cosetPt g (-m))
    rw [neg_cosetPt, hH]

theorem quadOf_neg (M : Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → ℚ) :
    quadOf M (-x) = quadOf M x := by
  simp only [quadOf, Pi.neg_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem thetaCount_cosetPt (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (n : Fin 4 → ℤ) :
    thetaCount Gz (cosetPt g n) = thetaCount Gz g :=
  funext fun e => thetaCoeff_cosetPt Gz g n _ e

theorem thetaCount_neg (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) :
    thetaCount Gz (-g) = thetaCount Gz g :=
  funext fun e => thetaCoeff_neg Gz g _ (fun _ => rfl) e

theorem minusSix_cosetPt (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (n : Fin 4 → ℤ)
    (x : ℚ) : minusSixD2Coeff (thetaCount Gz (cosetPt g n)) x =
      minusSixD2Coeff (thetaCount Gz g) x := by
  rw [thetaCount_cosetPt]

theorem minusSix_neg (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) (x : ℚ) :
    minusSixD2Coeff (thetaCount Gz (-g)) x = minusSixD2Coeff (thetaCount Gz g) x := by
  rw [thetaCount_neg]

/-- A real translation by an integral vector is a `cosetPt`. -/
theorem eq_cosetPt_of_ratVec {g g' : Fin 4 → ℚ} {n : Fin 4 → ℤ}
    (h : ratVec g = ratVec g' + intVec n) : g = cosetPt g' n := by
  funext i
  have hi := congrFun h i
  simp only [ratVec, intVec, Pi.add_apply] at hi
  simp only [cosetPt]
  have h2 : ((g i : ℚ) : ℝ) = ((g' i + (n i : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact hi
  exact Rat.cast_injective h2

/-! ## An analytic congruence -/

/-- Equal weighted theta series and congruent energies give equal coefficients. -/
theorem thetaCoeff_congr_of_latticeThetaQ {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    (hG : (gramR Gz).PosDef) (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m)))
    {g g' : Fin 4 → ℚ} {s s' : Fin 4 → ℤ} (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s)
    (hg' : ratVec g' = (gramR Gz)⁻¹ *ᵥ intVec s')
    (hfr : Int.fract (energy Gz g) = Int.fract (energy Gz g')) (M : Matrix (Fin 4) (Fin 4) ℚ)
    (hθ : ∀ τ : ℂ, 0 < τ.im →
      latticeThetaQ (gramR Gz) (M.map (Rat.cast : ℚ → ℝ)) (ratVec g) τ =
        latticeThetaQ (gramR Gz) (M.map (Rat.cast : ℚ → ℝ)) (ratVec g') τ) (x : ℚ) :
    thetaCoeff Gz g (quadOf M) x = thetaCoeff Gz g' (quadOf M) x := by
  have key := qcoeff_eq_lincomb (Int.fract (energy Gz g)) (thetaCoeff Gz g (quadOf M))
    (thetaCoeff Gz g' (quadOf M)) (fun _ => 0) 1 0
    (fun y hy => thetaCoeff_support_fract hG hEven hg hy)
    (fun y hy => by rw [hfr]; exact thetaCoeff_support_fract hG hEven hg' hy)
    (fun y hy => absurd rfl hy)
    (fun y hy => summable_norm_thetaCoeff hG M _ hy)
    (fun y hy => summable_norm_thetaCoeff hG M _ hy) (fun _ _ => by simp)
    (fun τ => by
      rw [← latticeThetaQ_eq_tsum_thetaCoeff hG M g τ.im_pos,
        ← latticeThetaQ_eq_tsum_thetaCoeff hG M g' τ.im_pos, hθ τ τ.im_pos]
      simp) x
  rw [key]
  ring

/-! ## `L₇ ⊕ A₂` (Table 1) -/

theorem energy_cosetL7A2_neg_r (r s : ℤ) :
    energy gramL7A2 (cosetL7A2 (-r) s) = energy gramL7A2 (cosetL7A2 r s) := by
  have h0 : ∀ g : Fin 4 → ℚ, cosetPt g 0 = g := fun g => by
    funext i
    simp [cosetPt]
  have h1 := energy_cosetPt_L7A2 (-r) s 0
  have h2 := energy_cosetPt_L7A2 r s 0
  rw [h0] at h1 h2
  rw [h1, h2]
  push_cast [Pi.zero_apply]
  ring

/-- The isometry `r ↦ -r` on coefficients (weights invariant under `-1 ⊕ 1`). -/
theorem thetaCoeff_cosetL7A2_neg_r {M : Matrix (Fin 4) (Fin 4) ℚ}
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (r s : ℤ) (x : ℚ) :
    thetaCoeff gramL7A2 (cosetL7A2 (-r) s) (quadOf M) x =
      thetaCoeff gramL7A2 (cosetL7A2 r s) (quadOf M) x :=
  thetaCoeff_congr_of_latticeThetaQ posDef_L7A2 even_L7A2 (ratVec_cosetL7A2_eq_inv (-r) s)
    (ratVec_cosetL7A2_eq_inv r s) (by rw [energy_cosetL7A2_neg_r]) M
    (fun τ _ => thetaQ_cosetL7A2_neg_r hMiso r s τ) x

theorem cosetL7A2_neg (r s : ℤ) : cosetL7A2 (-r) (-s) = -cosetL7A2 r s := by
  funext i
  fin_cases i <;> simp [cosetL7A2] <;> ring

theorem cosetL7A2_mod (r s : ℤ) :
    cosetL7A2 r s = cosetPt (cosetL7A2 (((modL7A2 r s).1 : ℕ) : ℤ) (((modL7A2 r s).2 : ℕ) : ℤ))
      ![-(r / 7), 2 * (r / 7), 2 * (s / 3), s / 3] := by
  rw [(modL7A2_val r s).1, (modL7A2_val r s).2]
  exact eq_cosetPt_of_ratVec (ratVec_cosetL7A2_emod r s)

/-- Reduction of an integer label of `L₇ ⊕ A₂` to its orbit representative. -/
theorem orbit_link_L7A2 (Φ : (Fin 4 → ℚ) → ℚ) (htr : ∀ g n, Φ (cosetPt g n) = Φ g)
    (hneg : ∀ g, Φ (-g) = Φ g) (hflip : ∀ r s, Φ (cosetL7A2 (-r) s) = Φ (cosetL7A2 r s))
    (r s : ℤ) : Φ (cosetL7A2 r s) = Φ (cosetEL7A2 (πL7A2 (modL7A2 r s))) := by
  have hmod : ∀ r s : ℤ, Φ (cosetL7A2 r s) =
      Φ (cosetL7A2 (((modL7A2 r s).1 : ℕ) : ℤ) (((modL7A2 r s).2 : ℕ) : ℤ)) :=
    fun r s => by rw [cosetL7A2_mod r s, htr]
  rw [hmod r s]
  generalize modL7A2 r s = p
  show _ = Φ (cosetL7A2 (((ιL7A2 (πL7A2 p)).1 : ℕ) : ℤ) (((ιL7A2 (πL7A2 p)).2 : ℕ) : ℤ))
  rcases orbit_L7A2 p with h | h | h | h <;> rw [h]
  · rw [← modL7A2_negr p, ← hmod, hflip]
  · rw [← modL7A2_neg p, ← hmod, cosetL7A2_neg, hneg]
  · rw [← modL7A2_negs p, ← hmod]
    have hf := hflip (-((p.1 : ℕ) : ℤ)) (-((p.2 : ℕ) : ℤ))
    rw [neg_neg] at hf
    rw [hf, cosetL7A2_neg, hneg]

/-- **Link, Table 1**: the coefficient at the integer label `(r, s)` is the coefficient at the
even-block representative of `(r mod 7, s mod 3)`. -/
theorem thetaCoeff_L7A2_link {M : Matrix (Fin 4) (Fin 4) ℚ}
    (hMiso : (isoL7A2.map (Int.cast : ℤ → ℚ))ᵀ * M * isoL7A2.map (Int.cast : ℤ → ℚ) = M)
    (r s : ℤ) (x : ℚ) :
    thetaCoeff gramL7A2 (cosetL7A2 r s) (quadOf M) x =
      thetaCoeff gramL7A2 (cosetEL7A2 (πL7A2 (modL7A2 r s))) (quadOf M) x :=
  orbit_link_L7A2 (fun g => thetaCoeff gramL7A2 g (quadOf M) x)
    (fun g n => thetaCoeff_cosetPt _ g n _ x) (fun g => thetaCoeff_neg _ g _ (quadOf_neg M) x)
    (fun r s => thetaCoeff_cosetL7A2_neg_r hMiso r s x) r s

/-! ## `A₁ ⊕ A₁ ⊕ A₂` (Table 3) -/

theorem cosetA1A1A2_mod (a b s : ℤ) :
    cosetA1A1A2 a b s = cosetPt (cosetA1A1A2 (((modA1A1A2 a b s).1 : ℕ) : ℤ)
      (((modA1A1A2 a b s).2.1 : ℕ) : ℤ) (((modA1A1A2 a b s).2.2 : ℕ) : ℤ))
      ![a / 2, b / 2, 2 * (s / 3), s / 3] := by
  obtain ⟨ha, hb, hs⟩ := modA1A1A2_val a b s
  rw [ha, hb, hs]
  exact eq_cosetPt_of_ratVec (ratVec_cosetA1A1A2_emod a b s)

theorem orbit_link_A1A1A2 (Φ : (Fin 4 → ℚ) → ℚ) (htr : ∀ g n, Φ (cosetPt g n) = Φ g)
    (hswap : ∀ a b s, Φ (cosetA1A1A2 b a s) = Φ (cosetA1A1A2 a b s))
    (hconj : ∀ a b s, Φ (cosetA1A1A2 a b (-s)) = Φ (cosetA1A1A2 a b s)) (a b s : ℤ) :
    Φ (cosetA1A1A2 a b s) = Φ (cosetEA1A1A2 (πA1A1A2 (modA1A1A2 a b s))) := by
  have hmod : ∀ a b s : ℤ, Φ (cosetA1A1A2 a b s) =
      Φ (cosetA1A1A2 (((modA1A1A2 a b s).1 : ℕ) : ℤ) (((modA1A1A2 a b s).2.1 : ℕ) : ℤ)
        (((modA1A1A2 a b s).2.2 : ℕ) : ℤ)) :=
    fun a b s => by rw [cosetA1A1A2_mod a b s, htr]
  rw [hmod a b s]
  generalize modA1A1A2 a b s = p
  show _ = Φ (cosetA1A1A2 (((ιA1A1A2 (πA1A1A2 p)).1 : ℕ) : ℤ)
    (((ιA1A1A2 (πA1A1A2 p)).2.1 : ℕ) : ℤ) (((ιA1A1A2 (πA1A1A2 p)).2.2 : ℕ) : ℤ))
  rcases orbit_A1A1A2 p with h | h | h | h <;> rw [h]
  · rw [← modA1A1A2_swap p, ← hmod, hswap]
  · rw [← modA1A1A2_conj p, ← hmod, hconj]
  · rw [← modA1A1A2_swapconj p, ← hmod, hconj, hswap]

/-- **Link, Table 3**: the projected coefficient at the integer label `(a, b, s)`. -/
theorem PThetaA1A1A2_link (a b s : ℤ) (x : ℚ) :
    PThetaA1A1A2 a b s x =
      thetaCoeff gramA1A1A2 (cosetEA1A1A2 (πA1A1A2 (modA1A1A2 a b s))) (quadOf MHA1A1A2) x := by
  rw [PThetaA1A1A2_eq, HA1A1A2_eq_quadOf]
  exact orbit_link_A1A1A2 (fun g => thetaCoeff gramA1A1A2 g (quadOf MHA1A1A2) x)
    (fun g n => thetaCoeff_cosetPt _ g n _ x)
    (fun a b s => by
      have h := thetaCoeff_cosetA1A1A2_swap a b s x
      rw [HA1A1A2_eq_quadOf] at h
      exact h)
    (fun a b s => by
      have h := thetaCoeff_cosetA1A1A2_conj a b s x
      rw [HA1A1A2_eq_quadOf] at h
      exact h) a b s

/-! ## `G₇⁻` (Table 2) -/

theorem repG7m_neg (t : ℤ) : repG7m (-t) = -repG7m t := by
  funext i
  simp [repG7m]

theorem repG7m_mod (t : ℤ) :
    repG7m t = cosetPt (repG7m (((modG7m t : Fin 21) : ℕ) : ℤ))
      ![16 * (t / 21), 11 * (t / 21), 6 * (t / 21), t / 21] := by
  rw [modG7m_val]
  exact eq_cosetPt_of_ratVec (ratVec_repG7m_emod t)

theorem modG7m_congr {t t' : ℤ} (h : t % 21 = t' % 21) : modG7m t = modG7m t' := by
  apply Fin.ext
  have h1 := modG7m_val t
  have h2 := modG7m_val t'
  omega

theorem oG7m_modG7m (t : ℤ) : oG7m (modG7m t) = modG7m (13 * t) := by
  apply Fin.ext
  have h1 := modG7m_val t
  have h2 := modG7m_val (13 * t)
  show ((13 : Fin 21) * modG7m t).val = _
  rw [Fin.val_mul]
  have h13 : ((13 : Fin 21) : ℕ) = 13 := rfl
  rw [h13]
  omega

/-- The separately even projection of Table 2 at `(r, s)` is the `O(D)` average at the even-block
representative of `9r + 7s mod 21`, for any translation-invariant even functional `Φ`. -/
theorem sepEven_link_G7m (Φ : (Fin 4 → ℚ) → ℚ) (htr : ∀ g n, Φ (cosetPt g n) = Φ g)
    (hneg : ∀ g, Φ (-g) = Φ g) (r s : ℤ) :
    sepEven (fun r s => Φ (cosetG7m r s)) r s =
      (Φ (repG7m (((ιG7m (πG7m (modG7m (9 * r + 7 * s))) : Fin 21) : ℕ) : ℤ)) +
        Φ (repG7m (((oG7m (ιG7m (πG7m (modG7m (9 * r + 7 * s)))) : Fin 21) : ℕ) : ℤ))) / 2 := by
  have hF : ∀ t : ℤ, Φ (repG7m t) = Φ (repG7m (((modG7m t : Fin 21) : ℕ) : ℤ)) := fun t => by
    rw [repG7m_mod t, htr]
  have hFneg : ∀ t : ℤ, Φ (repG7m (-t)) = Φ (repG7m t) := fun t => by
    rw [repG7m_neg, hneg]
  have hG : ∀ k : Fin 21, Φ (repG7m (((-k : Fin 21) : ℕ) : ℤ)) = Φ (repG7m ((k : ℕ) : ℤ)) :=
    fun k => by rw [← modG7m_neg k, ← hF, hFneg]
  have hGo : ∀ k : Fin 21, Φ (repG7m (((oG7m (-k) : Fin 21) : ℕ) : ℤ)) =
      Φ (repG7m (((oG7m k : Fin 21) : ℕ) : ℤ)) := fun k => by
    rw [oG7m_neg, hG]
  have h1 : Φ (cosetG7m r s) = Φ (repG7m (((modG7m (9 * r + 7 * s) : Fin 21) : ℕ) : ℤ)) := by
    rw [cosetG7m_eq, hF]
  have h2 : Φ (cosetG7m (-r) (-s)) =
      Φ (repG7m (((modG7m (9 * r + 7 * s) : Fin 21) : ℕ) : ℤ)) := by
    rw [cosetG7m_eq, show 9 * -r + 7 * -s = -(9 * r + 7 * s) by ring, hFneg, hF]
  have h3 : Φ (cosetG7m (-r) s) =
      Φ (repG7m (((oG7m (modG7m (9 * r + 7 * s)) : Fin 21) : ℕ) : ℤ)) := by
    rw [cosetG7m_eq, hF, oG7m_modG7m,
      modG7m_congr (t := 9 * -r + 7 * s) (t' := 13 * (9 * r + 7 * s)) (by omega)]
  have h4 : Φ (cosetG7m r (-s)) =
      Φ (repG7m (((oG7m (modG7m (9 * r + 7 * s)) : Fin 21) : ℕ) : ℤ)) := by
    rw [cosetG7m_eq, show 9 * r + 7 * -s = -(9 * -r + 7 * s) by ring, hFneg, ← cosetG7m_eq, h3]
  have horb : ∀ k : Fin 21,
      Φ (repG7m (((ιG7m (πG7m k) : Fin 21) : ℕ) : ℤ)) +
        Φ (repG7m (((oG7m (ιG7m (πG7m k)) : Fin 21) : ℕ) : ℤ)) =
      Φ (repG7m ((k : ℕ) : ℤ)) + Φ (repG7m (((oG7m k : Fin 21) : ℕ) : ℤ)) := by
    intro k
    rcases orbit_G7m k with h | h | h | h <;> rw [h]
    · rw [hG, hGo]
    · rw [oG7m_data.1 k]
      ring
    · rw [hG, oG7m_neg, oG7m_data.1 k, hG]
      ring
  simp only [sepEven]
  rw [h1, h2, h3, h4, horb]
  ring

/-- **Link, Table 2, `F`**. -/
theorem PFG7m_link (r s : ℤ) (x : ℚ) :
    PFG7m r s x = FcEG7m (πG7m (modG7m (9 * r + 7 * s))) x := by
  rw [PFG7m]
  exact sepEven_link_G7m (fun g => minusSixD2Coeff (thetaCount gramG7m g) x)
    (fun g n => minusSix_cosetPt gramG7m g n x) (fun g => minusSix_neg gramG7m g x) r s

/-- **Link, Table 2, `Θ_H`**. -/
theorem PThetaG7m_link (r s : ℤ) (x : ℚ) :
    PThetaG7m r s x = HcEG7m (πG7m (modG7m (9 * r + 7 * s))) x := by
  have hH : HG7m = quadOf MHG7m := funext HG7m_eq_quad
  rw [PThetaG7m, hH]
  exact sepEven_link_G7m (fun g => thetaCoeff gramG7m g (quadOf MHG7m) x)
    (fun g n => thetaCoeff_cosetPt _ g n _ x)
    (fun g => thetaCoeff_neg _ g _ (quadOf_neg MHG7m) x) r s

/-! ## `G₆⁻` (Table 4) -/

theorem cosetG6m_neg (a b t : ℤ) : cosetG6m (-a) (-b) (-t) = -cosetG6m a b t := by
  funext i
  fin_cases i <;> simp [cosetG6m] <;> ring

theorem cosetG6m_mod (a b t : ℤ) :
    cosetG6m a b t = cosetPt (cosetG6m (((modG6m a b t).1 : ℕ) : ℤ)
      (((modG6m a b t).2.1 : ℕ) : ℤ) (((modG6m a b t).2.2 : ℕ) : ℤ))
      ![2 * (t / 3), a / 2 + t / 3, b / 2 + t / 3, a / 2 + b / 2 - t / 3] := by
  obtain ⟨ha, hb, ht⟩ := modG6m_val a b t
  rw [ha, hb, ht]
  exact eq_cosetPt_of_ratVec (ratVec_cosetG6m_emod a b t)

/-- The `±` projection of Table 4 at a coset `cosetG6m p + n` is the value at the even-block
representative of `p`. -/
theorem avgNeg_link_G6m (Φ : (Fin 4 → ℚ) → ℚ) (htr : ∀ g n, Φ (cosetPt g n) = Φ g)
    (hneg : ∀ g, Φ (-g) = Φ g) (p : Fin 2 × Fin 2 × Fin 3) (n : Fin 4 → ℤ) :
    avgNeg Φ (cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n) =
      Φ (cosetEG6m (πG6m p)) := by
  have hmod : ∀ a b t : ℤ, Φ (cosetG6m a b t) =
      Φ (cosetG6m (((modG6m a b t).1 : ℕ) : ℤ) (((modG6m a b t).2.1 : ℕ) : ℤ)
        (((modG6m a b t).2.2 : ℕ) : ℤ)) :=
    fun a b t => by rw [cosetG6m_mod a b t, htr]
  rw [avgNeg, hneg, htr, add_self_div_two]
  show _ = Φ (cosetG6m (((ιG6m (πG6m p)).1 : ℕ) : ℤ) (((ιG6m (πG6m p)).2.1 : ℕ) : ℤ)
    (((ιG6m (πG6m p)).2.2 : ℕ) : ℤ))
  rcases orbit_G6m p with h | h <;> rw [h]
  rw [← modG6m_neg p, ← hmod, cosetG6m_neg, hneg]

/-- **Link, Table 4, `F`**. -/
theorem PFG6m_link {g : Fin 4 → ℚ} {p : Fin 2 × Fin 2 × Fin 3} {n : Fin 4 → ℤ}
    (hg : g = cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n)
    (x : ℚ) : PFG6m g x = minusSixD2Coeff (thetaCount gramG6m (cosetEG6m (πG6m p))) x := by
  rw [PFG6m, hg]
  exact avgNeg_link_G6m (fun g => minusSixD2Coeff (thetaCount gramG6m g) x)
    (fun g n => minusSix_cosetPt gramG6m g n x) (fun g => minusSix_neg gramG6m g x) p n

/-- **Link, Table 4, `Θ_H`**. -/
theorem PThetaG6m_link {g : Fin 4 → ℚ} {p : Fin 2 × Fin 2 × Fin 3} {n : Fin 4 → ℤ}
    (hg : g = cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n)
    (x : ℚ) : PThetaG6m g x = thetaCoeff gramG6m (cosetEG6m (πG6m p)) (quadOf MHG6m) x := by
  have hH : HG6m = quadOf MHG6m := funext HG6m_eq_quad
  rw [PThetaG6m, hg, hH]
  exact avgNeg_link_G6m (fun g => thetaCoeff gramG6m g (quadOf MHG6m) x)
    (fun g n => thetaCoeff_cosetPt _ g n _ x)
    (fun g => thetaCoeff_neg _ g _ (quadOf_neg MHG6m) x) p n

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_cosetPt
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_neg
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_congr_of_latticeThetaQ
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_L7A2_link
#print axioms HaagerupIzumi.C8.Theta.PThetaA1A1A2_link
#print axioms HaagerupIzumi.C8.Theta.PFG7m_link
#print axioms HaagerupIzumi.C8.Theta.PThetaG7m_link
#print axioms HaagerupIzumi.C8.Theta.PFG6m_link
#print axioms HaagerupIzumi.C8.Theta.PThetaG6m_link
