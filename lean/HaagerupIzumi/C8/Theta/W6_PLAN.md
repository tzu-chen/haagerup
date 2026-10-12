# W6 plan: the theta identities `hcancel` (phase 2, 1 October 2026; updated 4 October 2026)

W6 replaces the hypotheses `hcancel` of `Theta/M3First`, `M3Reverse`, `M6First` and
`M6Reverse` by theorems.  These files cover the proof of `prop:near-group-current-obstructions`,
manuscript lines 3614–3770.

* `hcancel` says, coefficientwise, `η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}`, or `φ F + κ Θ_H` for the
  reverse orientations.
* It is the output of `lem:pole-cancellation`, which is fully proved in
  `Analytic/PoleCancellation.lean` (`pole_cancellation`).

## 1. Compiled files (in the source tree, all `c8q build` exit 0, axioms only `propext`, `Classical.choice`, `Quot.sound`)

### `PoissonPi.lean`: multi-dimensional Poisson summation (not in Mathlib)

`tsum_eq_tsum_fourierPi`: `∑_m f(x+m) = ∑_k 𝓕f(k) e(k·x)`.  Assumptions on `f`:

* the translates have locally summable sup norms (`TranslatesSummable`);
* `𝓕f(k)`, `k ∈ ℤ^d`, is summable.

The proof periodizes, descends to the torus, and uses Mathlib's convergence of absolutely
summable `UnitAddTorus` Fourier series.

### `PoissonGaussian.lean`: Gaussians of a positive definite form

* `fourierPi_gaussCM`, the Fourier transform of a Gaussian.
* `tsum_exp_qf_poisson`: `∑_m e^{-πaQ_G(x+m)} = (det G)^{-1/2} a^{-d/2} ∑_k e^{-πa⁻¹Q_{G⁻¹}(k)} e(k·x)`.

### `LatticeTheta.lean`: theta series of weight `d/2`

`latticeTheta G γ τ = ∑_m exp(πiτ Q_G(γ+m))`.

* `latticeTheta_S_poisson` and `latticeTheta_S`: the latter is the coset form for an integral
  `Gz`, a residue system `R` (hypothesis `hR`) and `γ = G⁻¹s ∈ L'`.
* `cexp_qf_add_one`: the termwise `T`-law.  It was moved here in phase 2, and both `T`-laws are
  now derived from it.
* `latticeTheta_T`, `latticeTheta_add_intVec`, `latticeTheta_neg`.

The module docstring now states the representation convention (audit item 1):

* `T ↦ e(q(γ))` is Borcherds' `ρ_L`.
* The printed matrix `c·e(+(γ,δ))` equals `ρ_L(S)·C`, with `C : γ ↦ -γ`.
  - It agrees with `ρ_L(S)` on `C`-even vectors, which is enough for `Θ_L` and the even blocks.
  - Together with `T` it is **not** a representation on all of `ℂ[L'/L]`: for `ℤ/21`,
    `(S'T)³ = 1 ≠ S'² = C`.
* For vector covariance, use the `e(-(γ,δ))` form, obtained by replacing `R` with `-R`.
* The docstring also records the bridge between the vector variables `s`, `r` of the theorem and
  the coset labels of the tables:
  - `G⁻¹![0,r,s,0] = cosetL7A2 r s`;
  - `G⁻¹((9r+7s)e₀) = cosetG7m r s`.

### `LatticeThetaHarmonic.lean`: harmonic quadratic weights, weight `d/2 + 2`

* Hecke's identity for quadratic weights: `fourierPi_qgaussCM`.
* `tsum_qf_exp_qf_poisson`.
* `latticeThetaQ` with:
  - `latticeThetaQ_S_poisson` and `latticeThetaQ_S`, which carry the extra factor `τ²`;
  - `latticeThetaQ_T`, derived from `cexp_qf_add_one`;
  - phase 2 added `latticeThetaQ_add_intVec` and `latticeThetaQ_neg`.
* The citation was corrected from line 3654 to line 3656.

### `LatticeThetaHolomorphic.lean`

* Holomorphy on `{Im τ > 0}`.
* `MDiff` on `ℍ` for `latticeTheta` and `latticeThetaQ`.

### `LatticeThetaModular.lean`

* `covariant_of_S_T`.
* `coe_S_smul` and `coe_T_smul`.

The docstring now says (audit item 3):

* the lemma closes the gap only **given** a homomorphism `σ` whose values at `S` and `T` are the
  theta matrices, taken in the `e(-(γ,δ))` form;
* `σ` comes from the VOA side (item 4 below).

## 2. The phase-2 drafts: compiled on 4 October 2026 (phase 0)

**Status 2026-10-04 (phase 0 done):** `LatticeData`, `Eta8`, `QExpansion` were moved back from
`lean/tools/w6_drafts/` into `Theta/`, checked and built (`c8q build` exit 0; axioms only
`propext`, `Classical.choice`, `Quot.sound`).  Registration in `C8All`/`C8Axioms` is done by the
root agent (not by W6); see the root's ledger for the current status.
Fixes needed: three docstrings placed before `omit … in` (moved after it); the four
`det_*` proofs (the `norm_num [det_succ_row_zero]` expansion did not close) were replaced by a
new general lemma `det_eq_of_smith`/`det_gramR_of_smith` (determinant from the Smith data,
`det U, det V = ±1`, sign from `PosDef.det_pos`); the `O(D)` sum reindexing in
`thetaQG7m_S_o`/`thetaG7m_S_o` now uses `Fintype.sum_equiv`; `Eta8`/`QExpansion` only had
linter warnings.  No statement was changed.

The original drafts remain in `lean/tools/w6_drafts/` (now superseded).

### `LatticeData.lean` (plan item 1)

General part:

* **Bridges to the ℚ data:**
  - `ratVec`;
  - `inv_gramR_eq` (`G·K = 1` over ℚ ⇒ `(gramR G)⁻¹ = K`);
  - `harmonic_of_pairTrace` (`Theta/Harmonic`'s `pairTrace` ⇒ the ℝ harmonicity hypothesis);
  - `det_gramR`.
* **Positive definiteness:** `posDef_gramR_of_coercive`, a sum-of-squares criterion.
* **Isometries:**
  - `latticeThetaQ_isometry` and `latticeTheta_isometry`: `Θ_{M,Uγ} = Θ_{M,γ}` for
    `U ∈ GL(ℤ^d)` with `UᵀGU = G` and `UᵀMU = M`;
  - the cast transfer lemmas `gramR_transpose_mul_mul` and `ratCast_transpose_mul_mul`.
* **Residue systems:**
  - `existsUnique_residue_of_smith`: `hR` from an explicit factorization `U G V = diag(d)` and
    labels mapped by `U` into the box;
  - `exists_mulVec_eq_of_dvd`.
* **Label forms of the `S`-laws:**
  - `latticeTheta(Q)_S_labels`;
  - `sum_eChar_neg_of_involutive`, which switches to Borcherds' `e(-(γ,δ))` form (audit item 1).

Per lattice:

* `L₇⊕A₂`: labels `(r,s) ∈ ℤ/7×ℤ/3 ↦ (0,r,s,0)`.
* `G₇⁻`: labels `j ∈ ℤ/21 ↦ (j,0,0,0)`, with `cosetG7m r s = repG7m (9r+7s)`.
* `A₁⊕A₁⊕A₂`: labels `(a,b,s) ↦ (a,b,s,0)`.
* `G₆⁻`: labels `(a,b,t) ↦ a(-1,1,0,2) + b(-1,0,1,2) + t(1,0,0,-2)`.  The vacuum is
  `cosetG6m_zero`, and the polar coset `-w/3` is the label `(1,1,1)`.

For each lattice the draft contains:

* `posDef_*`, `even_*`, `inv_*`, `det_*` (21, 21, 12, 12) and `hR_*`.
* The identification `rep_*` of `G⁻¹·label` with the manuscript cosets.
* Explicit `S` and `T` data:
  - `L₇⊕A₂`: `sL7A2 = 2rr'/7 + 2ss'/3`, `eL7A2 = r²/7 + s²/3`;
  - `G₇⁻`: `16jk/21` and `8j²/21`;
  - `A₁⊕A₁⊕A₂`: `aa'/2 + bb'/2 + 2ss'/3` and `a²/4 + b²/4 + s²/3`;
  - `G₆⁻`: the form `B = [[3/2,1,-1],[1,3/2,-1],[-1,-1,4/3]]`.
* The `S`-laws, with and without weight (the unweighted ones are used by `F = -6D₂Θ`):
  `Θ_{H,p}(-1/τ) = -τ⁴/√|D| ∑_q e(-s(p,q)) Θ_{H,q}(τ)`, and `-τ²/√|D|` without weight.
* The `T`-laws `Θ_p(τ+1) = e(e(p)) Θ_p(τ)`.
* The reduction of integer labels modulo `D`.

Symmetries of the projections in the tables (audit item 2):

* `L₇⊕A₂`, `r ↦ -r`: the isometry `-1⊕1` (`thetaQ_cosetL7A2_neg_r`).
* `A₁⊕A₁⊕A₂`: the swap and `s ↦ -s` are isometries (`thetaQ_cosetA1A1A2_swap`, `_conj`).
* `G₆⁻`, `b ↔ c`: an isometry (`thetaQ_cosetG6m_swap`).
* `G₇⁻`, `(r,s) ↦ (-r,s)` = `j ↦ 13j`: a discriminant-form isometry (`O(D)`), not a lattice
  isometry.
  - The `S`/`T` exponents are invariant modulo 1 by a finite check (`oG7m_data`).
  - `thetaQG7m_S_o` and `thetaQG7m_T_o` then show that `(Θ_{13j})_j` satisfies the same laws as
    `(Θ_j)_j`, so the `r`-even projection transforms by the same matrices.

The Smith data, labels and exponent formulas were computed with an exact-arithmetic script and
are re-verified in Lean by `decide`.

### `Eta8.lean` (plan item 3)

* `eta8_S`: `η⁸(-1/τ) = τ⁴η⁸(τ)`, from `eta_comp_eq_csqrt_I_inv` and `(√i)⁸ = 1`.
* `eta8_T`: `η⁸(τ+1) = e(1/3)η⁸(τ)`.
* `eta8_ne_zero` and `differentiableOn_eta8`.
* `eta8_eq`: `η⁸ = q^{1/3} P⁸` with `P = ∏(1-qⁿ)`.
* `norm_etaProd_sub_one_le`: `‖P-1‖ ≤ 6‖q‖` for `‖q‖ ≤ 1/2`.
* `norm_inv_eta8_sub_le`: `‖η⁸(τ)⁻¹ - q^{-1/3}‖ ≤ 228‖q‖‖q^{-1/3}‖` for `‖q‖ ≤ 1/48`.
* `norm_qParam_one_le_of_one_le_im`: `Im τ ≥ 1` ⇒ `‖q‖ ≤ 1/48`.

### `QExpansion.lean` (plan item 2)

* `shell_finite`.
* `latticeThetaQ_eq_tsum_thetaCoeff` and `latticeTheta_eq_tsum_thetaCount`:
  `Θ_{H,g}(τ) = ∑_{e∈ℚ} thetaCoeff G g H e · q^e`.  Here `H = quadOf M`, and `thetaCoeff` is the
  coefficient of `Theta/Basic`, so the tables' coefficients become the actual Fourier
  coefficients.
* `summable_norm_thetaCoeff`.
* `tsum_rat_eq_tsum_nat`, which reindexes exponents `λ+ℕ`.
* `qcoeff_eq_of_tsum_eq`: uniqueness of coefficients, via `ProofMap.qseries_coeff_eq_zero`
  (imports `ProofMapConcreteCharacters`).

## 3. What remains to make `hcancel` a theorem

Sizes are in six-hour sessions.

0. **Compile the three drafts** (section 2): about 0.5 session, depending on the error count.
   Still to add after that:
   * the support lemma "energies of `γ + L` lie in `q(γ) + ℕ`", from `cexp_qf_add_one`'s
     computation;
   * the evaluation of `thetaQ*` at the table labels via the `*_emod` lemmas.

   **Status 2026-10-04: done.**  Drafts compiled (section 2).  New file `ThetaSupport.lean`
   (built): `qf_add_intVec_eq`, `energy_cosetPt_eq_add_int`, `thetaCoeff_support`,
   `nonneg_of_thetaCoeff_ne_zero`, `thetaCoeff_support_nat(_complex)` (support on `λ + ℕ` for
   every `λ ≤ 0`, `λ ≡ q(γ)`); integer labels as `G⁻¹` of integral vectors
   (`ratVec_*_eq_inv`); reduction maps `modL7A2`, `modG7m`, `modA1A1A2`, `modG6m` with
   `latticeThetaQ_coset* = thetaQ* (mod …)` (also unweighted), the new
   `ratVec_cosetG6m_emod`, the Table 4 coordinates `0 ↦ (0,0,0)`, `polarG6m ↦ (1,1,1)`; and
   `thetaQ*_mod_eq_tsum`: the component of the theta vector at the reduced label has the
   table coefficients `thetaCoeff G (label) (quadOf M) e` as `q`-coefficients.
1. **Define `λ, μ` (`κ, φ`) from `A, B` (`P`)** as the manuscript does (audit item 4), before
   applying `pole_cancellation`.  Today they are free variables of the `*_obstruction`
   theorems.

   **Status 2026-10-04: done** in the new file `ObstructionCoefficients.lean` (built; the four
   table files are unchanged).  `lamM3First`, `muM3First`, `phiM3Reverse`, `kappaM3Reverse`,
   `kappaM6First`, `phiM6Reverse`, `kappaM6Reverse`; `*_polar_match` (the combination has the
   manuscript's polar/vacuum coefficients, including the `M3First`/`M6First` vacuum `q⁰`
   entries, which vanish by `thetaCoeff_at_zero`), `*_remainder_polar_zero`, `*_polar_unique`,
   and `*_obstruction_of_defined` (`hcancel` for the *defined* coefficients plus the vacuum
   coefficient gives `dim U₁`; the polar hypotheses become consequences).
2. **The representation `σ`** (about 1 session).
   * Take `σ` from the modularity of the character vector (Zhu), as in `CharacterUniqueness`.
     Finiteness of the image is **not** a separate VOA input here: `σ` is pinned at the
     generators (`σ(S) = SθE*`, `σ(T) = TθE*`), so finite image is a property of the explicit
     Weil-type matrices (manuscript lines 3772–3774); it remains the hypothesis `hfin`.
   * Identify Zhu's `S` with the categorical modular `S` via Huang's theorem (external).
   * State the manuscript's "multiplication by `η⁸` identifies it with the Weil representation"
     as `σ(S)` and `σ(T)` on the even block equal to `-1/√|D| · e(-(γ,δ))` times the
     `η⁸`-character, and `e(q(γ) - 1/3)`.  This is a finite check from the `G_{2,3}`/`A_{2,1}`
     modular data.
   * Then `covariant_of_S_T` gives covariance of `Θ_H/η⁸`.  The even projections use the
     symmetry lemmas of `LatticeData`.

   **Status 2026-10-04: finite/theta part done** (new files `WeilBlocks.lean`,
   `EvenBlocks.lean`, built).
   * Full vectors `F*_p = Θ_{H,p}/η⁸` with explicit `Sθ*` (`-1/√|D| e(-(γ,δ))`) and
     `Tθ*` (`diag e(q(γ) - 1/3)`): `F*_S`, `F*_T`; `F*_covariant` given a homomorphism `σ` with
     `σ S = Sθ*`, `σ T = Tθ*` (named hypotheses); `noInvariant_sigma_*` = the `hinv` input of
     `pole_cancellation` (kernel-checked `T`-fixed coordinates `tfixed_*`).
   * Even blocks in the manuscript's labels (`E = Fin 4 × Fin 2` for `L₇ ⊕ A₂` and `G₇⁻`,
     `Fin 3 × Fin 2` for `A₁ ⊕ A₁ ⊕ A₂`, `Fin 2 × Fin 2 × Fin 2` for `G₆⁻`), kernel-checked
     orbit maps, orbit-constancy of the theta vector (for `G₇⁻` of the `O(D)` average
     `FaG7m`), reduced matrices `SθE* = reduceMat …`, `TθE*`; `FE*_S`, `FE*_T`,
     `FE*_covariant` (given `σ_E S = SθE*`, `σ_E T = TθE*`), `noInvariantE_sigma_*`
     (`SθEL7A2_vac = -2/√21`, `SθEA1A1A2_vac = -2/√12` at the only `T`-fixed coordinate).
   * `EvenBlockData.lean` (built): `SθEL7A2_eq`, the even block of `L₇ ⊕ A₂` in the
     manuscript's printed cosine form, `-(1/√21) C₇(r,r') C₃(s,s')` with `C₇(r,0) = 1`,
     `C₇(r,r') = 2cos(4πrr'/7)`, `C₃(s,1) = 2cos(4πs/3)` (orbits kernel-checked), and
     `TθEL7A2_eq` (`e(r²/7 + s²/3 - 1/3)`).
   * **2026-10-04, later:** closed forms of all even `S`-blocks: `SθEG7m_eq`
     (`EvenBlockDataG7m.lean`; `SθEG7m = SθEL7A2`), `SθEA1A1A2_eq` and `SθEG6m_eq`
     (`EvenBlockDataSigns.lean`; `-(1/√12) C₂₂ ⊗ C₃` resp. `-(1/√12)(-1)^{aa'+bb'} C₃`),
     `SθE6G6m_eq` (`M6ReverseSym.lean`; `SθE6G6m = SθEA1A1A2`).
   * **2026-10-04, audit fix (G₆⁻ block):** the `G₆⁻` even block used by the capstone and the
     obstruction theorem is now the **6-dimensional** quotient by `-1` and the interchange
     `b ↔ c` (`M6ReverseSym.lean`: `SθE6G6m`, `TθE6G6m`, `FE6G6m`, `FFE6G6m`, index
     `Fin 3 × Fin 2` via `ιA1A1A2`/`πA1A1A2`), matching the manuscript's
     `(v₀, v_A, v_B) ⊗ (even pointed factor)` (lines 3714–3720, 3762–3766).  The 8-dimensional
     version (`EvenBlocks`, `M6ReverseCancellation`) is kept but superseded.
   * **2026-10-04, non-vacuity (audit item 2): done.**  `WeilSanity.lean`,
     `WeilSanityST.lean`, `WeilSanityST3.lean` (built) prove, for each of the four even blocks,
     `SθE² = 1`, `(SθE TθE)³ = 1 = SθE²` and `TθE^N = 1` (`N = 21`, `21`, `12`, `12`):
     `sl2_relations_L7A2`, `sl2_relations_G7m`, `sl2_relations_A1A1A2`, `sl2_relations_G6m`.
     So `S ↦ SθE`, `T ↦ TθE` satisfies the defining relations of `SL(2, ℤ)`
     (`S⁴ = 1`, `(ST)³ = S²`, `S²` central), and the hypothesized `σ` exists (with finite image,
     as the generators' images have finite order and the relations hold); Lean does not construct
     `σ` (Mathlib has no presentation of `SL(2, ℤ)`).  The signs are checked: the cube is `+1`
     because of the Gauss-sum signs `G₇ = ∑ ζ₇^{x²} = i√7` (`gauss7_eq`, via `G₇² = -7` and
     `Im G₇ > 0`), `1 + 2e(1/3) = i√3`, `e(1/4) = i`.
   * Still open (VOA side, stays a hypothesis): `σ_E` itself (Zhu modularity of the character
     vector, Huang's identification of Zhu's `S` with the categorical `S`) and the comparison of
     `SθE*`, `TθE*` with the categorical `G_{2,3}`/`A_{2,1}` (resp. the `m = 6`) modular data.
3. **Equal principal parts and pole cancellation** (1.5–2 sessions; audit item 4).
   * The **full** polar part must match.  For `M3First` this includes the vacuum `q⁰` term.
   * On the VOA side, the coefficients at all other polar exponents must vanish.  These are not
     among the current `hpolar*` and `hvac` hypotheses and must be added as stated VOA inputs:
     the `q`-expansions of `δv`, their polar data, and holomorphy of `δv`.
   * Analytic inputs:
     - tail bounds for the theta `q`-series, from `summable_norm_thetaCoeff`;
     - `|1/η⁸| ≤ C|q|^{-1/3}`, from `norm_inv_eta8_sub_le`.
   * For `F = -6D₂Θ` (`M3Reverse`, `M6Reverse`):
     - termwise `q`-derivative of the theta series;
     - the `S`-law of `D₂Θ` in slash form;
     - the `E₂` `q`-expansion behind `minusSixD2Coeff`.
   * Reusable: `CharacterUniqueness.isBoundedAtImInfty_qseries` and
     `character_vector_unique_of_qexp`.

   **Status 2026-10-04: done for all four tables** (theta side; VOA side as named hypotheses).
   * `PolarParts.lean` (built): `thetaCoeff_polar` (a nonzero coefficient below `c ≤ 1` sits at
     `frac q(γ)`), and the **complete** polar entries of each theta vector, kernel-checked
     (`polar_L7A2`: `(0,0)@0`, `(±1,0)@1/7`, `(±3,0)@2/7`; `polar_G7m`: `0@0`,
     `{4,10,11,17}@2/21`; `polar_A1A1A2`: `(0,0,0)@0`, `(1,0,0),(0,1,0)@1/4`; `polar_G6m`:
     `(0,0,0)@0`, `(1,1,±1)@1/6`).  Holomorphy `mdifferentiable_F*`, `mdifferentiable_FE*`.
   * `RemainderBound.lean` (built): `norm_inv_eta8_le` (`|1/η⁸| ≤ (1 + 228/48) e^{2πy/3}`,
     `y ≥ 1`), `isBoundedAtImInfty_tsum_div_eta8` (a `q`-series with no exponent `< 1/3`,
     divided by `η⁸`, is bounded at `i∞`), `tsum_sub_lincomb`, `summable_lincomb`.
   * `M3FirstCancellation.lean` (built): `m3_first_hcancel_of_voa` and
     **`m3_first_dimension_of_voa`**: `dim U₁ = 15 + A + 10B` with `hcancel` *derived* from
     `pole_cancellation`.  Remaining hypotheses (all VOA side, named): `σ` on the even block
     with finite image and `σ(S) = SθEL7A2`, `σ(T) = TθEL7A2`; the difference vector `V`
     (holomorphic, `σ`-covariant); its `η⁸` `q`-expansion `δc` with support on
     `lamOf … + ℕ` and absolute convergence; the polar data (`0`, `-B`, `7 - A` at the three
     polar entries, zero at all other entries below `1/3`); the vacuum coefficient.
   * `M6FirstCancellation.lean` (built): `m6_first_hcancel_of_voa`,
     **`m6_first_dimension_of_voa`** (`dim U₁ = 8 + A`), same shape.
   * **`F` orientations, done the same day (2026-10-04):**
     - `SerreTheta.lean`: Mathlib's Serre derivative (`Derivative.serreDerivative 2` is the
       manuscript's `D₂`); `serre_finset_sum`, `serre_S_of_slash`, `serre_T_of_slash`; the weight-two
       theta laws in slash form (`θG7m_slash_S/T`, `θG6m_slash_S/T`); `FFG7m`, `FFG6m`
       (`F = -6∂₂Θ/η⁸`) satisfy the **same** `Sθ`, `Tθ` laws as `Θ_H/η⁸` (`FF*_S/T/covariant`).
     - `SerreQExp.lean`: `deriv_latticeTheta` (termwise), `normDeriv_latticeTheta`
       (`DΘ = Θ_{G}/2`), `normDeriv_theta_qexp` (`DΘ = ∑ e N(e) q^e`), `minusSix_serre_eq`.
     - `E2Theta.lean`: `thetaCoeff_support_fract`, `summable_norm_thetaCount`, `hasSum_E2`
       (Mathlib's `E₂` expansion with `e2Coeff`), `E2_mul_theta_hasSum` (Cauchy product), and
       **`minusSixSerre_theta_qexp`: `-6∂₂Θ_{g+L} = ∑ minusSixD2Coeff (thetaCount G g) e · q^e`**,
       i.e. the Table 2/4 `F`-coefficients are the actual `q`-coefficients.
     - `E2ThetaSummable.lean`: `cauchy_term`, `summable_norm_e2ThetaCoeff`,
       `summable_norm_minusSixD2Coeff` (absolute convergence at every height).
     - `M6ReverseCancellation.lean`: `m6_reverse_dimension_of_voa` (`dim U₁ = 5 + 12P`) and
       `m6_reverse_hcancel_of_voa` on the 8-dimensional block; includes `thetaCoeff_polarG6m_eq`
       (the polar coset `-w/3` is the label `(1,1,1)`).  **Superseded** by `M6ReverseSym.lean`:
       **`m6_reverse_dimension_of_voa_sym`**, `m6_reverse_hcancel_of_voa_sym` on the
       6-dimensional swap-symmetric block (polar coordinate `(11, 1)`, vacuum `(00, 0)`).
     - `M3ReverseCancellation.lean`: **`m3_reverse_dimension_of_voa`** (`dim U₁ = 14 + 42A`) and
       `m3_reverse_hcancel_of_voa`, on the separately even block (average over `j ↦ 13j`,
       coordinates `(r,s) ↦ 9r + 7s`); includes the `O(D)`-twisted `F`-laws, the translates
       `thetaCount_repG7m_congr`/`thetaCoeff_repG7m_congr`, and the halving of the polar
       coefficient (`(3/7·1 + 3/7·0)/2 = 3/14`, `(-4/7 + 0)/2 = -2/7`).
   * **Net status of W6 (2026-10-04): all four `hcancel` hypotheses are now theorems relative to
     VOA-side inputs.**  In the integer-label form of the table files they are
     `m3_first_hcancel_table_of_voa`, `m3_reverse_hcancel_table_of_voa`,
     `m6_first_hcancel_table_of_voa`, `m6_reverse_hcancel_table_of_voa`
     (`ObstructionsOfVoa.lean`, through the link lemmas of `TableLinks.lean` and
     `M6ReverseSym.lean`), and the obstruction theorems **without `hcancel`** are
     `m3_first_obstruction_of_voa`, `m3_reverse_obstruction_of_voa`,
     `m6_first_obstruction_of_voa`, `m6_reverse_obstruction_of_voa` (each applies the existing
     `*_obstruction` theorem with `hcancel := *_hcancel_table_of_voa`).  The remaining
     hypotheses are exactly: `σ` on the even block with `σ(S) = SθE*`, `σ(T) = TθE*` (VOA side:
     Zhu modularity, Huang's identification of `S`, comparison with the categorical modular
     data) and finite image `hfin` (a property of the explicit matrices, since `σ` is pinned at
     the generators); the VOA vector `V` (holomorphic, covariant); its `η⁸` `q`-expansion `δc`
     (support on `lamOf … + ℕ`, absolute convergence); the polar/vacuum coefficients of `δc` and
     the vanishing of `δc` at all other entries below `q^{1/3}`.  Non-vacuity of the `σ`
     hypotheses: `sl2_relations_*` (item 2 status).
4. **Coefficient extraction** with `qcoeff_eq_of_tsum_eq`, to obtain `hcancel` in its current
   form: about 0.5 session.

   **Status 2026-10-04: done for the theta-only orientations** (new file
   `CoeffExtraction.lean`, built): `qcoeff_eq_lincomb`; `lamOf`;
   `hcancel_L7A2_of_eq` and `hcancel_A1A1A2_of_eq` (`hcancel` of `M3First`/`M6First` from the
   componentwise functional identity `η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}` resp. `κ Θ_H` on `ℍ`, with
   VOA-side support/summability of the `δv` coefficients as named hypotheses);
   `PThetaA1A1A2_eq` (the Table 3 projection does not change the coefficients);
   `m3_first_obstruction_of_functional`, `m6_first_obstruction_of_functional`.  For the
   `F = -6D₂Θ` orientations the extraction is done inside `m3_reverse_hcancel_of_voa` and
   `m6_reverse_hcancel_of_voa` (item 3 status).

Remaining (as of 2026-10-04, end of the session): only the VOA-side inputs listed below, which
enter the four `*_obstruction_of_voa` theorems as named hypotheses.  The links between the
even-block statements and the integer-label tables are done (`TableLinks.lean`:
`thetaCoeff_L7A2_link`, `PThetaA1A1A2_link`, `PFG7m_link`, `PThetaG7m_link`; `M6ReverseSym.lean`:
`PFG6m_link_sym`, `PThetaG6m_link_sym`), as are the closed forms of all `SθE*` and the
`SL(2, ℤ)` relations (`sl2_relations_*`).

`hcancel` then becomes a theorem **relative to** these external and VOA-side inputs (audit
item 5):

* Zhu modularity of the character vector (giving `σ` and the covariance of `V`);
* Huang's identification of Zhu's `S` with the categorical `S`;
* the identification of the even `S`/`T` block with `SθE*`, `TθE*` (a finite check given the
  modular data);
* finite image of `σ` (hypothesis `hfin`; determined by the explicit matrices once `σ` is pinned
  at `S`, `T`, manuscript lines 3772–3774);
* the VOA-side `q`-expansion, polar and holomorphy data of `δv`.

## 4. Mathlib observations

* There is no multi-dimensional Poisson summation and there are no lattice theta series in
  Mathlib.  Both are provided here.
* `CFC.sqrt` works for real positive definite matrices under `open scoped MatrixOrder`.
* Polynomial × Gaussian Fourier transforms came from
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` along modulations.
* `Matrix.PosDef` is now defined via `Finsupp`; use `PosDef.of_dotProduct_mulVec_pos`.
* Mathlib has the `η` `S`-law (`ModularForm.eta_comp_eq_csqrt_I_inv`) and `eta_ne_zero`.  It has
  no presentation of `SL₂(ℤ)` and no Weil representation.
* `AddSubgroup.index_eq_natAbs_det` exists, but the Smith-form route
  (`existsUnique_residue_of_smith`) avoids index theory and is checkable by `decide`.
