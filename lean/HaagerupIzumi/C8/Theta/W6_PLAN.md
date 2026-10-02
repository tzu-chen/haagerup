# W6 plan: the theta identities `hcancel` (state at the end of phase 2, 1 October 2026)

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

## 2. Written but NOT compiled (moved out of the tree to `lean/tools/w6_drafts/`)

The c8q queue could not admit any job during the last part of phase 2.  The guard printed
"A legacy or exclusive guarded job holds the shared gate".  Per the root's instruction, the three
new files were therefore moved to `/home/tzuchen/Codes/haagerup/lean/tools/w6_drafts/`.  They are
complete drafts and have never been elaborated.  To resume:

1. Move each back into `Theta/`, in the order `LatticeData`, `Eta8`, `QExpansion`.
2. `c8q check` it and fix any errors.
3. `c8q build` it.
4. Register it in `C8All` and `C8Axioms`.

The pending queue request `200350-29fec8` (check of `LatticeData.lean`) will fail on the missing
file and can be ignored.

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
1. **Define `λ, μ` (`κ, φ`) from `A, B` (`P`)** as the manuscript does (audit item 4), before
   applying `pole_cancellation`.  Today they are free variables of the `*_obstruction`
   theorems.
2. **The representation `σ`** (about 1 session).
   * Take `σ` from the modularity of the character vector (Zhu; DLN for finite image), as in
     `CharacterUniqueness`.
   * Identify Zhu's `S` with the categorical modular `S` via Huang's theorem (external).
   * State the manuscript's "multiplication by `η⁸` identifies it with the Weil representation"
     as `σ(S)` and `σ(T)` on the even block equal to `-1/√|D| · e(-(γ,δ))` times the
     `η⁸`-character, and `e(q(γ) - 1/3)`.  This is a finite check from the `G_{2,3}`/`A_{2,1}`
     modular data.
   * Then `covariant_of_S_T` gives covariance of `Θ_H/η⁸`.  The even projections use the
     symmetry lemmas of `LatticeData`.
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
4. **Coefficient extraction** with `qcoeff_eq_of_tsum_eq`, to obtain `hcancel` in its current
   form: about 0.5 session.

Remaining total: about 5–7 sessions.

`hcancel` then becomes a theorem **relative to** these external and VOA-side inputs (audit
item 5):

* Zhu modularity of the character vector;
* DLN finite image;
* Huang's identification of Zhu's `S` with the categorical `S`;
* the identification of the even `S`/`T` block (a finite check given the modular data);
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
