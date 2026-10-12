# Independent physics and transcription review

Reviewed on 29 September 2026. This is an editorial and static source review of the expanded draft, not a fresh verification of the CFT construction. The reviewer read the saved JSON/TSV files, inspected the transcription routines, and extracted the physics pages from the compiled 322-page PDF with `pdftotext`. No lattice producer, numerical workload, eigensolver, or research replay was run.

## Result

The expanded physics material preserves the distinctions required to interpret the data: raw versus normalized fields, the 96-field intermediate slice versus the complete 113-field tensor, global versus Virasoro blocks, selected lattice chiral blocks versus sewn bulk correlators, diagonal-center defects versus the selected first-factor Haagerup action, and tube multiplicity spaces versus full projector images.

The static spectral and thermal review found no substantive convention error. Two normalization details needed explicit attention: the left lowering factor `8640^(2p)` and the rescaling of the raw spin-three coordinate fields. The former is printed and derived in the physics expansion. Both parafermion and Potts conversion formulas are now present in `coordinate_details.tex` and its assembler; their exact values are recorded below so the coordinate atlas and correlator formulas can be compared directly. No substantive issue remains open in the material reviewed.

## Exact coverage incorporated

- Thirteen highest-vector norms and all 113 component indices, Cartan weights, and norm ratios.
- Every one of the 169 ordered pairs of current multiplets, including empty target sets.
- One phase-sensitive representative for each of the 318 nonzero ordered multiplet maps. The remaining 1879 maps are explicitly zero. The saved sparse tensor has 18,365 nonzero components among 1,442,897 ordered components.
- An explicit two-factor transvectant formula reconstructs all component coefficients from these representatives and their recorded norms. Its algebraic derivation was reviewed, including the no-factorial lowering convention and conversion from raw projection coefficients to unit-field coefficients.
- All 32 resolved stress projections of the eight original multiplets and all nine nonzero primary targets in the extremal `u`-pair sum rule.
- All 198 saved global-block rows: six families with weights 0 through 32; the corresponding reduced Taylor coefficients are printed alongside them.
- All 30 surviving Gaussian terms for the two independent reflection-positive `u` orderings, all nine selected lightest-module blocks, and all fifty saved rational-point correlator values.
- All 78 unordered center fusion products, specifying all 144 ordered products and all 1728 fusion coefficients by commutativity; all twelve complete twisted bilinear matrices; all 78 distinct diagonal Cardy annuli.
- All 36 ordered Haagerup fusion products, the full 6-by-12 forgetful matrix, all twelve tube multiplicity spaces, all six Haagerup twisted spaces, and all 21 distinct extension annuli. Annulus reversal supplies the remaining fifteen ordered extension annuli.

The table generator checks that the set of representative multiplet triples exactly equals the support obtained from the full saved sparse tensor. This is a saved-data coverage check, not an independent calculation of the mode products.

## Normalization findings

### Left current lowering

The saved raw lowering basis has

`N_(m,p,q) = N_(m,0,0) * 8640^(2p) * p!*(n_m-1)!/(n_m-1-p)! * q!*(r_m-1)!/(r_m-1-q)!`.

The torus-gauge derivation is explicit: for the left root, the gauge factor is `1/(5^2*8^4*9^3) = 1/8640^2`. Consequently `(F_L)_0^* = 8640^2 (E_L)_0`, while `(F_R)_0^* = (E_R)_0`. This agrees with all saved component norms checked by the transcription routine. It is consistent with the original manuscript's transported positive form; it is an additional explicit convention, not a change of the underlying basis.

### Raw and canonical spin-three fields

`structural_fields.tsv` stores the raw parafermion `primary` as `w` and the raw Potts `weight_three_primary` as `w_P`. They should not be silently identified with a canonically normalized `a` satisfying `a_(5)a = c/3`.

The exact source is `hi_cft_20260923_proof_pf13_ope.json`, whose key called `norm` is the bilinear self-OPE coefficient here, not automatically a positive Hermitian norm:

- Parafermion: `w_(5)w = -86086 + 36894*s*t`, with `s=sqrt(13)`, `t=i*sqrt(3)`. Write `a=sigma*w`, where `sigma^2=-(7+3*s*t)/9223500`; then `a_(5)a=8/15`.
- Potts: `(w_P)_(5)w_P=8424`. Write `a_Potts=w_P/sqrt(31590)`; then `(a_Potts)_(5)a_Potts=4/15`. Its unit field is therefore `w_P/sqrt(8424)`, up to overall sign.

The parafermion square root is a phase-sensitive rescaling, whereas the subsequent division by `sqrt(c/3)` is positive real. Changing the final sign of the canonical generator does not alter its identical four-point function. The coordinate atlas should retain the raw vectors and print these conversion formulas. The physics expansion now explicitly points to those conversions before using canonical `a` and unit `a_hat`.

## Spectral and thermal conventions checked

The thirteen chiral tables each retain all twenty-five saved grades: twelve `U` modules and the holomorphic `E8` vacuum module. Grades are measured from actual lowest weights, particularly `h_(d3)=15/13`, rather than the twist representative `2/13`. Equal unflavoured `a` and `c0` characters continue to label distinct modules.

The inherited descendant-removal convention includes the vacuum correction `+q`; the full diagonal-state convention is `Delta=2h_i+n+m`, spin `n-m`, and multiplicity `a_i(n)a_i(m)`, or `v_i(n)v_i(m)` for double Virasoro primaries. The folded spin tables correctly state that a positive-spin row counts each sign separately, not their sum. The transcription code checks equality of the two source rows before folding.

The saved fundamental matrix contains 26 coefficient matrices, keyed `-1` through `24`, hence 3744 matrix entries. An earlier prose count of 3888 was reported and corrected. The printed recurrence coefficients include indices 0 through 25, needed for the nonvacuum grade-24 calculation.

For thermodynamics, the conventions `t=beta*v/L`, `b=2*pi*t`, `E=Delta-2/3`, `F/(2*pi*v/L)=-log(Z)/b`, `C_V=b^2 Var(E)`, and `S=log(Z)+b<E>` agree with the saved source. The source has eighty-digit decimal precision and five temperatures for each of two theories; all six reported observables give sixty interval rows in total.

The endpoint transcription uses `ROUND_FLOOR` for lower bounds and `ROUND_CEILING` for upper bounds at twelve decimal places, with an explicit enclosure assertion. This remains correct for negative free energies and negative mean energies. The 120-digit decimal context is ample for the saved endpoints. Positive tail bounds are first rounded upward to eight significant digits; the subsequent `.7E` formatting retains exactly those eight significant digits. The cutoff is `Delta=24`, so the shifted energy cutoff `70/3` is correct. Modular partition-function tails and requested-temperature moment tails are distinguished, with separate evaluation/reference temperatures. The intervals remain conditional on positivity and full modular invariance, as stated in the source.

## Coordinate atlas conventions checked

The source `grade2_fields.tsv` contains 337 rows. `structural_fields.tsv` contains 525 rows, including exactly 91 repeated `p,z` rows and 434 additional spin-three rows. The assembly routine checks equality of the repeated records and prints them once.

The oscillator encoding agrees with the mode engine: integer `j` represents `alpha_(j mod 8)(-1-floor(j/8))`. Repeated indices are repeated commuting oscillator factors; there is no divided-power normalization. Momentum vectors are in the ordered eight-dimensional simple-root basis. The coefficient order `(1,s,t,st)` agrees with the exact field encoding, and rational coefficients are formatted without rounding.

## Verification limits and layout

The source distinctions and construction dependencies remain visible in the expanded draft. In particular, finite block positivity through 32 is not presented as an all-weight proof; selected nonvacuum lattice blocks are not presented as a sewn diagonal bulk correlator; modular-data checks are not presented as a reconstruction of associators or arbitrary OPE coefficients.

The optional `physics_tables/check_transvectant_reconstruction.py` was supplied for a future root-coordinated guarded check. It was not executed by this reviewer, and no passing result is claimed. The two substantial physics paragraph overflows found in the first build were corrected by allowing the current-type list to wrap and putting boundary-overlap decimals in a table. Text extraction from the successful PDF showed the normalization, coupling, and scope prose present and readable. Visual rendering of the final PDF is handled separately by the root agent.
