# HaagerupIzumi — Lean 4 formalization of the proof up to the Evans–Gannon equations

Lean `v4.33.1`, Mathlib tag `v4.33.1` (commit `0df444a3`). Built with
`lake build` from this directory (the Mathlib package directory was copied
from `../../equational-theories-lean-stage2/.lake/packages`, so no cache
download is needed). There are no `sorry`s; `lake build` succeeds with
linter warnings only, and

```
#print axioms HaagerupIzumi.Concrete.EGEquations_concrete
-- [propext, Classical.choice, Quot.sound]
```

## Main statement

`HaagerupIzumi.Concrete.EGEquations_concrete` (in `Analytic/Cubics.lean`):
for every odd `n ≥ 1` and every `G : HypGamma (ω₁ n) (ω₂ n)` (an interface
packaging the properties of the hyperbolic gamma function with periods
`ω₁ = d + 1`, `ω₂ = 1 + 1/d`, see below), the concrete coefficient matrix
`D n hn G hodd` built from the samples `W a = -sgn(a) F(a)/√d` satisfies all
four families of Evans–Gannon equations (linear, quadratic, cubic, quartic)
for the cyclic Haagerup–Izumi fusion ring `Z/n`.

The proof follows `../hi_infinitude_expanded.tex` (`../proof_expanded/`)
through Chapter 9 and stops there: the reconstruction theorem of Chapter 10
and the categorical conclusions are not formalized.

## The algebraic half (`CoeffData`)

The structure `CoeffData n K` packages the abstract data used by the
algebraic parts of the proof: a field `K`, `δ` with `δ^2 = n δ + 1`, and
coefficients `W : ZMod n → K` with `W 0 = -1`, `W a ≠ 0`, and
`W a * W (-a) = δ` for `a ≠ 0`. Everything below is proved for arbitrary
`n ≠ 0` and, where stated, `CharZero K` or `K = ℂ`.

| Module | Content (section of the expanded proof) |
|---|---|
| `Coefficients` | `B`, `A = B/τ`, uniform formula, order-three and transpose-like symmetries, axis values, linear identities (3.4–3.8), column symmetries |
| `Residuals` | residuals `Q`, `C`, `𝒞 = τ³ C`, swap symmetry, two-product lemma (5.1) |
| `Quartic` | the quartic residual is a contraction of cubic and quadratic residuals (10.1) |
| `Factorization` | balanced triples, `S`, `P`, their permutation/translation invariance, factorization of `𝒞` with and without corrections (5.7, 5.8) |
| `Boundary` | the boundary cubics `g = 0`, `h = 0`, `h = -g`, `g = h = 0` (Lemma 5.4, Part B) |
| `Balanced` | full match and collision values of `δ²S − τP` (Lemma 5.4, Steps A3–A4) |
| `Degenerate` | every degenerate cubic vanishes (Lemma 5.4) |
| `Interpolation` | vanishing Fourier block lemma on `ZMod N` over `ℂ` (Lemma 2.7), via `ZMod.dft` |
| `Reflection` | reflection by matrix inversion (Lemma 9.3), with explicit inverses of both sides |
| `FourierReduction` | Lemma 6.1: the Fourier transform of `𝒞_{g,h}(·,l)` through `û_{-g}` and the two product transforms |
| `Completion` | descent maps, induction in the ordered range (Prop. 9.1), the normal-form combinatorics (Lemma 9.2), all cubics (Prop. 9.4), and `EGEquations_of` |

`CoeffData.EGEquations_of` says: if all quadratic residuals vanish (`Q = 0`)
and the restricted Fourier vanishing `RestrictedFourier` holds, then the
matrix `A` satisfies all four families of Evans–Gannon equations.

## The analytic half (`Concrete`)

| Module | Content |
|---|---|
| `Analytic/Residue` | residue calculus on rectangles from Mathlib's Cauchy–Goursat theorem: `HasResidue`, generalized residues `HasResidueGen` (poles of order ≤ 2), the rectangle residue theorem, and the strip version `strip_residues(_gen)` with exponential decay |
| `Analytic/HypGamma` | the interface `HypGamma ω₁ ω₂` (see below) and elementary consequences |
| `Analytic/Periods` | `d`, `δ`, `ω₁`, `ω₂` and their arithmetic (`ω₁ω₂ = ω₁ + ω₂`, `ω₁ − ω₂ = n`, rational independence used for pole bookkeeping) |
| `Analytic/Sampling` | `F(z) = 1/γ(ω₂ + z)`, Lemma 3.2, the samples `W`, and `toCoeffData` |
| `Analytic/Contour` | Proposition 4.1: sample rule (Lemma 3.9 for positive labels), the kernel `K_h`, the difference identity, residues, decay, the strip and two-gamma applications, `column_fourier_sum` |
| `Analytic/ColumnFourier` | Lemma 4.3 and `Q = 0` (Proposition 4.4) |
| `Analytic/Windows` | Lemma 3.9 in all cases: `tz_pos`, `tz_neg_nonneg`, `tz_neg_neg`, periodicity `tz_add_n` |
| `Analytic/Products` | the two-ratio kernel `K2'`, Lemma 6.2, its residues and decay, `ε`-choice for the lines, residues `ρJ1`, `ρJ2`, translation lemmas for line integrals |
| `Analytic/LeftProduct` | Proposition 6.3 (1) with (8.4): `left_product` |
| `Analytic/RightProduct` | Proposition 6.3 (2) with (8.10): `right_product` (crossed families, double poles when `h = l`, window sample corrections, the two surviving residues) |
| `Analytic/NegColumn` | Lemma 8.1: `neg_column` |
| `Analytic/Restricted` | no-pinch conditions, Euler/shift/evenness chain for the left kernels, the Γ-factor bookkeeping and the four coefficient identities (`term1`–`term4`), and Proposition 8.2 `bracket_zero` |
| `Analytic/Cubics` | the restricted frequency set (`exists_freq`), `restricted_fourier`, and `EGEquations_concrete` |

### What is taken as given: the interface `HypGamma`

The hyperbolic gamma function is not constructed. `HypGamma ω₁ ω₂` is a
structure whose fields are the properties used in the proof, all of which
are standard facts about Ruijsenaars' hyperbolic gamma function (BSS):

* position of poles and zeros (`poleSet`, `zeroSet`), holomorphy off the
  poles, nonvanishing off the zeros, the two shift identities, reflection;
* simple poles with residues `residue w`, and the residue `√Ω/(2π)` at the
  origin;
* positivity on `(0, Ω)` and reality on the real axis;
* the growth of ratios `γ(z + c)/γ(z)` along vertical lines (Lemma 2.4);
* the two-gamma integral formula (2.17) along a vertical line, with the
  crossed left poles added back (`two_gamma`);
* the four-gamma kernel `K₄(r, s, x, y)` of Chapter 7 with: its value
  through a vertical line with crossed poles added back (`K4_line`),
  evenness `K₄(r,s,x,y) = K₄(r,s,−x,−y)`, the shift identity (7.7), the
  Euler transformation (Lemma 7.3), and the four-term identity (Lemma 7.4)
  at the parameters `R = g/2`, `X = (n+g)/2 + l`, `Y = (n+g)/2 + h`.

The continuation-in-parameters arguments of Chapter 7 are therefore not
formalized; they enter through the last group of fields.

## What is not formalized

* The hyperbolic gamma function itself and the properties listed above.
* The Evans–Gannon reconstruction theorem (Chapter 10) and the categorical
  conclusions.
