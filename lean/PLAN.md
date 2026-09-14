# Remaining formalization plan: closing the hyperbolic-gamma interface

Checkpoint status (2026-09-14, commit `0daf48c`): the conditional development
built cleanly, with no `sorry`, and

```
#print axioms HaagerupIzumi.Concrete.EGEquations_concrete
-- [propext, Classical.choice, Quot.sound]
```

The gamma function enters only through the structure argument
`G : HypGamma (ω₁ n) (ω₂ n)` (`Analytic/HypGamma.lean`). This file records
what it would take to replace that structure by a construction, so that the
main theorem holds outright for Ruijsenaars' hyperbolic gamma function.

Tier 1–2 complete (2026-09-14): `GammaCore.lean` constructs
`ruijsenaarsCore n hn : HypGammaCore (ω₁ n) (ω₂ n)` from the explicit
integral. All its fields are proved: global holomorphy, shifts, reflection,
the exact pole and zero sets, nonzero simple residues, the residue at zero,
reality/positivity, and the exact-rate uniform ratio bound on arbitrary
bounded vertical strips. The constructor's axiom audit is
`[propext, Classical.choice, Quot.sound]`. The whole existing conditional
odd-order development also rebuilds after the interface refactor.

Tier 3 remains in progress. No complete `HypGamma` constructor or
unconditional Evans–Gannon theorem is yet claimed. The new
`ResidueAlgebra.lean` proves intrinsic residue uniqueness/linearity and
corrected-contour additivity for use in this stage.

Use `python lean/safe_lean.py --build FILE` to check
one module with already-built prerequisites under the project's resource
limits; these checks are serialized across agents.

Everything in Tier 1 and Tier 2 is standard; Tier 3 is where the mathematics
of BSS Chapter 7 lives and where most of the risk is. Sizes are rough,
calibrated against the current analytic half (about 9.5k lines).

## Tier 1 — construct γ and prove the local properties (complete)

Fields: `poleSet`/`zeroSet` (as used by `differentiableOn`, `ne_zero`,
`eq_zero`), `shift₁`, `shift₂`, `reflect`, `residue_zero`, `residue` and
`hasResidue`, `real_pos`, `real_axis`.

Route: the BSS normalization on the strip `0 < Re z < Ω`,

    log γ(z) = −∫₀^∞ ( sinh((2z−Ω)t) / (2 sinh(ω₁t) sinh(ω₂t))
                         − (2z−Ω)/(2ω₁ω₂t) ) dt/t,
    γ(z) = exp(log γ(z)),

then extension to `ℂ` by the real shift relations. This is the centered
Ruijsenaars function evaluated at `i(z−Ω/2)`; the rotation and translation
are necessary to match the interface's conventions.

Steps:

1. Define the integrand, prove absolute integrability on `(0, ∞)` for `z` in
   the strip (uniformly on compact subsets), and holomorphy of the integral
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
2. Prove the two shift identities on the strip. This reduces to the classical
   integrals `∫₀^∞ sin(at)/sinh(bt) dt = (π/2b) tanh(πa/2b)` and the analogous
   integral with `sinh(ω₁ t) sinh(ω₂ t)`; neither is in Mathlib. Suggested
   proof: expand `1/sinh` as a geometric series in `e^{-2bt}` and integrate
   termwise (`∫₀^∞ e^{-ct} sin(at) dt` is elementary), or use the residue
   machinery already in `Analytic/Residue.lean`.
3. Reflection `γ(z) γ(Ω − z) = 1` and reality on the real axis are immediate
   from oddness of the integrand; positivity on `(0, Ω)` from the sign of the
   integral.
4. Extend by `γ(z + ω₁) = 2 sin(πz/ω₂) γ(z)` and `γ(z + ω₂) = 2 sin(πz/ω₁) γ(z)`
   to a meromorphic function on `ℂ`. Well-definedness needs the two shifts to
   commute on the strip (they do, by the identities themselves). Poles and
   zeros come from the sine factors; residues at the poles from the shift
   identities and the residue at the origin.
5. Residue at the origin `√(ω₁ω₂)/(2π)`: the two shifts give
   `R = ω₂ γ(ω₁)/(2π) = ω₁ γ(ω₂)/(2π)`; reflection and positivity fix the
   positive square root. The specialized periods satisfy `ω₁ω₂ = Ω`.
   Simple poles require an irrational period ratio; the construction must
   establish that hypothesis for the specialized periods.

Original estimate: 4k–6k lines. The integral convergence, differentiation,
and meromorphic gluing also require substantial analysis and endpoint
bookkeeping; the definite integrals are not the only new work.

## Tier 2 — `ratio_bound` (Lemma 2.4) (complete)

The proof needs the exact exponential rate of `|γ(z + c)/γ(z)|` as
`Im z → ±∞`, uniformly on bounded vertical strips, because the decay
conditions (`|θ| < π(1 − g/Ω)` and the like) are sharp. This follows from
Ruijsenaars' asymptotics

    γ(z) ~ exp( ∓ iπ ( z²/(2ω₁ω₂) − (ω₁² + ω₂²)/(24 ω₁ω₂) ) ),  Im z → ±∞,

or, more cheaply, from a direct estimate of `log γ(z + c) − log γ(z)` through
the integral representation after shifting `z` into the strip (the shift
identities contribute explicit sine factors whose growth is known).

Preferred route: prove
`log |γ(x+iy)| = π(x−Ω/2)|y|/(ω₁ω₂) + O(1)` uniformly for `x` in compact
subintervals of the fundamental strip. A cosine-transform decomposition
reduces the leading term to `∫₀^∞ (1−cos(2yt))/t² dt = π|y|`; this avoids
constructing the full complex phase asymptotic.

Estimate: 1k–2k lines. Confidence: medium.

## Tier 3 — the integral identities

### 3a. `K4_line`, `K4_even`, `K4_swap` (moderate)

Define `K₄(r, s, x, y)` directly by the vertical-line integral with crossed
poles added back, formula (2.2), at the parameter ranges actually used
(`K4Conv` and `K4NoPinch` hypotheses), instead of by meromorphic continuation.
Then:

* `K4_line` is the statement that the value does not depend on the line, a
  contour shift with the residue theorem (`strip_residues_gen`), exactly as in
  `LeftProduct.lean`/`RightProduct.lean`;
* `K4_even` is the substitution `z ↦ −z`;
* `K4_swap` (7.7) is a substitution plus a contour shift.

Estimate: 2k–3k lines. Confidence: medium. The definition must be checked to
agree with the draft's `K₄` on the parameter set where both are defined; only
the identities matter for the proof, not the agreement.

### 3b. `two_gamma` (2.17), `K4_euler` (Lemma 7.3), `K4_four_term` (Lemma 7.4) (hard)

* `two_gamma`: the hyperbolic beta integral. Standard proof: the integral as a
  function of the parameters satisfies first-order difference equations in
  `ω₁`- and `ω₂`-shifts (contour shift plus the shift identities; our
  machinery), the ratio to the claimed product is therefore periodic with two
  incommensurable periods; boundedness plus Liouville
  (`Differentiable.apply_eq_apply_of_bounded`) and density of the period
  lattice give a constant; the constant is fixed by a pinching argument
  (residue as two poles collide). Needs holomorphy of parametric integrals,
  the identity theorem, and a careful pinch computation.
* `K4_euler`: the Euler transformation. Either through `two_gamma` applied
  twice with a Fubini swap of the resulting double integral
  (`MeasureTheory.integral_prod`, with the decay estimates of Tier 2), or via
  the same difference-equation method.
* `K4_four_term`: contour shifts of `K₄` combined with the shift identities,
  along the lines of Chapter 7, Step 5 of the draft. Moderate once `K₄` is
  concrete and `K4_line` is available; the draft states it after continuation
  in parameters, which the direct definition avoids.

The four-term statement also requires `ω₁ω₂ = ω₁+ω₂`, in addition to
`ω₁−ω₂ = n`. This hypothesis is now explicit in the interface and supplied
at its specialized use. For `two_gamma`, Ruijsenaars (2011), Appendix C,
Proposition C.1 offers a direct dual-shift argument whose constant is fixed
by a Fourier integral of `sech`; use this to avoid a separate pinching
normalization argument if its parameter domain fits the required extension.

Estimate: 6k–12k lines. Confidence: low.

## Recommended order and intermediate milestones

1. Tier 1, then Tier 2: instantiate `HypGamma` from the construction except
   for the six `two_gamma`/`K4_*` fields. Milestone: a structure
   `HypGammaCore` (the Tier 1–2 fields) with a theorem
   `ruijsenaars : HypGammaCore (ω₁ n) (ω₂ n)`, and `HypGamma` refactored as
   `HypGammaCore` plus the integral identities. The main theorem then reads:
   for Ruijsenaars' gamma function, assuming (2.17), Lemma 7.3 and Lemma 7.4.
2. Tier 3a: define `K₄` concretely and prove the three easy identities.
   Milestone: only `two_gamma`, `K4_euler`, `K4_four_term` remain assumed, and
   all three are statements about explicitly defined integrals.
3. Tier 3b, starting with `K4_four_term` (contour arithmetic), then
   `two_gamma`, then `K4_euler`.

## What Mathlib provides and what it does not

Provides: Cauchy–Goursat on rectangles (used in `Residue.lean`),
differentiation under the integral sign, dominated convergence, Fubini,
Liouville, the identity theorem, the real and complex Gamma function API as a
model for the file structure, `ZMod.dft`.

Does not provide: the double sine or hyperbolic gamma function in any form,
the Fourier integrals of `1/sinh`, q-Pochhammer products for `|q| = 1`
(so the infinite-product definition of the double sine is not usable for real
periods; the integral representation is the practical definition), the
hyperbolic beta integral.

## Not planned

The Evans–Gannon reconstruction theorem (Chapter 10) and the categorical
conclusions remain outside the formalization.
