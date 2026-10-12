# All-trace and larger-ground filters for gamma0

Separate source: `hi_cft_third_gamma0_d6_check.py`. It reads the frozen
joint-ground output, checks its source hash, recomputes every constituent
dimension/index/energy and both positive trace equations, and never imports
or edits the original enumerator. No numerical job has been run by this
author. ROOT owns all execution.

## Third identity and all-current trace table

For each A1 factor let a,b,c be the ordinary indices on c1,d1,d4, and k
its positive integral level. The exact weight-two modular certificate fixes
every other leading trace once these are chosen:

| Module/grade | Ordinary trace index |
|---|---|
|vacuum grade1|4k-9a-b-3c=4|
|b|20k-9a+b+3c|
|a and c0|18k+9a|
|c1|a|
|c2|6k-6a|
|d1|b|
|d2|10k+b-4c|
|d3|30k+9c|
|d4|c|
|d5|4k-b-3c=4+9a|
|d6|2k-b+2c=4-2k+9a+5c|

The full table is independently derived in
[CFT's trace note](hi_cft_third_gamma0_all_ground_traces.md).
Every finite representation index must be nonnegative. These conditions
already sharpen the first-stage witness set, without any affine-energy
comparison. The output separately records negative d6, other negative
ground indices, and optional odd-ground parity rejections.

For each surviving witness the code asks whether its two d6 indices occur
on a **joint** SU2xSU2 representation of dimension14. With `--include-d5`,
it asks the same question for dimension13 and indices `(4+9aL,4+9aR)`.
The current code does not apply representation dimension constraints to
the larger remaining grounds, only their nonnegative trace indices.

The default finite-support check permits every integrable irrep `(n,m)`
with `nm<=dimension`. If the original input used the energy filter, the
same explicit module-unitarity/nonnegative-commutant-energy premise is
inherited. Each constituent then additionally satisfies

\[
\frac{n^2-1}{4(k+2)}+\frac{m^2-1}{4(l+2)}\le h,
\]

where d5 has `(dimension,h)=(13,7/13)` and d6 `(14,8/13)`.
Those are the gamma0 ground weights, not the gamma1 multiplicities.
`--third-only` omits both larger-ground dynamic programs; its summary
still includes every explicitly recorded pre-DP filter.

## Optional invariant-form parity

The `--bilinear-parity` mode has a separate exact justification. A
selfcontragredient irreducible module has a unique nondegenerate invariant
bilinear form up to scale. Transposition preserves invariance, so it is
either symmetric or alternating. L0 is self-adjoint for that form;
different grades are orthogonal and its restriction to every grade is
nondegenerate. An odd-dimensional grade therefore forces the entire
module form to be symmetric. This is the elementary argument recorded in
[the bilinear-form note](hi_cft_third_odd_ground_bilinear.md), with its
primary Li/van Ekeren references.

The c1,d1,d4,d5 grounds have odd dimensions3,7,5,13. The d6 ground is
even-dimensional14, but its **next** coefficient is441, which is odd.
This is visible in the unnumbered Haagerup character display following
[EG equation(2.7), printedp22](https://arxiv.org/pdf/1006.1326).
Thus d6 also has a symmetric form. No categorical indicator is guessed.

A finite SU2xSU2 irrep `(n,m)` has bilinear sign `(-1)^(n+m)`. A
symmetric representation must contain every quaternionic type
(`n+m` odd) with even multiplicity. The code applies this to the
original small grounds and builds it into the d5/d6 support dynamic
program. The unflagged baseline deliberately omits this restriction.

## Exact support algorithm and scope

For each level pair, a bounded unbounded-coin dynamic program stores one
decomposition for each reachable `(dimension,left_index,right_index)`.
Irrep types are visited in a fixed order; total dimension increases when
a copy is added. This represents every multiset of allowed irreps, while
retaining only an existence witness for equal index triples. All indices
are nonnegative, so trimming states above the requested coordinate and
sum bounds cannot remove a solution. In the symmetric-form mode,
quaternionic types are added in pairs; all other types are unrestricted.

Every surviving original3/7/5 witness is retained and linked to its input
index. For it, one d6 and optional d5 witness is saved, with directly
recomputed dimension and indices. This is sufficient for a necessary
support test; it is not a list of every large-ground decomposition.
No branching, fusion, affine descendant or higher-character constraint
is inferred from the existence of a finite witness.

## Resources and controls

Input JSON at most2MiB, at most400 level pairs and1000 original witnesses;
the actual finite input has244. Each DP is limited to20,000 states across
all15 dimensions, with small integer keys and at most14 irrep labels per
stored witness. One level's DP is released before the next. Conservative
process peak below100MiB fits a128MiB AS guard; a60second alarm gives an
independent runtime bound. Crossing a resource bound raises an error and
can never be interpreted as an exclusion.

Prepared controls independently enumerate small decompositions at
dimensions3,4,5,7 and compare exact index support with the DP, for
unrestricted, symmetric and alternating forms. Every returned witness
is reconstructed and checked. A forced state-budget failure confirms
that resource exhaustion is explicit. Input bytes and both source files
are hashed/rechecked before output promotion; no existing output is
overwritten.

ROOT, CFT_constraints and Uniform independently read and passed the full
source, coefficient table, DP/parity logic, exact-target reconstruction,
resource bound and failure semantics. The source is frozen for ROOT's
controls; no author execution has occurred.

ROOT commands after independent source review:

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_d6_check.py --input hi_cft_third_gamma0_joint_finite_results.json --include-d5 --output hi_cft_third_gamma0_large_grounds_finite.json
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_d6_check.py --input hi_cft_third_gamma0_joint_finite_results.json --include-d5 --bilinear-parity --output hi_cft_third_gamma0_large_grounds_orthogonal.json
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_d6_check.py --input hi_cft_third_gamma0_joint_energy_results.json --include-d5 --bilinear-parity --output hi_cft_third_gamma0_large_grounds_energy.json
```
