# Gamma0 two-current-factor exact enumeration

The new `hi_cft_third_gamma0_joint_ground_check.py` prepares a necessary
test for the remaining gamma0 current algebra `A1_k x A1_l`. It uses
ROOT/CFT's exact positive trace identity

\[
4+9t_{c1}+t_{d1}+3t_{d4}=4k
\]

for each factor separately. The three ground spaces have dimensions3,7,5
and weights1/3,6/13,5/13 respectively. The trace identity uses the actual
Haagerup modular representation and the gamma0 character, not arbitrary
three low-dimensional representations.

An independent check of the constant is immediate from the same modular
space as the gamma1 audit. For gamma0 the particular trace is
`E2*chi0/12+D(chi0)/4`. Its coefficients in vacuum,c1,d1,d4 are
`-1/2,1/4,21/26,25/52`; the vacuum coefficient includes the polar E2
contribution. Their combination with weights1,9,1,3 is exactly4, while
each of the three saved homogeneous M2 basis vectors has combination0.

For the tensor product of SU2 irreducibles of dimensions n,m,

\[
I_n=\frac{n(n^2-1)}6,\quad
t_L=mI_n,\quad t_R=nI_m,
\]
\[
h_{n,m}=\frac{n^2-1}{4(k+2)}+
          \frac{m^2-1}{4(l+2)}.
\]

The code enumerates **every unordered direct sum** of such irreducibles
with total dimension3,5,7. Colored-partition counts are5,17,52.
Integrability requires `n<=k+1,m<=l+1`. The default additional test is
`h_(n,m)<=h_ground` for every constituent. That inequality explicitly
assumes unitary physical modules, or independently nonnegative affine
commutant L0. It is not inferred from bare unitarity of the VOA.
`--finite-only` omits this energy test while preserving the positive
integrable affine-level constraints. Every Frobenius–Schur parity
restriction is omitted, so the search retains a safe superset.

For a d-dimensional joint representation, the sum of the two Dynkin
indices is at most I_d. Applying the two trace identities and the three
dimension bounds gives

\[
4(k+l)\le8+9I_3+I_7+3I_5=160.
\]

Thus it is exhaustive to take `1<=k<=l,k+l<=40`. Before the ground
filters, convexity gives the residual central-charge bound

\[
c_{\rm residual}=8-\frac{3k}{k+2}-\frac{3l}{l+2}
=2+\frac6{k+2}+\frac6{l+2}\ge\frac{28}{11}.
\]

The output retains all surviving level pairs and **every** joint ground
decomposition witness, with its dimensions, two indices, constituent
affine weights, remaining coset weights, residual central charge and
the explicit energy/parity premises. A surviving witness is not a
branching construction, fusion solution or VOA existence proof. If no
witness survives, the lower bound is null and the empty feasible set is
reported directly.

## Resource and independent controls

Only the standard library and exact `Fraction` arithmetic are used.
There are400 unordered candidate level pairs,74 prepared decompositions,
and at most `5*17*52=4420` global witnesses. The last bound is global
because a decomposition triple uniquely determines both levels via
the two trace equations. No numerical array, eigensolver, subprocess
or external checkpoint is used. With fewer than about40,000 small
summand dictionaries even at the generous witness bound, a conservative
100MiB process envelope fits the proposed128MiB AS guard. A30second
alarm and unchanged-source hash check bound execution. No computation
has been run by the author.

Controls independently sum integer SU2 Cartan weights to verify the
Dynkin-index normalization; test all five dimension3 decompositions,
all three colored-partition counts and left/right permutation symmetry;
test exact integrability/energy boundaries; and substitute every saved
witness into both original trace equations and all three dimensions.

CFT_constraints independently read and passed the complete source,
normalization, colored-partition counts, exhaustiveness, energy-premise
scope and resource envelope. The source is released for ROOT's controls;
no author execution has occurred.

ROOT commands, after independent source review:

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_joint_ground_check.py --output hi_cft_third_gamma0_joint_ground_results.json
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_joint_ground_check.py --finite-only --output hi_cft_third_gamma0_joint_ground_finite_only.json
```
