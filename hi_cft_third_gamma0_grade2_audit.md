# Actual ambient grade-two comparison

The standalone `hi_cft_third_gamma0_grade2_check.py` follows the executed
quartic certificate. It adds the actual E8 extension premise
`B=E6_1 times A2_1`, `B|W=0+b`, and CFT's independently identified
embeddings125/187. It does not promote those embedding assumptions to
a statement about every gamma0 VOA or the physical chain.
The exact placements and primary references are recorded in
`hi_cft_third_e8_hosts125_187.md`, independently read and checked here.
In particular [Theorem5.1 of Adamović et al.](https://arxiv.org/html/1702.06089#S5)
contains the required G2_1 times A2_2 embedding in E6_1.

## Coefficients and affine descendants

For `H_hol=(Delta/E4^2)Xi v`, the next coefficient is
`(CHI−504I)v`. At vacuum grade2 the character data give

\[
[D_2D_0\chi]_2=312,\qquad [E_2^2\chi]_2=264,
\qquad [E_2 T]_2=T_2-24T_1=T_2-96.
\]

The constants retain the vacuum-pole terms: the first is
`(5/3)(3/2)120+4(2/3)6+12(−1/3)`, and the second is
`120−48*6+432`. The quadratic `T_2` is independently obtained from
the already executed next-grade engine. These determine all five
quadratic/quartic moments of W2 from the saved three M4 coefficients.

The affine-vacuum grade2 representation is

\[
(3,1)+(1,3)+2(1,1)+(3,3)
+\mathbf1_{k>1}(5,1)+\mathbf1_{l>1}(1,5).
\]

It has dimension `27−5delta_k1−5delta_l1`, quadratic indices
`36−20delta_k1` and `36−20delta_l1`, mixed moment16, and pure
moments `168−136delta_k1`, `168−136delta_l1` in the ordinary
`Tr h^4/4` convention. The remaining W2 subspace is affine-highest:
its orthogonal complement to the current-generated grade2 states is
annihilated by positive current modes, by adjointness and the fact
that W1 consists exactly of these currents.

At least one remaining singlet is the nonzero complementary Sugawara
stress. Its central charge is positive for both retained level pairs.
Affine highest labels obey integrability and `h_aff<=2`. This latter
inequality uses the unitary vacuum VOA, not an assumption that all
irreducible nonvacuum modules are unitary.

## Actual finite ambient representation

CFT independently supplied the following restrictions of the E6
fundamental27:

\[
P_{125}=(2,6)+(1,9)+(1,5)+(1,1),
\]
\[
P_{187}=(3,3)+(2,4)+(2,2)+(1,5)+(1,1).
\]

Let E be the actual E6 adjoint restriction, recovered as
`b_top+(3,1)+(1,3)−A`, with `A=(1,3)+(1,5)` the A2 adjoint.
The affine level-one characters give

\[
B_2=P\otimes P+E\otimes A+(1,1)+2A.
\]

Here E6 grade2 is `1+78+650=27 tensor 27bar`, A2 grade2 is
`1+2*8`, and all restricted SU2 product irreps are selfdual.
The exact dimension is1370, agreeing with W2 dimension120 plus the
b next-grade dimension1250. The helper first verifies the b ground
dimension and all five moments against the quartic prediction; these
already match by independent hand calculation, so no b exclusion is
claimed.

## Support and multiplicities

Subtract both the required affine-vacuum representation and the
grade1 affine descendants of the entire b ground from B2. A b ground
irrep `(n,m)` contributes `(3 tensor n,m)+(n,3 tensor m)`, with the
integrable null `(n+2,m)` removed when `n=k+1` and the corresponding
right null when `m=l+1`. These descendants lie in the b summand,
orthogonal to W, so subtracting them is mandatory. Their dimensions
are400 and468 for hosts125 and187, respectively. The resulting
ambient affine-primary singlet caps are4 and5, matching the independent
commutant calculation.

The remaining ambient multiplicity of each irrep is an upper bound
for the affine-primary part of W2. The optional bounded DP tests its
dimension and five moments simultaneously, enforces the inherited
vacuum symmetric form by even quaternionic multiplicities, and
includes the mandatory complementary-stress singlet.

Every DP state carries both one linked existence witness and a bitset
of **all** attainable singlet counts. Merging equal moment states
unites their bitsets, so a single chosen decomposition never hides a
different possible commutant dimension. The reported counts already
subtract the two affine Sugawara states. They are the counts allowed
by this finite representation relaxation; the actual commutant
weight2 dimension must be among them, but a listed count does not
construct the required highest vectors or OPE.

One-axis and mixed Cauchy inequalities are checked before searching.
Each SU2 type also has nonnegative `2S-I=n(n^2-1)(n^2-4)/10`, giving
two additional safe pruning coordinates.

There is no unrestricted high-grade partition enumeration. The
ambient types and multiplicities are fixed by finite Clebsch–Gordan
products. A global cap of20000 generated DP nodes, including nodes
from previous type stages, bounds both linked-history and live-table
memory. A cap hit aborts with an explicit error and certifies no
exclusion. Default operation reports exact moments without the DP;
`--support` requests the bounded support test.

## Resource and binding

Pure stdlib, two level pairs only, one support search at a time.
Input is at most2MiB and each source at most128KiB. The DP stores at
most20000 six-integer states and linked nodes, plus short singlet
bitsets; expected process peak below100MiB. Use ROOT's128MiB guard
and60second alarm. Source/input bytes and all transitive producer
hashes are checked before output promotion. Outputs are never
overwritten. No author execution has occurred.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_grade2_check.py --input hi_cft_third_gamma0_quartic_results.json --support --output hi_cft_third_gamma0_grade2_results.json
```

## Executed status and exact factorization redesign

ROOT's broad `--support` search reached its20000-node cap safely at
21:54:13UTC. It produced no exclusion. The unchanged source then
completed its moment-only mode at21:54:18UTC in
`hi_cft_third_gamma0_grade2_moments_results.json`. The six remaining
affine-primary targets, ordered as dimension, left/right quadratic,
mixed, twice left/right fourth, are

* host125: `(98,30,1774,575,30,161374)`;
* host187: `(93,100,500,470,508,13148)`.

The new separate `hi_cft_third_gamma0_grade2_factored.py` uses these
immutable targets without changing the first producer. Write a_n for
the total dimension of the right multiplicity space accompanying the
left irrep n. At host125, left integrability gives only n1/2; therefore
a2=30 and a1=38. The mixed moment fixes the right index of the doublet
block to575, and the total right index fixes the singlet block to624.

At host187 the left moments give

\[
a_3+6a_4=34,\qquad a_2=14a_4-36,\qquad a_1=63-14a_4.
\]

Nonnegativity leaves a4=3 or4. The actual n4 right labels are all even,
so a4 is even: necessarily `(a1,a2,a3,a4)=(7,20,10,4)`.

Only these small right-dimension partitions remain. The helper enumerates
each block completely, with actual multiplicity caps and the same
unitary-vacuum energy/parity restrictions, then checks the remaining
right quadratic, mixed, and fourth equations on their full Cartesian
product. An independent hand control gives exactly two host125 doublet
partitions: `(14,8,6,2)` and `(12,12,2,2,2)`. Each output contains every
feasible full decomposition and its commutant singlet count, not a
representative chosen from a larger range.

Depth-first recursion has at most nine irrep types per block and keeps
no broad multidimensional state table. Caps are500000 visited DFS nodes,
5000 solutions per block,1000000 combined tuples, and2000 final
decompositions. These caps abort rather than exclude. Conservative peak
below100MiB; use the same128MiB address limit and60second alarm.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_grade2_factored.py --input hi_cft_third_gamma0_grade2_moments_results.json --output hi_cft_third_gamma0_grade2_factored_results.json
```

The factored certificate was executed successfully by ROOT at22:03:02UTC,
after three independent source reviews. It took0.0045seconds with21424KiB
peak RSS. Host125 used3367 visited partition nodes and4 combined tuples;
host187 used212 nodes and660 tuples. Each has exactly one feasible
affine-primary decomposition, and **the actual full-current commutant
inside W must have weight2 dimension2** under the stated E8 premise.

For host125 the additional affine-primary representation is

\[
2(1,1)+(1,5)+2(1,9)+(1,13)
+(2,2)+(2,6)+(2,8)+(2,14).
\]

For host187 it is

\[
2(1,1)+(1,5)+(2,2)+(2,4)+(2,6)+(2,8)
+(3,3)+(3,7)+(4,4).
\]

The two singlets in these expressions already exclude the affine
Sugawara states. Uniqueness here is uniqueness of finite irrep
multiplicities. It does not locate their vectors within the ambient
multiplicity spaces, nor prove OPE closure or VOA existence.
