# Feasibility of a strong-generation proof through degree three

23 September2026. Algebra/source inspection only; no new mode or rank job.

The first useful question is whether the full normal-product span

    N4=K1_(-1)S3 + T S3 + S2_(-1)S2

contains the needed weight-four singular products. This is more informative
than extending the existing weak-word grade-four span without distinguishing
normal products from singular products. Here S3 is the certified956-dimensional
finite span. All reorderings and derivative placements are included in the
displayed N4 by the VOA identities, once the required lower-grade products
are known to lie in the selected lower spaces.

The existing tolerance1e-5 grade-four file is not this test. It records
4423 current/translation descendants,5313 after normal-ordered u*S2,
5941 after u_0*S3 and6010 after additional generator modes. Only the first
number concerns all K/translation descendants. The second uses the single
actual u, not all of S2 on the left. Thus neither5313 nor6010 is an
established dimension of the full N4. These are also numerical dimensions,
not characteristic-zero certificates.

## Size of the new degree-three generator space

The exact N3 has dimension634 and the exact S3 dimension956. Thus a
candidate with U1=K1 and U2=S2 needs322 further degree-three strong
directions. The following is an affine-PBW prediction of its K-types,
not a new checkpoint-row extraction or certificate.

Write (l,r) for the tensor product of finite sl2 representations of
dimensions l and r. The known nonaffine degree-two multiplets are

    2(1,1)+(1,5)+2(1,9)+(1,13)
      +(2,2)+(2,6)+(2,8)+(2,14).

There are ten highest vectors and98 dimensions. The predicted quotient
P3=S3/N3 is

    3(1,3)+(1,5)+5(1,7)+2(1,9)+3(1,11)
      +(1,13)+2(1,15)+(1,19)
      +(2,2)+(2,4)+2(2,6)+2(2,8)+2(2,10)+(2,12)+(2,14).

This has18 left-singlet copies of total dimension162 and10 left-doublet
copies of total dimension160:28 highest vectors,322 dimensions. It comes
from87 copies in S3, using its exact saved weight table, minus59 predicted
copies in N3. For the latter, affine-vacuum grade three contributes68
dimensions; the two commuting stress directions contribute14; the four
left-singlet charged copies contribute252; the four left-doublet copies
contribute300. The total is634. At left level1, the grade-one singular
submodule removes the spin3/2 summand above a fundamental top, which is
essential to this count.

This PBW description is valid for the expected affine-primary degree-two
multiplets; their exact annihilation relations, or directly the row counts
in the saved634 checkpoint, should be checked before using this table as
a certificate. The dimension agreement alone is not a substitute for that
check. All subsequent workload counts below use this28-copy prediction.

## What covariance genuinely saves

For each pair of finite K-modules, the map a tensor b -> a_n b is
K-equivariant. If the target normal-product span is K-stable, it suffices
to check one highest vector in every left irreducible copy against every
vector in the right module, followed by K closure of the outputs. Indeed
highest-left tensor all-right generates the full tensor product under
diagonal lowering: subtracting the term with lowering on the right
isolates lowering on the left. This also works for both sl2 factors.

Checking highest-left against highest-right alone is insufficient.
Repeated irreducible copies and all tensor-product channels must be kept.
One can instead use Clebsch--Gordan highest-channel vectors, with an exact
record of every multiplicity, but that requires a separate channel builder.

A candidate strong generating space is K1 plus the98 new S2 directions
plus a K-stable322-dimensional complement P3. Existing composite S2/S3
vectors need not be treated as additional independent generators.
The new high-weight tests are:

* S2_0 P3 in N4: at most10*322=3220 highest-left mode calls.
* P3_1 P3 in N4: at most28*322=9016 calls.
* P3_0 P3 in N5: at most28*322=9016 calls.

Skew symmetry can remove some duplication, but no reduction has been
assumed here. Lower singular outputs, including neutral S2 fields and all
required current modes, must also pass. The expected strong span in weight
five is generated from K1_(-1)N4, T N4 and S2_(-1)S3; it contains the
other derivative placements through quasi-commutativity and lower tests.

## A bounded route and its limits

First reconstruct the28 highest P3 vectors from the existing grade-three
checkpoint and verify the K-type table. This uses weight-three blocks
only, with no ambient-grade-four/five enumeration. Prefer short exact
mode-word representatives to dense arbitrary orthogonal combinations;
record any highest-vector linear combinations exactly.

Second build N4 over the existing split prime, streaming one Cartan block
at a time, then test S2_0 P3 and P3_1 P3. The normal-product seeds are
six current modes on956 S3 vectors,956 translations, and roughly ten
nonaffine highest S2 fields on120 S2 vectors, followed by K closure.
This is a concrete bounded pilot rather than a proposal to store all of
B4, whose known dimension is71052. Give it explicit sparse-term/cache
caps and retain raw word provenance. Its runtime cannot be inferred from
the26-second X2 run: the fields and intermediate vectors are much denser.

Only if this pilot supports closure should a generic grade-five engine be
written and audited. The current exact engine accepts left fields of
weight at most2, so P3-left products need a genuine mode-engine extension,
not just a larger output-grade parameter. Recursive normal-order formulas
or a Heisenberg-oscillator/lattice-vertex recursion must handle derivative
factors and arbitrary left oscillator degree. Per-action fixed momentum
and grade bounds allow sparse operation without a full B5 basis.

A positive closure proof requires exact characteristic-zero residual
identities or equivalent exact linear-combination certificates. Equal
finite-prime ranks alone do not prove containment over the number field.
Even a finite-prime failed membership can reflect a rank drop of N4 at
that prime unless its characteristic-zero rank or an exact annihilating
functional is separately certified. Thus modular pilots guide the work;
they cannot by themselves complete this strong-generation argument.

This route could settle properness if all the finite singular products
close. At present it is a new finite route with a substantial grade-five
engine/certificate requirement, not a consequence of the existing956/6010
span dimensions.
