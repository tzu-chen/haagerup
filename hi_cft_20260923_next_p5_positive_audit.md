# Independent source audit of the exact P5 positive-mode gate

23 September 2026. Read-only audit; no job was executed by the auditor.
Source reviewed: `hi_cft_20260923_next_p5_positive.py`, supplied SHA256
`3df446d6162163a7e03283a29b1db2bd7302da5aaa6c647da78dab7ca4f196d7`.
Result: PASS, with no requested source change.

The general recursive lattice engine is installed at target grade5 before
`lower.load` generates any operator. Its recursive module globals and the
shared exact-module globals use the same bounded creation/vertex/basis-mode
caches. The saved exact row source and FastField control are authenticated.
Canonical P4 vectors are checked against the independent P4 controls, full
source hashes, grades, weights and ordered triplet labels.

Every PCT left operator is first reduced exactly into the frozen S2 rows,
so the subsequent products use actual U fields independently of any PCT
closure assertion. Each P5 field is the explicit grade-five word A[7]_0P4,
and its complete exact vector and recipe are saved with file/content hashes.
For a weight-two left field, modes5,4,3 produce grades1,2,3 respectively.
The complete exact echelon residual is checked against K,S2,S3; no prime
specialization or tolerance is used. A failing target retains its exact
vector and residual, and successful targets retain full reduction relations.

A nonzero grade-one residual proves that an actual U current lies outside
K. The stated conclusion U=B additionally uses the separately established
current-algebra dichotomy. Failure at grades2 or3 is correctly reported only
as failure of that saved lower-space containment. Passing the finite list
does not establish properness or all-mode closure.

The liveness estimate includes the frozen S2/S3 load, three P4 fields, three
P5 fields, one target/residual pair and one serialized artifact. Vector and
coefficient caps, primitive cache sizes64/64/128, a1GiB RSS boundary and a
hard3GiB AS ceiling are retained. The180second prototype is appropriate for
a root-only safe-launcher run; an external timeout remains a useful hard
termination backstop. All permanent host/thread/single-job limits apply.
