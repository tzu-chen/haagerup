# Independent review of the H4 exact FLINT consumer

23 September 2026. Read-only source review; no numerical job was launched
by this reviewer. Root owns all launches and the shared numerical slot.

Reviewed sources:

* `hi_cft_20260923_next_n4_h4_flint.py`, SHA256
  `41f0222b5892e2ace3cb76eb313d64d7edfbfb8eb3a4ac8935bbe6982846b5de`;
* `hi_cft_20260923_next_flint_field_solve.py`, SHA256
  `a34162592474e7bc12a211cc3e1fbf6638317ce7832e687dbd20cb3f17989bd4`;
* frozen base `hi_cft_20260923_next_n4_exact_block.py`, SHA256
  `43d8729ec6fcbe8efe0018d4d8af993e25472dd3b5a0a2d934a364efe0f4c283`.

The initial gate passes source review with rank at most64, batch8,
600 seconds and a3GiB address ceiling. Larger ranks need a separate
allocation review; the command-line maximum is not launch authorization.

## Exactness and provenance

The base reconstructs actual raw normal words from authenticated exact
S2/S3 rows, checks their specialization against the modular raw vectors,
and stores their exact coefficients. The extension loads only a P4
artifact with the completed exact-control status, matching vector digest,
and matching authenticated source graphs. A negative column identifier
selects one of these exact P4 fields. The modular extra pivot supplies an
additional square-minor coordinate; it is not used as an exact upper-rank
argument.

The native regular representation is correct in the basis
1,sqrt13,sqrt(-3),sqrt(-39). Solving a field matrix of order n becomes a
rational matrix of order4n. Native output alone proves no containment:
every target is checked against the complete sparse linear combination
of actual normal words and exact P4 fields, and only an empty residual
is recorded as a passed identity.

The producer binds its own source, the native wrapper, the exact-control
summary and vector payload, and the native validation artifact separately
from the frozen base's source graph. On restart it verifies both graphs.
The initially found metadata alias was repaired before launch: the
original normal-column list and its recorded metadata are detached before
P4 is appended. The extended column list is separately copied and checked
on restart. Thus base and H4 resume conditions agree.

Root confirmed that the source N4 database remains permanently immutable;
subsequent modular target checks write separate databases. This matters
because the base authenticates the complete source database digest.

## Resource scope

At rank64 the native rational matrix has256 squared entries. Together
with the already reviewed exact-input cache, three bounded P4 vectors,
eight targets and rational workspaces, the initial estimate below0.9GiB
RSS is conservative. Existing raw-vector, serialized-record and rational
height caps remain in force. The hard3GiB address limit bounds native
workspace growth; no larger allocation is authorized by this audit.

Python's signal handler is deferred during a ctypes native solve. Its
SIGALRM alone therefore does not promise interruption precisely at600
seconds inside C; retain the outer safe-runner supervision and deadline.
This is an operational qualification, not a gap in the sparse identity
certificate.

No result from this consumer establishes an exact upper dimension for
the full normal span. Completed exact relations, together with the H4
criterion and its remaining grade-five gate, are the intended proof.
