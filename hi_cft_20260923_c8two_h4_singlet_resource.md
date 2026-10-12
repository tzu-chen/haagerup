# Final H4 joint-singlet projection: bounded allocation review

These NEW producers consume the closed exact `(0,0)` H4 block in
`hi_cft_20260923_c8two_targeted_h4_support`. They do not modify that block or
any frozen source. Root alone launches numerical work through the permanent
safe launcher. The reviewed address-space limit is 3 GiB; external timeout
must cover the entire invocation, because native FLINT may not return to a
Python alarm promptly. Permanent group RSS, host reserve and CPU limits stay
unchanged.

`hi_cft_20260923_c8two_h4_singlet_prime.py` reads the 279 cached actual normal
columns and twelve actual target recipes. It omits the canonical P4-zero
column: the certified P4 triplet has zero joint-singlet projection. The
projector uses the unchanged full factors for left bound 4 and right bound
24; skipping remaining factors on an axis requires an exactly zero raising
action. Original-mode controls include one full target and twelve grade-four
current actions. Rank is capped at 100, states at 5,000, intermediate raising
vectors at 12,000 terms, retained sparse terms at 1.2 million, and SQLite at
256 MiB. The source-vector LRU holds at most 60,000 terms and the whole-action
cache at most 300,000 prime terms / 50,000 entries. In-memory echelon rows,
candidate copies, decoded source records and cache objects are included in
the estimate: expected peak 0.3–0.7 GiB RSS, with a 1 GiB boundary stop and
3 GiB hard AS backstop. Suggested first time budget 300 seconds (external
timeout 320 seconds). Partial atomic checkpoints may be resumed.

`hi_cft_20260923_c8two_h4_singlet_exact.py` consumes the closed prime artifact,
replays ordinary exact source words, verifies their complete prime digest,
applies the rational projector, and verifies the complete projected prime
vector. It selects the recorded invertible minor at rank at most 100 and
uses the already controlled FLINT regular representation solver. The native
workspace preflight remains 512 MiB; no old native cap is increased. Every
relation is checked by a full characteristic-zero sparse residual.

Exact live storage includes the 128 MiB whole-action LRU, 64 MiB projected
vector LRU, at most 60,000 source-vector terms (roughly 60 MiB at observed
heights), twelve live targets with at most 5,000 terms each, a rank-100 minor,
native rational workspaces, and one projected/raised/feedback vector family.
Each exact intermediate is bounded to 2,048 coefficient bits; raised and
feedback vectors are checked immediately after each mode call. Expected
peak is 0.4–1.0 GiB RSS; inherited 1.4 GiB boundary and hard 3 GiB AS remain.
Suggested exact budget 600 seconds (external timeout 620 seconds), and the
existing inherited 2-million exact disk-term bound still applies.

All source files, exact block artifacts, prime output, mode helpers and native
control artifacts are hash-bound. Resume checks require matching source
graphs and metadata; saved relations retain exact coefficients and full word
recipes. Output paths are disjoint from all bound source paths.

The conclusion is deliberately **projected H4 containment only**. Recovering
the twelve unprojected relations additionally requires the independent exact
raising-premise certificate. The producers neither assume that premise nor
claim complete Gate4 merely from projected identities.
