# Direct projected N5: reviewed launch design

Prepared 2026-09-23 during the 12:16:30–14:16:30 UTC c8 window. These are new
files; all earlier sources and artifacts remain frozen. Only the root agent
may launch a numerical job, serially through `hi_cft_safe_run.py`. The expired
September 15 exception does not apply. Permanent ceilings remain 6 GiB AS,
8 GiB group RSS, 32 GiB host MemAvailable, and two CPUs/threads. This workflow
requires the tighter **3 GiB AS** launch profile and an external timeout.

## Files and certificate scope

* `hi_cft_20260923_c8two_n5_inputs.py`: immutable N4, canonical P4, and exact
  checkpoint24 inputs; deterministic ordinary normal recipes.
* `hi_cft_20260923_c8two_n5_direct_prime.py`: projects each candidate immediately,
  keeps only independent projected columns, and stops when all selected
  projected targets are contained. There is no ordinary N5 rank computation.
* `hi_cft_20260923_c8two_n5_direct_exact.py`: reconstructs each ordinary recipe
  through the frozen exact H4 provider, verifies its saved unprojected digest,
  reconstructs the rational FE projector, checks the entire specialized
  projected vector, solves a pivot minor using FLINT, and checks the full
  characteristic-zero sparse residual. It reuses the frozen native-solve and
  full-residual implementation; no positive result rests on finite-prime
  containment alone.

The candidate family is all matching-weight K(-1)/translation descendants
of the 6007 saved raw normal grade-four words plus the canonical P4 triplet,
and all matching-weight pairs from the full 120 by 956 S2(-1)S3 family.
Default ordering alternates chunks of eight descendants and eight products.
Alternative ordering is explicit and bound by the task digest. No exhaustiveness
claim is needed: exact containment in any selected actual normal words suffices.

Default operators are 0 through 8. A fixed requested weight groups all compatible
CG channels, at most three targets. For a highest left field of right highest
weight m, only canonical P4 lowering depths 0 through min(m,2) are requested.
Thus the neutral left field has one channel and right-spin-half has two. The
remaining neutral complement follows from total stress and current Sugawara
under the separately proved H4 theorem. Returning from highest projected
identities to unprojected families requires that theorem's K-stability and
triangular Clebsch–Gordan argument; selected columns need not themselves form
a K-stable space.

## Prime pilot memory and time

Recommended first launch: one weight, 300 seconds, 3 GiB AS, external timeout
320 seconds. Its internal RSS boundary is 1 GiB. Expected peak is **0.4–0.8
GiB RSS**, conservatively below 1 GiB, based on the preceding raw/projected
pilots; time to containment is unknown and measured at the first weight.

Simultaneous live storage includes at most 300,000 input S2/S3 terms, a
200,000-term source-grade4 LRU, a 250,000-term echelon-row LRU, and a
300,000-term/50,000-entry complete-mode cache. Prime coefficients are Python
integers. The largest ordinary, raised, feedback, projected, and reduced
vectors are individually bounded by 40,000 terms (source grade-four raw
records by 20,000); several such vectors coexist during projection. There
are at most 120,000 interned grade-five states, 300 projected pivot rows,
and 30,000 candidate recipes. Serialized row and target retention is capped
at 16 million terms in a 512 MiB SQLite file; this is disk storage, not an
in-memory aggregate. Source and output SQLite page caches total about12 MiB.
Transient JSON/decompression buffers are bounded by 16 or32 MiB. Primitive
creation/vertex/basis caches retain only64/64/128 entries; their variable
entry sizes remain covered by RSS boundaries and the hard address limit.

The pilot compares complete original and cached modes for actual target,
descendant, and product recipes at two scalars. Twelve more controls compare
all six zero-current actions on an actual grade-five basis state at scalars
1 and7. Current sl2 normalization and commuting axes are also checked.

## Exact consumer memory and time

Recommended first launch: max rank300, 600 seconds, 3 GiB AS, external timeout
620 seconds with TERM followed by KILL after5 seconds. Expected peak is
**0.7–1.3 GiB RSS**; the inherited boundary stops at1400 MiB. Runtime is unknown:
the earlier full-three-target grade-five identity used111.73 seconds and
0.649 GiB, while some high projected blocks needed multiple intervals.

The three live bounded caches are the raw grade-four provider (128 MiB),
the projected exact-vector LRU (64 MiB), and the whole exact action cache
(128 MiB), totaling320 MiB. The exact mode cache registers only the ten
original fields, six currents and total stress, with up to20,000 entries.
Unregistered full S2 left fields use the original mode engine. Twelve exact
original/cache comparisons use all six currents on a grade-five basis state
at scalars1 and1+sqrt(13). Installation occurs after grade-five engine setup
and provider initialization; all source and control code hashes are bound.

At most three exact target vectors coexist. Every ordinary/projected vector
and immediate raised/feedback intermediate is capped at40,000 terms and
2048-bit coordinates. The source state table and grade-four provider state
table coexist; compressed JSON records, exact decoded records, field objects,
dictionary copies during FE projection, and the current mode output all add
transient storage. Derived exact vector retention is capped at2 million
terms per derived database and each database at512 MiB; it is loaded through
the bounded LRUs, not all at once.

The native solve is at most300 by300 over the quartic field (1200 by1200
over Q), at most three RHS. The existing coefficient-height preflight refuses
an estimated native allocation above512 MiB. Python pivot matrices and up to
three exact targets remain live during native solving. FLINT is single-threaded;
its native workspace is controlled by the hard3 GiB AS ceiling as well as
the preflight. A Python alarm alone cannot reliably interrupt a ctypes native
solve, hence the required external timeout. Relation coefficients retain the
existing4096-bit bound, and the full residual is recomputed exactly over all
sparse states before any relation passes.

## Integrity and interruption behavior

Every input is read as a closed immutable SQLite snapshot and authenticated
by complete-file SHA256; summaries must match source metadata. Full source
graphs include the frozen checkpoint, canonical P4 certificate, engine,
cache helper, new producer/adapter and native-control ancestry. The producer
stores each accepted raw normal recipe, FE factors, ordinary specialized
vector digest and full projected vector. Resume checks counts, contiguous
state/row/target IDs, source-cursor ancestry, factors and task digests. Output
and temporary-summary paths are protected against authenticated inputs.

SQLite metadata and data commit together; JSON summaries are written through
fsync and atomic rename. An interruption rolls back the current uncommitted
candidate. The exact provider has a separate derived cache: losing its latest
uncommitted entries only requires reconstruction; no identity relies on an
unsaved provider entry. Exact coefficient records preserve the frozen schema.
No source is edited after the first launch; later changes require new filenames.

Only syntax checks have been executed by the implementing agent. Numerical
oracle controls, timing and all mathematical outputs await root launch.
