# Exact P4 controls: allocation and proof review

23 September2026. Root reviewed the finite Casimir construction, all mode
indices and resource bounds. The structure agent has launched no job.

The producer is `hi_cft_20260923_next_structure_p4_controls.py`. It reads
the authenticated lower checkpoint using the already reviewed GMP loader,
and constructs one exact right triplet from source operator0 acting by
mode zero on r3_000705. Two left and eleven right Casimir factors remove
unwanted finite K-types. All current modes have output grade4; only the
six Virasoro controls lower to grades3 and2. The fixed number of Casimir
factors follows the ambient lattice norm bound, not a guessed truncation.

The output contains actual (1,3) vectors,18 exact current identities,
six exact lower-space relations and a split-prime replacement check
against the three recorded modular extras. The latter does not establish
an exact upper rank for the normal span. The source graphs of the exact
vectors bind the frozen lattice/source files. A discovery-database
snapshot hash and the digest of consumed modular rows are recorded
separately, because later pilot target appends do not change these exact
vectors or their source-word proof.

Expected memory: approximately0.30GiB for authenticated GMP S2/S3 data,
at most0.15GiB for several sparse grade4 projector vectors and bounded
mode caches64/128/256, and below0.10GiB for the read-only modular database,
state index, serialization and remaining interpreter overhead. Thus
reviewed expected peak is below0.60GiB. The process requires an address
limit at most2GiB and enforces a768MiB RSS boundary,12000-term vector cap,
2048-bit raw coefficient cap and4096-bit reduction coefficient cap.
The vectors payload is capped at32MiB before compression.

Default hard alarm is300seconds; root may select a reviewed value up to
900seconds without changing memory limits. Use the permanent safe launcher,
one teamwide numerical slot, its host reserve and two-thread/CPU caps.
The modular producer must be closed before this read-only consumer runs.
The calculation does not resume partially: output summary and vectors
appear only after all controls pass. No earlier partial log is a PASS.

The algebraic conditions and remaining exact weight4/5 gates are written
in `hi_cft_20260923_next_structure_h4_certificate.md`. Passing these small
controls does not itself prove properness or identify a full character.
