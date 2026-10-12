# Small exact Jacobi data checker

Producer: `hi_cft_20260923_c8two_jacobi_check.py`. This is a new source;
all prior producers and checkpoints remain frozen. Root alone may launch it.

The checker loads the 120 exact grade-two echelon rows, decomposes the two
actual highest fields a3 and a6, and combines the source-bound lower-closure
identities for eight pairs. Every combination must have zero component in
the known exact quotient S3/N3. It then authenticates the two completed H4
bottom witnesses, including their nonzero canonical P4-minus coefficients,
exact zero residuals, and nested source/ancestor graphs. It tests the
off-triplet weight only on the bottom inputs. Raising the resulting zero
identity is the separate audited algebraic argument.

No new lattice mode, dense matrix, eigenvector, native solve, or grade-five
vector is constructed. It uses four-component GMP rational field arithmetic
already controlled by the frozen lower-closure producer. Exact coefficients
are bounded by 4096 bits. The 120 retained grade-two rows have a 50,000-term
aggregate cap, with 20,000 terms per row. Each saved relation is decoded
separately (8 MiB lower record, 16 MiB authenticated H4 record); SQLite cache
is 2 MiB and memory mapping is disabled. There are at most 956 coordinates
per lower relation, eight combined results, and two H4 records. Metadata
JSON has an 8 MiB cap, with 32 MiB reserved for the raising certificate.
Source hashes are streamed in 1 MiB blocks. No database is copied or mutated.

Estimated peak RSS is 0.15–0.35 GiB, including imported libraries, metadata,
50,000 exact sparse coefficients/states, one decoded relation, and transient
serialization. The producer enforces a 512 MiB RSS review boundary and a
hard AS limit at most 2 GiB. The default internal alarm is 180 seconds
(maximum accepted 300 seconds); use an external timeout as well. The
permanent team-wide 8 GiB group RSS watchdog, 32 GiB host reserve, two-thread
and two-CPU limits remain in force through `hi_cft_safe_run.py`.

Only a fresh atomic JSON output is allowed. Output and temporary paths are
checked against every authenticated source. Input SQLite files must be closed
and have no journal/WAL sidecar. Optional `--gate4` and `--charged-span`
arguments must be completed, source-bound certificates with the expected
formats, status, dimensions, and quotient order. Without them the output is
explicitly conditional; it proves only the small exact Jacobi data.

The mathematical implications are in
`hi_cft_20260923_c8two_jacobi_proof.md`. A complete Gate5 conclusion additionally
uses Gate4, current stability of the full formal normal spaces, and the
charged-pair spanning certificate. Properness then uses the independently
audited finite strong-generation theorem. No characteristic-zero upper rank
of a selected grade-four or grade-five column list is assumed.
