# Exact replay of the H4 singlet premises

New producer `hi_cft_20260923_c8two_h4_singlet_premise.py`; root-only launch.
It reads closed source certificates and writes one fresh atomic JSON.
It does not construct lattice modes or call a native solver.

The producer authenticates the old exact H4 kernel seeds; replays every
saved kernel-basis raw vector, raising action, elimination coefficient,
pivot normalization and pending raising residual using exact four-component
GMP rational arithmetic; and authenticates the twelve new exact H4 records
covering the residual supports. Input coordinates lie in the independently
known 322-dimensional grade-three quotient. Its output asserts only that
the twelve pending weight-zero classes are joint current singlets modulo
W4. Their exact projected membership remains a separate gate.

The exact basis has at most322 rows per operator and vectors have at most322
coordinates, with a4096-bit arithmetic cap. Only one operator's working
basis is retained. All JSON inputs are capped at32MiB; actual sparse input
files are much smaller. Source SQLite files are read one at a time with a
2MiB cache, disabled mmap, and a512MiB file-size cap. No database is copied
or mutated. Source hashes are streamed. All nested source graphs, original
record digests and full-zero-residual flags are checked.

Expected RSS is0.15–0.4GiB, with a768MiB review boundary and hard AS cap2GiB.
The internal alarm is180seconds, maximum accepted300; root should use an
external200second timeout. The permanent one-job rule,8GiB group watchdog,
32GiB host reserve and two CPU/thread limits remain enforced by the safe
launcher. The script rejects open journal/WAL inputs and protects all
authenticated input paths from output replacement.
