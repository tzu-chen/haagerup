# Independent charged-span replay

Root-only serial job through the safe launcher, with 2 GiB address limit,
the permanent 32 GiB host reserve and at most two CPUs/threads. Use a
180-second internal alarm and a 200-second external timeout. No native
solver, workers or subprocesses are used.

The verifier uses Python integers and Fraction parsing from the previously
audited independent Gate4 verifier, rather than the producer's prime field
class. It authenticates source files, replays all 644 lowering coordinate
vectors, checks both sl2 commutators and four cross-axis commutators against
the exact raising certificate, then reconstructs all 28 retained charged
seeds from the saved exact lower relations and independently repeats rank.

Four sparse 322-column current matrices, the lower-coordinate tables and
the small echelon basis dominate storage. These are bounded by the already
known quotient and lower-space dimensions; no lattice-mode vectors are
rebuilt. Each compressed record is bounded at 8 MiB, input certificate at
32 MiB, and SQLite at 256 MiB with a 2 MiB page cache and no mmap. Expected
peak is below 0.3 GiB. Output is bounded by the shared 32 MiB atomic writer.

This adds independent arithmetic and representation checks; it does not
claim an independent implementation of the lattice vertex-operator modes.
Those remain authenticated through the producer and exact source graph.
