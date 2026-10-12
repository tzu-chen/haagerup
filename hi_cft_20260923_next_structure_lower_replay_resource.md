# Independent lower-relation replay: review and scope

Prepared23 September2026 for root-only execution. Source:
`hi_cft_20260923_next_structure_lower_replay.py`, SHA256
`bf56020617ceed927356aa2684a254428e8060ba861dce304be23911f3ce7f60`.
No numerical job was launched by the structure agent.

The completed producer certified3970/3970 exact lower relations in77.875s,
with sampled group RSS0.229GiB. This replay imports no lattice mode engine
and does not invoke FastField. Its field multiplication independently
uses the four basis-bit indices, reducing shared bits by13 and-3. It
reconstructs each saved target from the frozen basis and its recorded
linear coefficients, then compares the canonical exact-coordinate digest.
It also independently rebuilds the six current-space echelon vectors
from their documented Chevalley coordinates using scalar rational
elimination, and checks every task recipe and zero-residual record.

The lattice modes themselves are not recomputed. In particular a
quasiprimary zero target is checked against the producer's bound empty
target digest. This is an independent linear-algebra/certificate replay,
not an independent lattice-VOA implementation. All producer, field,
checkpoint and source data hashes are authenticated before replay, and
the completed SQLite artifact is itself hashed into the new output.

Input liveness is capped at300000 sparse terms, with four GMP rationals
per coefficient. Budget0.30GiB for input dictionaries and state keys,
0.05GiB for one reconstructed target and temporary coefficient products,
and0.05GiB for JSON records, SQLite's8MiB cache and interpreter overhead.
No mode caches or dense matrices exist. Conservative expected peak is
below0.45GiB; a768MiB measured-RSS boundary and2GiB address-space
requirement provide margin. Individual JSON records are capped at8MiB,
relation length956, vector length20000, and input rational height4096bits.

Default runtime is300seconds, maximum900; a hard alarm fires ten seconds
after the requested boundary. Root must use the permanent safe launcher,
one teamwide job, its host reserve and two-thread/CPU cap. Completed
targets are atomically checkpointed every20seconds, so bounded calls can
resume without replaying certified targets. An interrupted current target
is retried. The completed producer database is opened read-only/immutable
and must be closed before launch.

The replay does not change the properness boundary. Its sole purpose is
to strengthen the already passed lower gate; exact weight-four A0P3
normal-word identities are still required by the strong-generation proof.
