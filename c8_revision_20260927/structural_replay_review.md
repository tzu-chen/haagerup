# Structural replay allocation and provenance review

27 September 2026. This review performs no numerical job. Root controls
every execution serially through the permanent launcher. The commands
below retain its32GiB host reserve,8GiB group-RSS watchdog, and two-CPU /
two-thread limits, with a narrower2GiB address-space cap. The old temporary
memory exception is expired.

## First two native-CLI jobs

From `/home/tzuchen/Codes/haagerup`:

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 300s python hi_cft_20260923_next_structure_core_extension.py --seconds 280 --output c8_revision_20260927/core_extension_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 300s python hi_cft_20260923_next_81top_exact.py --sector all --seconds 280 --output c8_revision_20260927/top81_replay.json
```

These are **separate serial jobs**, not parallel commands. Check actual
host/cgroup availability at launch, as required by the launcher policy.

The core producer reconstructs120 sparse weight-two vectors, with at most
12 vectors in a Cartan block. Its exact kernel routine holds one image and
one tracked lift per pivot; `vadd` makes new dictionaries rather than a
dense in-place workspace. It keeps the25 zero-energy vectors and their
small joint eigenspaces for serialization. The underlying exact engine has
12000-entry vertex and basis-mode caches,2048-entry creation cache, and
16384-entry dot/cocycle caches; its grade ceiling is two. There are no
ambient dense matrices or numerical-library imports. Allow conservatively
0.5GiB RSS including Fraction temporaries, copies, cached mode expansions,+and the JSON output. The old measured time was6.72s with40060KiB RSS.
Required facts include S2 dimension120, known-core dimension15,
zero-energy dimension25, and all six order-thirteen target weights.

The top producer treats four81-state sectors sequentially. It stores at
most30 sparse operator matrices per sector, with100000-entry and2048-bit
coefficient caps. Its in-place additions act on sparse dictionaries; there
is no dense81^4 commutant matrix. Cyclic elimination stores at most81 rows
and their recipes. Old-sector matrices are released when rebound; only
the small certificate records persist. Dot/coordinate/gauge caches are
bounded, and the dot cache is cleared between sectors. The earlier full
resource review is `hi_cft_20260923_next_81top_resource_review.md`.
Conservative expected peak is below0.5GiB; the old four-sector run was3.10s
with26452KiB RSS. **Exit zero is insufficient**: the producer handles a
time/budget stop and can return a partial record. Require `status=complete`,
four sectors, and in every sector `cyclic_dimension=81`,
`irreducible=true`, `seed_eigenspace_dimension=1`, and
`exact_weighted_adjoint_checks=true`.

## Unchanged hardcoded-output producers

The new `replay_structural_input.py` imports an unchanged, frozen producer.
It replaces only that module's `Path` constructor. Exactly one request for
that producer's original output path is redirected to a fresh revision
path. All other path requests are returned unchanged. Exactly one output
write must occur. The output JSON is compared in full with the frozen
record, excluding only `seconds` and `peak_rss_KiB`, before installation.
Writing uses an exclusive temporary file and a no-overwrite hard link.
Source and original-certificate hashes are checked before and after the
run. It does not modify the source file, rename old results, monkeypatch
global pathlib, or change the mathematical assertions.

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 600s python c8_revision_20260927/replay_structural_input.py potts --output c8_revision_20260927/potts_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 600s python c8_revision_20260927/replay_structural_input.py pf13_membership --output c8_revision_20260927/pf13_membership_replay.json
```

The Potts producer explicitly constructs the standard lattice weight-three
field, verifies primarity, and derives it from the generated weight-two
space. Its old run needed one additional zero-mode pair beyond normal
descendants, ending at Cartan-zero rank41, in8.25s with97808KiB RSS.

The PF13 membership producer independently reconstructs the relevant
Cartan-zero grade-three span from weight-two products, reduces the saved
primary into it, checks its PCT-stable line, and computes the positive
stress identity as an exact vector equation. Its old run used154 zero-mode
pairs and rank58, in179.77s with sampled group RSS0.114GiB. The replay
therefore strengthens both actual inclusion and the stress identity.
The span stores at most58 grade-three pivots, and the exact4 engine's
12000-entry caches are bounded. Fraction rows and temporary `vadd` copies
are the main live objects. Conservative estimate for either replay is
below0.75GiB RSS. Their indirect numerical-module imports initialize only
the small rank-eight and grade-two lattice data; neither selector calls
the exploratory numerical main, grade-three floating setup, eigensolvers,
or ambient dense matrix builders. No worker process is created.

The adapter was written and statically reviewed by the audit agent, not
executed by it. A successful run must end with adapter status
`unchanged_producer_exact_replay_passed` and exit zero. Parent code must not
mistake a producer's intermediate success log for adapter completion.

## Provenance boundaries discovered

The frozen640-file combined ledger, and its first650-file supplemented
replay, already bind the core-extension and81-top sources/results; the
Potts sources/results; and the PF13 exact-field, membership, nonlinear,
upper-pole, simple-pole, decoupling and DLY result records. However, the
combined source graph omitted three producers and two recursive fields:

* `hi_cft_20260923_proof_pf13_exact.py`;
* `hi_cft_20260923_proof_pf13_dly.py`;
* `hi_cft_20260923_proof_pf13_weight7.py`;
* `hi_cft_20260923_proof_pf13_W5.json`;
* `hi_cft_20260923_proof_pf13_W6.json`.

The truncation comes from lines51--54 of `proof_pf13_weight7.py`.
Its output has no embedded source hash. The upper-pole resume producer
loads W5 and authenticates15 earlier successful assertions via the saved
log; it recomputes only the last pole. The nonlinear and truncation
producers may reuse W5/W6 checkpoints, so those field files are genuine
dependencies rather than optional reports.

The older `hi_cft_20260923_proof_artifact_audit.json` does retain all five
historical hashes in its `manifest_sha256` table. The revised
`authenticate_inputs.py` now includes that historical manifest and checks
all five specific hashes explicitly. W6 is8.8MiB, above the revision
JSON-parse cap, but it is only stream-hashed, so the8MiB JSON cap remains
unchanged. This supplements the graph without changing any frozen record.
Binding historical bytes still does not replay the expensive W5/W6 mode
constructions or turn those records into independent formal proofs.

The full weight-seven/truncation producer is not recommended as a short
replay: the historical truncation stage alone took1057s, followed by a
larger weight-seven product, and its cap is1800s. Likewise, the original
PF13 exact-field producer reruns floating coefficient recognition before
exact checks. Neither is needed for the four bounded replays above.
The DLY seven-coefficient conversion and simple-pole scalar algebra are
tiny exact Fraction calculations and are suitable for an additional
reviewed replay if root requests them; no lattice mode computation is
needed for those two checks.
