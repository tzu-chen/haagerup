# Exact grade-four producer: review and bounded launch proposal

The producer is `hi_cft_20260923_next_grade4_exact.py`. No numerical or
exact-arithmetic workload was run by the implementing subagent. Its only
executed check was Python bytecode compilation. The root owns the shared
numerical slot and must review and launch the pilot.

## Intended mathematical scope

1. Reconstruct the previously certified 120-dimensional S2 using the same
   sparse input products, preserving their unechelonized representations.
2. Reconstruct the previously certified 956-dimensional S3 using current
   and translation descendants, the specified highest weight-two products,
   and exact current-lowering closure. Verify every Cartan multiplicity
   against the earlier grade-three certificate.
3. Store the entire exact S3. Previous producers retained only dimensions.
4. Generate S4 from current and translation descendants of S3, `u_-1 S2`,
   `u_0 S3`, and closure under the two current lowering operators and `u_1`.
   This is the same finite generator prescription as the preceding numerical
   6010 calculation. No target rank or numerical block dimension is imposed.
5. In a separate audit phase, check every mode of the six currents, omega,
   and u whose target is at the same or a lower grade, on S1 through S4.
   A failing exact residual is saved rather than silently enlarging a span.

Even a complete exact rank 6010 and every finite low-mode audit do not control
higher intermediate grades. They do not prove properness, rationality, a
vacuum character, or the Haagerup category.

## Resource estimate before launch

The previous exact S3 run took about 535 s and less than 0.2 GiB RSS. This
producer adds provenance and checkpoint serialization and uses smaller mode
caches. A conservative S3 estimate is 9–15 minutes and below 0.5 GiB RSS.
Its in-place sparse subtraction avoids recopying unchanged coefficients,
but no speedup is assumed before measurement.

S4 has up to 7000 retained rows, compared with 956 in S3. Coefficient growth
and denser Cartan blocks can make the full calculation take hours. The
full runtime is unmeasured and must not be inferred from the 31 s floating
calculation. First measure a 180–300 s S4 pilot; use its saved term counts,
progress cursor, largest coefficient height and RSS before extending it.

There is no dense 71052-dimensional ambient basis and no dense linear
algebra. The largest explicit allocations are dictionaries of sparse rows,
one candidate/reduction vector, elimination recipes, bounded basis-action
caches, and one Cartan-block serialization at a time. At the default cap of
1,000,000 saved sparse terms, budgeting approximately 900 bytes per term
gives 0.84 GiB for row storage, before caches (budget 0.4 GiB), provenance,
temporary coefficients and JSON buffers (budget 0.3 GiB). These are rough
conservative accounting figures, not measured peak claims. Fraction height
is separately capped at 2048 bits; exceptionally tall coefficients can use
more memory. A 1800 MiB soft RSS stop and 3 GiB hard address-space cap are
recommended for S4. The soft RSS check occurs between exact operations,
so the hard cap remains essential. Saved-term and bit-length caps refuse
the next insertion and checkpoint the previous completed work.

No BLAS, eigensolver, NumPy, multiprocessing or detached process is used.
The permanent safe launcher supplies the one-job lock, at most two threads
and CPUs, 8 GiB group RSS watchdog, at least 32 GiB host MemAvailable and
cgroup checks. The expired September 15 exception is irrelevant.

## Checkpoint and provenance format

`CURRENT` points to a complete checkpoint directory. Each has one gzip JSON
file per nonempty `(grade, Cartan weight)` block, a field file, and a manifest
with source/file SHA256 hashes, exact cursors, dimensions and stage history.
Unchanged blocks use hard links; changed blocks are streamed a row at a time.
Only after all files are written does the producer atomically replace
`CURRENT`. A kill during a write leaves the preceding complete checkpoint
usable. Old directories and incomplete `.partial` directories are retained;
the root should inspect disk use during extended work and may remove older
complete generations once a later CURRENT has been verified. Do not remove
the current checkpoint. Hard-linked files remain valid after old generations
are removed.

Every accepted row stores its mode/ref recipe, ordered exact elimination
coefficients and parent IDs, and final normalization. Fields retain their
explicit recipes or their hashed original field-file index. The replay phase
checks these identities using exact arithmetic; initial exact field membership
in U still relies on the prior membership certificates. No floating arrays
enter this chain. The exact engine is reused, so replay is an arithmetic
reproduction, not an independent implementation of lattice vertex operators.

Timed and operation-count exits return status 75 after saving. A root should
treat 75 as a completed bounded pilot, not as a mathematical failure. Changing
any hashed source after the first checkpoint intentionally prevents resume;
freeze this producer once the pilot begins, or explicitly audit a new version.

The producer's `--seconds` is checked **between** operations, not by a hard
alarm inside a large exact mode/reduction. SIGTERM and SIGINT request a save
at the next such boundary. Use an outer bounded `timeout` inside the safe
launcher for a hard wall-time policy, for example `timeout --signal=TERM
--kill-after=15s 1260s python ... --seconds 1200`. A forced kill may lose the
current operation, but leaves the last atomic checkpoint usable. Checkpoint
load/write time is included in elapsed time accounting but cannot be
interrupted safely by a requested boundary stop.

## Commands for root review

Inspect `/proc/meminfo` and applicable cgroup limits first. Run these
sequentially, never alongside another team's numerical process.

Initial 60 s smoke pilot, including S2 construction and serialization:

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_next_grade4_exact.py --checkpoint-dir hi_cft_20260923_next_grade4_checkpoint --phase grade3 --seconds 60 --soft-rss-mib 1400
```

Continue S3, using the same directory:

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_next_grade4_exact.py --checkpoint-dir hi_cft_20260923_next_grade4_checkpoint --phase grade3 --seconds 1200 --soft-rss-mib 1400
```

After S3 is complete, a 300 s S4 pilot:

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- python hi_cft_20260923_next_grade4_exact.py --checkpoint-dir hi_cft_20260923_next_grade4_checkpoint --phase grade4 --seconds 300 --soft-rss-mib 1800
```

Only after S4 completes, `--phase audit` starts or resumes the low-mode checks.
`--phase replay` checks every saved field and row recipe and can also be used
after S3. Both accept the same bounded time/operation arguments. A replay of
an incomplete generation certifies its saved rows only. A complete low-mode
audit is recorded explicitly in the manifest; absence of that flag means the
checks remain unfinished.
