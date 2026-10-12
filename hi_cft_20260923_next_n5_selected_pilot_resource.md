# Selected grade-five normal-word pilot

Producer: `hi_cft_20260923_next_n5_selected_pilot.py`. It passed syntax
compilation and an independent source audit by the c2_axes agent. No
numerical job was run by its author. Root owns the numerical slot.

## Inputs and finite scope

The source is a CLOSED immutable snapshot of the N4 v2 SQLite database,
with normal rank 6007 and three independent extra columns. Both database
and readable summary are hashed, and their core checkpoint metadata must
agree. Resume refuses changed source hashes.

Actual weight-four generator inputs come from the exact canonical P4
triplet controls, rather than arbitrary quotient representatives. The
consumer requires status `exact_P4_triplet_and_lower_controls_passed`,
checks the vector artifact's path and SHA256 against its summary, verifies
the format and all three names/weights, and authenticates both source
graphs. The exact field coefficients specialize at the same good split
prime as the N4 pilot.

For each selected highest weight-two operator a and canonical P4 vector p,
the target is a_0 p, of weight five. The default `--operators 7` selects
three targets, in Cartan weights (1,11), (1,13), and (1,15). This depends
on the source field's verified weight (1,13), not an assumed representation
dimension. The program computes the actual weights from the bound fields.

The normal column family consists of all six K(-1) and translation actions
on the 6007 saved raw N4 words plus the three canonical P4 vectors, and
ALL 120 S2(-1) by 956 S3 products with a selected output weight. Using the
full S2 basis avoids an unproved shortcut involving current lowering
through omitted Cartan blocks. Only encountered states in the selected
blocks are interned; no ambient grade-five basis is enumerated.

Periodic target tests can stop once the selected targets lie in the current
finite-prime normal-word span. Exhaustion means only that this explicit
column family was exhausted. A surviving residual does not prove a new
characteristic-zero strong generator; passing containment requires exact
relation reconstruction and full sparse verification before it is used
in the all-weight proof.

## Engine and bounds

The independently audited `proof_general_modes_v2` engine is installed with
ceiling five before any mode call. Its existing caches are cleared and
both recursive module globals and x globals are rebound. The creation,
vertex, and basis-action caches have capacities 64, 64, and 128. The
Heisenberg derivative/normal-order indices and finite intermediate-mode
ranges were independently checked in
`hi_cft_20260923_next_grade5_mode_audit.md`.

There are 2464 oscillator monomials of weight five at fixed momentum,
compared with 726 at weight four. The smaller caches account for that
increase. Plan the first call for 600 seconds, AS3GiB, and an internal
candidate-boundary RSS stop at 1GiB. Expected peak is approximately
0.4--0.8GiB RSS; this is unmeasured and the upper allocation estimates
are intentionally conservative. A single mode can finish before the
RSS check; the hard address ceiling is the backstop.

Included allocations and explicit limits:

* The frozen S2/S3 inputs have at most 300000 sparse terms, approximately
  224508 in the saved data. Their finite-field coefficient/state objects
  are retained; the old grade-four span is streamed one raw row at a time.
* The reduced-row LRU has at most 250000 integer terms. At most 120000
  encountered grade-five states and their index/weight maps are retained.
  There are at most 4096 independent rows in any selected Cartan block.
* One generated row has at most 40000 terms. Compressed records have a
  bounded 16MiB decoder. The canonical three-field artifact separately
  allows at most 16MiB compressed/32MiB decompressed; parsed source text
  is released before the main mode/rank loop. Budget roughly 0.15GiB
  transient headroom for decompression, parsed JSON and sparse scratch.
* Primitive caches and their coefficient/state tuples are budgeted at
  approximately 0.2--0.3GiB in the full-cache case. The input fields,
  state indexes, reduced-row LRU, interpreter and sparse working vectors
  account for the remaining estimated 0.2--0.5GiB.
* The output SQLite database has a 512MiB page cap, 8MiB page cache, mmap
  disabled, and disk-backed temporary storage. The read-only source has
  a 4MiB cache. Allow another 512MiB disk for the rollback journal.
* Persisted normal-column raw plus echelon terms are limited to 16million.
  At most 30 targets each contribute one raw and one residual vector,
  both subject to the 40000-term limit. They remain disk backed; target
  testing materializes one target and residual at a time.
* There are at most 30000 selected column tasks per invocation. Larger
  operator batches must be split into separate reviewed outputs rather
  than increasing caps. The default operator-seven pilot is much smaller,
  but its exact task count is determined from the frozen source metadata.

SQLite commits target vectors, accepted columns, their raw mode recipes,
echelon rows, interned states and stage cursor atomically at approximately
20-second boundaries. A hard alarm rolls back the incomplete transaction.
The JSON is an atomic readable summary; SQLite remains authoritative.
All source files, this new producer and the canonical P4 artifacts are
hash-bound. Freeze the producer after the first launch.

Only root may launch, through the permanent safe runner, after the P4
controls have passed and the N4 source is closed. Preserve the 32GiB host
reserve, at most two CPUs/threads, one team-wide numerical job, 6GiB
permanent address ceiling and 8GiB group watchdog. This pilot uses the
stricter 3GiB address ceiling. No larger resource exception is active.
