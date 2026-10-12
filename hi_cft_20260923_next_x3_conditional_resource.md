# Bounded grade-three conditional rank producer

Producer: `hi_cft_20260923_next_x3_conditional_rank.py`. This is a new
source and does not modify any frozen producer or certificate. Syntax
checking passed; no mode/rank calculation has been run by this agent.
The root agent alone owns the numerical slot.

## Mathematical scope

The frozen X2 producer and independent rank replay certify 1250 linearly
independent reductions modulo 1000003 of explicit U-mode words on the exact
rational space K1-perp in B1. Under the established properness fork
B=U direct-sum X, these words lie in X2. Their unnormalized raw vectors,
not their echelon replacements, are the input here. Reduction of a raw
vector is the reduction of its exact word even though its integer residue
list alone is not a chosen characteristic-zero lift.

The grade-three candidates are K(-1)X2, omega(0)X2, and all certified
charged highest S2 fields acting by mode zero on X2. After each seed stage,
the four K raising/lowering zero modes and actual three-vertex u(1) act
until the retained span stops growing. All these are actual U words.
Only mode outputs of ambient grade three are accepted. Cartan weights are
checked and Gaussian elimination is performed separately in each weight.

The prime is the same split prime as X2, with square roots 231543 of 13
and 1000 of -3. Conversion of exact rational primitive coefficients rejects
denominators divisible by the prime; row elimination divides only by
nonzero finite-field pivots. A resulting rank is therefore a rigorous
characteristic-zero lower bound. No finite-field upper-rank assertion is
made.

Since dim B3=11586 and the separately certified exact finite U-word span
S3 has dimension956, properness implies dim X3<=10630. Reaching rank10630
therefore proves **U3=S3 conditionally on U being proper**. The producer
stops at that threshold; it does not test whether further words increase
the rank. A rank above10630 would disprove properness, but this particular
threshold-stop run will not produce that alternative. A smaller completed
or interrupted rank proves only the stated conditional lower bound.

## Storage and resource review

Hard address-space limit:3 GiB, below the permanent6 GiB ceiling.
The producer checks a1 GiB peak-RSS review threshold at every completed
candidate boundary. One mode operation or checkpoint serialization can
cross that review threshold before the next boundary; the address-space
limit and permanent external watchdog remain the hard safeguards.

Combined live input-X2, raw-X3, and echelon-X3 sparse terms are capped at
2,000,000. An insertion that would exceed the cap is refused before any
row/vector mutation. Full lattice/oscillator state tuples are interned
once, with at most11586 states; raw and echelon rows hold integer state IDs
and plain integer residues. The 1250 X2 inputs retain finite-field scalar
objects because they are fed to the mode engine. Only one accepted X3
source at a time is expanded from IDs into engine state/scalar objects.
Gaussian elimination copies only the current candidate, never all rows.

Two primitive-action caches have4096 entries each. Their values retain
exact primitive rational coefficients; the creation caches have2048
entries, and the inherited dot/cocycle caches16384 each. A single primitive
action has fixed lattice momentum and grade at most3, so its output has
at most192 oscillator states. This is an extreme cache-entry bound, not
an expected occupancy: root/current actions are much sparser. The cache
bound, sparse-row dictionaries, Python object overhead, and one live mode
output motivate the conservative1 GiB RSS review budget. Expected live
storage is roughly0.3–0.6 GiB, but it is not a proven ceiling; a cache-heavy
or dense-block case must stop and be redesigned rather than raising caps.
The permanent host reserve of32 GiB, group-RSS watchdog8 GiB and two-CPU /
two-thread limit are still enforced by safe_run.

No full ambient grade-three basis or dense11586-square array is built.
A single elimination block is bounded by11586 states trivially; the
term cap bounds all retained blocks together. There is no claim that the
zero-weight block has already been counted. Computing it just for planning
would be an extra numerical job and was not done.

Input certificate/field JSON documents are individually limited to8 MiB,
and the X2 JSONL file to32 MiB before parsing. The latter is parsed one
line at a time. Source hashing streams1 MiB chunks. On resume, the saved
state catalog is below16 MiB, and committed vector rows are parsed one
line at a time. A checkpoint serializes only the state catalog, metadata
and block ranks; it does not serialize a second copy of every vector.
New vectors are appended as individual JSONL records with their raw
vector, normalized echelon row, two hashes, pivot, Cartan weight and
explicit mode-word provenance. There is never a full JSONL read_text.

## Checkpoints, replay and time bounds

The summary is atomically replaced only after the JSONL stream is flushed
and fsynced. It records the committed byte count and prefix SHA256, source
hashes (including this producer), state catalog, candidate cursor and
closure cursor. Checkpoints occur after each stage and at candidate
boundaries every30 seconds. A single slow mode can delay that cadence.
The internal alarm is at most600 seconds per invocation, including input
verification and reload. At asynchronous interruption the producer retains
the previous committed checkpoint; it does not certify a possibly partial
current insertion. Resume verifies the committed prefix and truncates
only the uncommitted tail. Completed or saturated certificates cannot be
resumed. Source changes after the first checkpoint are rejected.

The saved echelon rows are trusted only as a hash-bound producer output on
resume; resume is not an independent elimination replay. A lightweight
checker can subsequently reconstruct the row rank from the committed raw
vectors, check the saved normalized rows and validate the acyclic word
graph without recomputing vertex modes. Full coefficient provenance can
be replayed from the source-hashed X2 word producer and this producer.

The X2 run took26.52 seconds /44 MiB. Grade-three state expansion and
elimination are larger; tens to hundreds of seconds is plausible, but
completion within600 seconds is not promised. The first bounded run is
also the resource pilot. Stop at the term/RSS cap and redesign if necessary.

Suggested root-only command, after checking the shared slot and host
memory through the mandatory launcher:

```sh
python hi_cft_safe_run.py --limit-mib 3072 -- timeout --signal=TERM --kill-after=15s 630s python hi_cft_20260923_next_x3_conditional_rank.py
```

Reusing exactly this command resumes a bounded-stop checkpoint. The
internal alarm should stop first; external TERM/KILL merely preserves the
last atomic prefix if a Python operation is unusually stubborn.
