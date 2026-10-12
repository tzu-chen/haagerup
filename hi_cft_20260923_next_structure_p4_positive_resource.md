# Exact positive P4 modes: root-only small gate

Producer: `hi_cft_20260923_next_structure_p4_positive.py`.
No numerical job launched by its author. All ten primitive highest
weight-two fields act on the exact canonical P4 triplet in modes4,3,2,
giving90 targets of weights1,2,3. Higher modes are scalar or zero and
are not needed for this diagnostic. It is independent of an assumed
grade-five normal-span closure.

The same run additionally computes all30 exact A1P4 targets of weight4,
then specializes at the saved good split prime and reduces against the
6007 normal plus3 extra rows of the permanently immutable N4 snapshot.
It checks that snapshot's hash equals the discovery hash authenticated
by the P4 control, and checks its source graph. The70k-state index is
retained, while reduced rows are streamed with a4MiB SQLite cache. A
nonzero residual is stored together with the complete exact target and
prime elimination coefficients. It certifies6011 independent actual U4
vectors. A zero prime residual is only a finite-prime containment and
does not certify exact weight-four membership.

The authenticated exact lower loader supplies the same120 S2 and956
S3 rows used by the3970 passed relations, plus six reconstructed exact
current rows. The completed P4 controls and all their source hashes are
authenticated before loading the three field vectors. Each target is
reduced exactly in the saved Cartan block. Relations include target
digests and complete exact residuals. A nonzero residual is saved and
stops immediately; all90 empty residuals are required for success.

This is a bounded one-process, no-worker call with300-second whole-run
alarm, address cap2GiB, soft768MiB RSS boundary, at most two CPUs/threads,
the usual32GiB host reserve and shared single-job lock. Use the permanent
safe launcher. Estimated peak is0.3--0.5GiB: approximately225000 retained
lower-basis terms,6990 P4 terms, bounded caches64/128/256, one target and
residual, the state index and a small120-record JSON certificate. The earlier P4 controls
with the same inputs/caches peaked near0.257GiB. Raw vectors have12000
terms and2048-bit coefficients at most; reduction coefficients are capped
at4096 bits. Input decompression is bounded at32MiB and released before
the mode loop. JSON checkpoints are atomic after each operator's three
fields and immediately on a nonzero witness.

The output does not itself label an abstract VOA: root may combine a
nonzero exact lower residual, or the certified grade-four rank6011,
with the already proved proper-branch dimensions to deduce U=B.
If every target passes, the grade-four A0P3 and grade-five
A0P4 gates are still required for the finite strong-generation proof.
