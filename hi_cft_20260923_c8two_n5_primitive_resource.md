# Primitive-left direct N5 subset

New files only: `c8two_n5_primitive_inputs.py`, `c8two_n5_primitive_prime.py`
and `c8two_n5_primitive_exact.py` (each with prefix `hi_cft_20260923_`).
The frozen full-S2 input/prime/exact-v1 and support-v2 sources are unchanged.
Only the root launches numerical work, serially under the permanent guarded
launcher; retain3 GiB AS,32 GiB host reserve and at most two CPUs/threads.
The exact consumer retains its1400 MiB RSS boundary; the prime producer's
boundary remains1 GiB. External timeout is mandatory around native solves.

The candidate family retains every prior matching-weight current(-1) and
translation descendant of saved raw normal grade-four fields and the canonical
P4 triplet. It replaces the120 left S2 basis vectors in products by the ten
original weight-two fields, each paired with every matching-weight saved S3
row. Recipes are explicit `S2_primitive_minus1_S3` records containing operator
index0..9, mode−1, exact grade-three row ID and output weight.

Every retained recipe is an actual normal word. This workflow asserts only
positive containment in that candidate subset. It does **not** require or
claim that these products exhaust the highest projection of the full normal
span. Such an exhaustion theorem could justify a negative result, but no
negative result from this producer has that meaning. All target channels,
canonical P4 conventions, FE projectors and early containment checks are
unchanged. Product-order choices are explicit and task-digest bound.

The new prime wrapper injects the new input class into the frozen producer's
module only inside its own process. Its source hash and the new input source
hash enter the complete source graph before the frozen resume comparison.
Existing complete-mode cache/original-mode controls remain, and two additional
comparisons check an actual primitive product at scalars1 and7. The wrapper
records a separate primitive candidate policy. Atomic checkpoints, source-ID
provenance, closed-input safeguards and output protection remain inherited.

The exact wrapper extends the audited support-v2 consumer. A primitive product
is reconstructed as `provider.ops[operator]` mode−1 applied to the authenticated
exact S3 input. The complete ordinary specialization digest, full projected
specialization and final characteristic-zero residual are all checked by the
frozen consumer. Finite-prime support omission remains a proposed subset only.
The new exact adapter source is bound in `primitive_exact_recipe_extension`.
Downstream certificate readers must authenticate this extension's source graph,
the support-v2 helper/adapter policy graphs, and the original top source graph.

Resource ceilings are unchanged and candidate metadata becomes smaller.
The full120 S2 input vectors remain loaded for frozen source compatibility, and
the old recipe builder briefly constructs its bounded metadata list before
discarding full-S2 products; this adds at most a few MiB. No discarded product
is evaluated. Prime expected peak remains0.4–0.8 GiB RSS; exact0.7–1.3 GiB RSS.
The ten left fields are already registered in both prime and exact action
caches, so the new products use existing cache identities. All vector40k-term,
source20k-term, rank300, database512 MiB, native512 MiB preflight, coefficient
height and cache limits remain unchanged. Native solves require a reviewed
external timeout because Python alarms may not interrupt ctypes immediately.

Runtime improvement is unmeasured. The product family is much smaller, but
retained descendants and projections may still dominate. First proposed
root-only prime payload (300-second allowance; external320 seconds):

```text
python hi_cft_20260923_c8two_n5_primitive_prime.py --weight 0,2 --output NEW_primitive.json --seconds 300
```

After that source is closed, a containing subset can be tested exactly with a
fresh output (600-second allowance; external620 seconds):

```text
python hi_cft_20260923_c8two_n5_primitive_exact.py --database NEW_primitive.sqlite --source-summary NEW_primitive.json --output NEW_primitive_exact.json --max-rank 300 --seconds 600
```

Only syntax checks were run by the implementing agent. No numerical controls
or jobs were launched by any implementing agent.
