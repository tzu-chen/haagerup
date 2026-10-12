# Independent audit of the final H4 singlet recovery

23 September 2026, `/root/exact_grade4`. This note records source review and
read-only consistency checks. All numerical jobs were launched by root under
the permanent resource guard; this agent ran no numerical or symbolic job.

## Frozen producers and independent source reviews

The joint-singlet helper, prime producer and exact consumer are respectively
`hi_cft_20260923_c8two_h4_singlet_common.py`,
`hi_cft_20260923_c8two_h4_singlet_prime.py`, and
`hi_cft_20260923_c8two_h4_singlet_exact.py`. Their frozen SHA256 digests are:

* common: `ed93e17059a5b98ee0be46bd132eccf40eaebd486f48d99ad27ccf00b807269e`;
* prime: `fb1650fa7ca987dab22dcaa430cfaea1df73fbc134797c42ca76e128871043df`;
* exact: `dbe2b700748d421cc240979260d8b5d0c03e6e2a8fd5ecda99b9f8067dd7c81c`.

The structure and c2 agents independently approved the final sources. The
source artifacts contain the same frozen hashes. The grade-four current
highest-weight bounds are 4 and 24. On the weight-zero block the prescribed
FE polynomial kills all nontrivial current types. Skipping later factors on
one axis only after its raising action vanishes is valid; the other axis is
still processed. The canonical P4 weight-zero vector is omitted because its
certified triplet has zero joint-singlet projection.

Each accepted column is the projection of an actual authenticated normal
word, not a proposed upper-rank spanning statement. Exact ordinary vectors
match their entire prime specialization digest; projected vectors also match
the entire saved prime vector. The exact invertible minor is used only to
find coefficients. A full characteristic-zero sparse residual decides each
identity. No characteristic-zero upper bound for N4 is inferred from a
finite-prime rank.

## Closed result checks

The prime summary and log agree on rank 21, 12 contained targets, and cursor
232 among the selected 279 normal columns. It completed in 32.310 seconds,
with sampled peak group RSS 0.139 GiB and guard exit 0. Early containment is
sufficient; no exhaustion assertion is used.

The exact summary and log agree on 12 verified targets, zero failed targets,
rank 21, and `all_source_targets_verified=true`. It completed in 51.602
seconds, with sampled peak group RSS 0.214 GiB and guard exit 0. Largest
vector coefficients had 148 bits; largest relation coefficients had 402
bits. The native matrix had 138-bit coefficients and a 2,822,400-byte
workspace estimate. FLINT 3.4.0 used one thread. The unchanged native
512-MiB preflight and rank-100 review limit were respected.

The independently audited raising-premise replayer completed all 24 checks
for the same twelve targets in 3.341 seconds, at 0.052 GiB sampled group
RSS, with exit 0. It reconstructs saved exact raising-coordinate kernel
bases and authenticates the twelve additional exact raised relations. It
does not evaluate new lattice modes.

## Combining the certificates

The final combiner `hi_cft_20260923_c8two_gate4_singlet_verify.py` was
independently source-audited. It identifies the pending words as precisely
the original 130 requested targets minus the 118 directly passed targets,
then matches those twelve pairs against the raising-premise certificate,
prime target words and exact relation records. It independently recomputes
all twelve full residuals with cleared-denominator integer arithmetic.

Let W4 be the full current-stable normal span plus the actual P4 triplet.
The raising premise says both E currents kill each pending class modulo
W4. Every FE projector factor is therefore identity on that class. Hence
the exact projected membership implies the unprojected membership. This
step needs no new semisimplicity or dimension assumption.

The combiner then authenticates the 2,145 old exact seed records and adds
the 130 now-certified records in the saved raising/Nakayama test. Its
closed output is `hi_cft_20260923_c8two_gate4_verified.json`, with status
`all_Gate4_identities_proved_by_exact_seeds_and_raising`, covering 2,898
primitive-highest-left A0P3 identities. This is Gate4; Gate5 is supplied by
the separately authenticated Jacobi reduction.

Finally, rereading the recursive strong-generation proof revealed no new
circle. Nested Wick contractions lower total pair weight; its sole
same-total undifferentiated-generator case lowers left weight. Direct P4
Virasoro controls precede the Virasoro reduction of positive modes. Once
Gate5 is certified, the finite gates imply strong generation in weights
one through four and U1=K of dimension 6, without assuming a characteristic-
zero dimension of N4 or using a conditional vacuum character as input.
