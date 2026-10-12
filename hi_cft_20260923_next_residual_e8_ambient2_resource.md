# Full E8 residual commutant in grade two: launch review

23 September 2026. New producer:
`hi_cft_20260923_next_residual_e8_ambient2.py`.
The author has only edited and syntax-checked it. Root alone owns the
numerical slot. All permanent desktop safeguards apply; the September 15
exception is expired.

## Exact scope and coordinate audit

The integral E8 basis replaces the eighth old E6+A2 simple root by
lambda=omega_1(E6)+glue_sign*omega_1(A2), exactly as in the frozen
81-top producer. Rational LDL enumeration gives every norm-at-most-four
momentum, with asserted shell sizes 1,240,2160. Momentum coordinates are
converted back to the original rational E6+A2 coordinates, so the
Heisenberg Gram matrix, oscillator labels, pairings, and grade-three
normal-order engine stay valid.

The E8 group algebra uses `sector_setup`'s epsilon. Every old-lattice
field, including both Potts/parafermion stresses and the saved B kernel,
is multiplied by its `gauge(alpha)`. This direction is fixed by the
identity gauge(a)gauge(b)epsilon(a,b)=old_epsilon(a,b)gauge(a+b), which
the frozen producer checks. All old cocycle-dependent caches are cleared
before installing epsilon. The B sector must reproduce dimension five
and contain the entire previously saved kernel, not just q and r.

The full E8 grade-two dimension is 4124, split as 1370+1377+1377.
Only Cartan-zero states are retained. The B zero block must have size86;
each of the three blocks has a hard cap256. The kernel of the actual
core stress L(0) is computed sector by sector. Each output vector is
checked against core stress L(-1), all relevant nonnegative Potts and
parafermion stress modes, and the four core current modes. Positivity of
the actual unitary core is the separate theorem identifying zero energy
with its commutant. The producer does not identify that commutant or
assert its rationality.

## Memory and time before launch

The existing B-only calculation took7.29s and29.6MiB peak RSS. The E8
producer does not allocate a 4124-square matrix or even retain all4124
basis vectors. It retains the2401 momentum tuples during enumeration,
at most768 Cartan-zero one-hot inputs, then discards unused momenta.
Only one sector's elimination rows and lifts are live at once.

The bounded grade-three engine has512 vertex entries and512 basis-mode
entries, each limited to512 returned terms; creation has128 entries
limited to256 terms, with the old degree-at-most-two creation cache
still bounded by2048 entries. Mode caches are cleared between sectors.
Exact elimination stores at most160000 coefficient entries across rows,
lifts, and answers. Every visible vector has at most6000 terms and every
number-field coefficient has numerator/denominator bit length at most2048.
These generous worst-case algebra limits permit substantially more than
the expected small kernels; they are stop conditions, not targets.

JSON source files are individually capped at2MiB and decoded once.
Their dictionary trees are deleted after extracting the fields and old
basis. Completed sector certificates remain serialized in memory, capped
at12000 total sparse terms. `json.dump` streams output instead of making
an additional whole-file string. Atomic replacement preserves the last
completed sector if a later one stops. Kernel coefficient objects and
their serialized copies coexist only while that sector is being saved.

Expected peak RSS is below0.35GiB and expected runtime is30--120s, based
on the B result and the small zero blocks; these estimates are not a
performance guarantee. Accounting pessimistically for maximal-bit
elimination rows, sparse tuple/dictionary overhead, both mode caches,
current vector copies, and serialized certificates gives an allocation
budget about1.2GiB. The hard process AS cap is2GiB, below the permanent
6GiB ceiling; the permanent8GiB group watchdog and32GiB host reserve
still apply. No NumPy/BLAS/SymPy workspace, worker, or detached process
is used. A290s-or-less internal alarm and300s external timeout bound
runtime. If a cap triggers, retain the partial certificate and redesign;
do not raise the cap automatically.

Suggested root-only launch, after confirming the shared slot and host
memory through the launcher:

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 300s python hi_cft_20260923_next_residual_e8_ambient2.py --seconds 280 --glue-sign 1 --output hi_cft_20260923_next_residual_e8_ambient2.json
```

The other isotropic E8 gluing is available as `--glue-sign -1` with a
different new output path. One gluing already contains both charge
sectors +lambda and -lambda. Repeating for the other gluing is optional,
not required to establish the chosen E8 host's grade-two kernel.
