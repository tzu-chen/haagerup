# Exact positive-mode test on three grade-five words

Producer: `hi_cft_20260923_next_p5_positive.py`. Root alone launches it under
`hi_cft_safe_run.py`. No numerical run was made during preparation.

The default180second run builds the three exact fields
`P5_j=A[7]_0 P4_j` and checks thirty exact products
`PCT(A[i])_5 P5_j` against the six-current space. The PCT fields are each
independently reduced into the frozen exact S2 span, so their membership in U
does not depend on an unrecorded conjugation claim. A nonzero exact current
residual supplies an actual U current outside K. Combined with the previously
proved dichotomy U=B or U1=K, this proves U=B.

Optional `--modes 5,4,3` additionally checks grades two and three, giving ninety
products in total. A nonzero result there is reported as an exact failure of
the selected lower-space containment; the producer itself does not silently
upgrade it to a new-current witness. No grade-four modular test is included.
Passing the finite list does not prove all positive modes or properness.

Estimated peak0.4–0.7GiB RSS, with the existing all-S2/S3 row load already
measured near0.23GiB in the lower-control producer. Added liveness includes
three P4 fields (6989 total terms), three P5 vectors (each capped40000 terms),
one output/residual pair, ten small PCT fields, and at most one32MiB artifact
serialization together with its parsed vector. Primitive caches are64creation,
64vertex,128basis-mode entries. Individual coefficients stop at2048bits; saved
relation coefficients at4096bits. A1GiB RSS boundary and3GiB AS hard ceiling
apply. Permanent host reserve and group limits remain unchanged.

The default job budget is180seconds; the ninety-product optional run may use
up to600seconds only after root review. Mode generation cost is uncertain,
so this is a bounded experiment rather than a completion promise. An outer
timeout with a short kill grace is recommended, preserving the last atomic
summary and previously written exact source artifacts. No workers or native
dense matrix solves are used.

Each P5 artifact stores its complete exact vector and mode recipe; its file
and uncompressed-content hashes are recorded. The summary authenticates the
canonical P4 data, exact S2/S3 source rows, current basis, FastField controls,
PCT function, general grade-five mode engine, and this producer. Each target
has an exact relation and target hash; a failing target also stores its full
exact vector and residual. Use a new output name for each attempt; this small
prototype does not resume a partial test list.
