# Exact N4 relation solve: one-block pilot

Producer: `hi_cft_20260923_next_n4_exact_block.py`. No numerical run was
performed by the author. The producer has passed Python syntax compilation;
root must review it and launch through the permanent safe launcher.

## Choice of exact algorithm

The old grade-four numerical data have maximum ambient Cartan width 3078,
with zero-weight candidate rank 280. These are planning observations, not
an exact upper bound. The frozen grade-three/early grade-four checkpoint
records a maximum retained coefficient height of 410 bits.

Repeating sparse exact elimination over a dense 280-by-3078 block could
touch approximately 861840 field entries and order 120 million field
multiply-adds. A square pivot-coordinate solve instead holds 280-by-280
field entries; the subsequent full residual verification supplies the
proof of containment. This route does not require an exact rank upper
bound. The direct GMP field solver is deliberately simple and independent
of the optional root-supplied FLINT regular-representation solver.

The consumer selects all accepted modular normal words in one requested
Cartan block, reconstructs their short raw mode-word DAGs exactly, and
checks that each reconstructed raw vector specializes to its stored
split-prime vector. It forms the square matrix at the saved pivot states,
factors it by exact field LU with row swaps, solves each target, and checks
the ENTIRE sparse-vector identity. Every successful relation stores exact
coefficients over Q(sqrt(13),sqrt(-3)) and an exact-zero-residual flag.

The FastField adapter and its independent Fraction-oracle control result
are source-hash-bound. No finite-prime installation is made in this process.
The frozen mode producers and original N4 database remain unchanged.

## Initial bounded pilot

Choose an actual block of modular rank at most 32 or 64 containing at least
one A0P3 target; an outer-weight block such as (2,6) is a candidate, subject
to the completed pilot's actual rank table. Start with `--max-targets 3`.
The default rank gate is 64; no oversized block is silently accepted.

Use AS3GiB, 600 seconds maximum for the first call, and the permanent
launcher. The internal hard alarm includes import and mode reconstruction.
A 1400 MiB candidate/loop-boundary RSS stop remains below the hard address
ceiling. For rank at most 64, expected peak is roughly 0.35--0.65 GiB RSS;
mode cost and exact coefficient growth require measurement. Completion
within 600 seconds is not promised. A stopped process preserves the most
recent committed exact vectors and relation certificates; LU itself is
recomputed on resume.

Explicit allocations and guards:

* Exact inputs and computed raw words are persisted in SQLite. The decoded
  vector LRU has a conservative 128 MiB accounting cap using both term
  count and coefficient height. Each row has at most 12000 terms and
  2048-bit numerator/denominator components. Imported source blocks are
  streamed one row at a time; a whole block's JSON array is never loaded.
* The input database has a 4 MiB page cache; the output database has an
  8 MiB page cache, mmap disabled, and a 512 MiB page limit. The latter can
  also require up to 512 MiB rollback-journal disk. A two-million persisted
  exact-term cap provides an additional stop. No database is copied into RAM.
* There are at most 71052 modular state descriptors, with no ambient basis
  generation. Cache misses temporarily retain one decoded row plus its
  serialized and parsed forms. Each record has a bounded 16 MiB decoder.
* Primitive caches have creation128, vertex256, and basis-action256 entries.
  Both x.creation and e4.creation reference the bounded creation wrapper.
  They are cleared at approximately 20-second checkpoints. Allow roughly
  0.15 GiB for these caches, mode scratch and allocator retention.
* The dense field LU has r-squared entries. At r=64, even the 4096-bit
  matrix-height cap gives only a few tens of MiB for coefficients. The
  supported absolute rank gate is 320, for an explicitly reviewed larger
  call; at that gate the same conservative accounting can approach
  0.5 GiB for LU alone, on top of vectors/caches/serialization. Do not
  launch a large block merely because the command accepts it.
* Every LU row and every forward/backward solution coefficient is checked
  against a 4096-bit cap. This bounds retained coefficient growth; exceeding
  it calls for a different solver or representation, not higher memory caps.
  Full exact target vectors obey the same 2048-bit cap as raw columns.

The root's independently tested FLINT solver can later solve the same
selected pivot matrices using 4r rational coordinates. It is an optional
alternative if direct field LU is slow. Any new consumer must retain the
original raw DAG and source lineage and must still verify each complete
sparse residual; solver success on pivot coordinates alone is insufficient.

## Certificate scope

Output `all_block_targets_verified` refers only to the listed A0P3 targets
in the requested Cartan block. A three-target pilot remains explicitly
partial. A nonzero residual says that the chosen exact column subset did
not contain that target; it is not an exact upper-bound certificate for
the full normal span. No standalone all-weight properness statement is
made by this one-block consumer.

All needed blocks plus the independent exact lower singular checks can
supply the finite recursive strong-generation criterion in
`hi_cft_20260923_next_structure_recursive_strong_certificate.md`.
