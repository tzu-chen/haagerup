# Skipping the invariant descendant block in the N4 pilot

The frozen producer's first stage spans D=K(-1)S3+T S3. The saved exact
S3 checkpoint has completed both current-lowering queues: its metadata
records `closed_lower3=dimensions[3]=956`. Let f be either lowering current.
Then

    f_0(k_{-1}s)=(f_0 k)_{-1}s+k_{-1}(f_0 s),
    f_0(Ts)=T(f_0s).

The current Lie algebra K is stable under f_0, and the exact saved S3 is
stable under f_0. Consequently f_0D is contained in D. This uses only the
two lowering currents actually used by the producer; no extra assertion
about raising-current verification is needed for this skip.

The frozen exact echelon rows have unit pivots and their denominators are
checked to be nonzero at the chosen split prime. Exact membership reduces
using these unit pivots. Thus the identities also specialize to the same
prime as the pilot. Every lowering candidate whose source is one of the
independent first-stage raw descendants is redundant in the modular span.

The new wrapper `hi_cft_20260923_next_n4_strong_skip_v2.py` reads the completed
first-stage rank from the original SQLite history, checks that each row in
that initial interval has a raw descendant recipe, and raises the lowering
cursor to twice that rank if necessary. It copies the closed original
database into a new database; the original producer and database are not
modified. The new metadata records the old database SHA256, old source
hashes, before/after cursor, exact premise, this note, and new wrapper hash.

All finite-field arithmetic, row/cache/disk caps, 768 MiB candidate-boundary
RSS stop, 3 GiB address cap and 600-second default hard alarm are inherited
unchanged. The streaming SQLite backup adds two small page caches and disk
I/O, not an in-memory database copy. Allow at most another 512 MiB disk for
the new main file and 512 MiB for its rollback journal. Expected peak remains
approximately 0.5--0.75 GiB RSS. Root alone may launch it under the permanent
safe launcher. No execution was performed by the author.
