# Bounded raising-coinvariant certificate: resource review

Root is the sole launcher. Use `hi_cft_safe_run.py`, one foreground
process, at most two CPUs/threads, no workers, permanent host reserve
32 GiB. This producer additionally requires address space at most 3 GiB,
a 1 GiB RSS boundary, and a 300-second default / 900-second maximum alarm.
No job was run while preparing this source.

The frozen lower certificate previously loaded 224,480 sparse terms with
approximately 0.229 GiB peak RSS. This producer loads only grade three
from that same source, with a 300,000-term cap. It retains at most two
20,000-term current-mode vectors at a time, current/basis caches of
128/256/512 entries, and the exact quotient coordinate rows. Raising
requires 644 current-zero calls, not any grade-four or grade-five mode.

The quotient has 322 coordinates, with at most 64 in any Cartan block.
Each echelon row and raising image is confined to one such block.
Coefficient height is capped at 4,096 bits. There is one raising-image
echelon basis and one operator's augmented copy, reused serially for all
nine fields; there are no nine simultaneous dense systems. All linear
algebra is sparse and there is no native dense solver or native workspace.

The retained compact raising records are capped at 12 MiB before appending
them. Final JSON is capped at 32 MiB; writes are atomic. Each authenticated
H4 record has bounded 16 MiB decompression and only one database/record is
open at a time. Hashing streams 1 MiB chunks and memoizes hashes rather
than file contents. Each H4 database is at most 512 MiB and at most 100
such files are accepted. They are read-only, immutable, and must have no
active writer; root has confirmed the original H4 directory remains closed.

Expected peak is below 0.7 GiB with the measured input coefficient sizes;
the 1 GiB boundary and 3 GiB address cap handle exceptional growth without
raising the permanent ceilings. Stop and retain the bounded partial
output if the exact coefficient cap or time boundary is reached. A prime
pilot is available under the same caps but a nonzero prime deficit is
not reported as an exact deficit.
