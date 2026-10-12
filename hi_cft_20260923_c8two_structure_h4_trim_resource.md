# Targeted H4 cache trimming before native solves

The first targeted run closed after 602 seconds with 77 of 130 identities
passed. Its sampled peak was 1.542 GiB during a native solve, exceeding the
forecast and the Python 1,400 MiB review boundary while remaining under the
enforced 3 GiB address limit. This new wrapper reduces simultaneous liveness;
it does not raise any cap or change the frozen first-run files.

The new wrapper `hi_cft_20260923_c8two_structure_h4_trim_v2.py` copies only a
closed targeted directory into a fresh destination. Copies use 1 MiB chunks,
with streamed digests checked against the closed ancestor's authenticated
file hashes. A separate lineage authenticates the new wrapper and the entire
old snapshot. The original targeted policy is preserved exactly, including
its batch size and all existing relation records. Every resumed block gains
the new lineage in its metadata, visible to the recursive Gate 4 verifier.

Only the native solve entry point is wrapped. Once the unchanged caller has
constructed the matrix, right-hand sides and exact targets, the wrapper drops
the reconstructible 192 MiB whole-action cache, 128 MiB raw-vector LRU and
64 MiB integer-column LRU, resets their accounting, clears primitive mode
caches, and calls Python garbage collection. Matrix, RHS, targets, immutable
input fields and disk certificates are retained. The same frozen FLINT solve
and complete integer residual then run. A cache miss reconstructs data using
the same authenticated sources and original arithmetic.

At most 384 MiB of estimated retained cache payload is removed before a solve;
the actual reduction depends on occupancy and allocator retention. Expected
peak is below the prior 1.542 GiB measurement and ideally below 1.4 GiB, but
this is not a guarantee. The unchanged 512 MiB native allocation preflight,
1,400 MiB Python high-water boundary, 3 GiB hard address limit and external
timeout remain mandatory. A new excessive peak requires another redesign,
not higher limits. No allocator-specific ctypes call is introduced.

Root alone may run the continuation, serially through the safe launcher,
with at most two CPUs/threads and at least 32 GiB host MemAvailable. Suggested
first continuation is 600 seconds plus an external 620-second timeout. All
work by this implementing agent was reading, editing and syntax compilation.
The import stage has its own Python alarm; the frozen main routine resets
that alarm for computation. The mandatory external timeout therefore bounds
the combined copy and compute interval.
