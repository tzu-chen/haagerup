# Final Gate4 combination resource review

Root-only serial research job. Use the unchanged safe launcher with 2048 MiB
address space and an outer 260-second foreground timeout; the verifier has a
240-second alarm. The guard enforces the normal host-memory reserve, group RSS
watchdog, two-thread/two-CPU limit and shared lock. No native solve or lattice
mode computation runs here.

The verifier authenticates the source graphs and the 2145 original and 118
additional exact records. The twelve projected targets have at most 5000 terms,
2048-bit vector coefficients and 4096-bit relation coefficients. Live retained
vector and integer-column caches are capped at 16 MiB and 32 MiB respectively.
Compressed records are bounded by the frozen decoder; individual source JSON
files are at most 32 MiB and SQLite connections use 2 MiB caches without mmap.
Only one projected residual is computed at a time. The 322-dimensional sparse
raising matrices and nine sequential rank checks use ordinary Python integers.
There are no workers and no nested solve. Estimated peak RSS is 0.2–0.6 GiB;
an internal boundary refuses above 768 MiB, with the 2 GiB hard address limit
covering allocations between boundaries. This stays below all permanent caps.

The proof scope is Gate4 only: exact raised controls show each unresolved class
is killed by both raising currents modulo the full current-stable W4. The joint
FE projector is therefore identity on each such class. Full projected residuals
are independently recomputed with the integer engine, recovering twelve raw
memberships. The final raising/Nakayama calculation covers all 2898 identities.
Gate5 and the finite strong-generation implication remain separate deductions.

The output retains the audited H4 raising-certificate schema consumed by the
frozen Jacobi checker, and records the singlet derivation method explicitly.
