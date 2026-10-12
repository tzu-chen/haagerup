# Two-hour proof attempt, 23 September 2026

Window: 02:29:16–04:29:16 UTC. The target is to prove that the explicit
subalgebra from the preceding construction is a Haagerup realization.
No identification or rationality assumption is used as a theorem.

The permanent resource policy applies. The September 15 exception has
expired. Every numerical or exact research calculation runs through
`hi_cft_safe_run.py`, with one job, two threads/CPUs, the 32 GiB host
reserve and the process-group watchdog. Initial host MemAvailable was
about 46 GiB. The launcher also checks cgroup headroom on every run.

The first calculation concerns the 86-dimensional ambient current space.
Sparse exact mode actions and Cartan-weight Gaussian elimination use
less than 0.3 GiB estimated RSS, including coefficient growth and bounded
mode caches. The address cap is 2 GiB and the per-job alarm 600 seconds.
For numerical weight-two branching, dense frames are at most 1370 square
(30 MiB complex), with streamed mode matrices and solver copies; allow
0.8 GiB RSS under the same 2 GiB cap. No full three-index tensor is formed.

Higher-grade computations require a further allocation estimate below
before launching. Files from the preceding window remain unchanged.

Weight four review: the ambient space has expected dimension 71052
(726 zero-momentum oscillators, 78*192 root states, 702*44 norm-four
states, 2346*8 norm-six states, 5694 norm-eight states). Refuse above
72000. Work in joint Cartan blocks, stream images from the saved
weight-three blocks, and cap the generated rank at 7000. Retain at most
three sparse generator matrices, never a dense ambient-square matrix or
an ambient-by-6010 frame. Budget 1.5 GiB RSS including at most 10000
cached vertex actions, sparse assembly lists/copies, block frames and QR
workspaces. Use a 3 GiB address cap (below the permanent 6 GiB ceiling),
the normal watchdog/reserve, and a 900-second alarm. Record actual peak
RSS and do not enlarge the caps if the estimate fails.

Higher individual OPEs (through target weight six): no ambient basis or
multi-field closure frame is allocated. Use sparse exact states with a
250000-term output cap, a 256-entry vertex cache and 128-entry recursive
mode cache. Estimate up to 1.2 GiB RSS including number-field coefficient
growth, creation-series caches and simultaneously live fields; enforce
2 GiB address space and a 900-second per-producer alarm. Persist each
completed field before the next calculation. A refusal or timeout is an
incomplete certificate, never evidence for a vanishing relation.

Weight-seven extension of the individual-OPE review: retain the saved
7352-term W5, a predicted 25000–40000-term W6, and at most 250000
terms in the streamed weight-seven product. Estimate 1.5 GiB RSS,
including exact coefficient copies, seven weight-six comparison fields
and the same bounded caches. Keep the 2 GiB address cap. The producer
has a 1800-second alarm and is launched with more than 40 minutes left
in the user window; do not start another numerical job concurrently.

Final first-row comparison: once the weight-seven producer exits, run
the exact upper-pole checks with target weights at most five, reusing
the stored W4 and W5. Estimate 0.4 GiB RSS with the bounded recursive
caches, 2 GiB address cap and 600-second alarm. The separate DLY
normalization comparison manipulates only a few dozen rational
coefficients and existing JSON metadata (<0.1 GiB); it too runs under
the launcher, sequentially. No other numerical job runs concurrently.

The final remaining-coset diagnostic uses two sparse weight-two fields,
one 342-term primary and existing 1370-by-7 and 1370-by-4 frames.
Target grade at most four, estimated RSS below 0.4 GiB, address cap
2 GiB, alarm 180 seconds. The upper-pole continuation, if needed,
reuses completed exact assertion records from the unchanged producer
and its log; only the final target-weight-five product is recomputed,
under the same memory estimate and a fresh 600-second cap within the
research deadline. Artifact auditing uses a 256 MiB address cap and
reads JSON files one at a time.

The last two-axis recognition reuses the same seven-dimensional
Griess data and checks sparse modes through weight three. It uses
no new ambient basis, estimated RSS below 0.4 GiB, a 2 GiB address
cap and a 120-second alarm. No weight-three kernel search or further
parafermion identification is included in this last diagnostic.
