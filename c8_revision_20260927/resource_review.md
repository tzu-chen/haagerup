# Resource review for the 27 September manuscript revision

The expired September 15 exception is not used. Root alone runs numerical
work, serially through `hi_cft_safe_run.py`. Subagents only read, reason, and
edit. Every job retains the shared lock, two threads and CPU affinity,
8 GiB group RSS watchdog, and 32 GiB host MemAvailable reserve. The launcher
checks `/proc/meminfo` and all applicable cgroup ancestors before each job.
Initial inspection found about 52.7 GiB MemAvailable and no finite ancestor
memory.max. Swap is not included in any allocation budget.

The frozen source files and old certificates are preserved. Fresh outputs
are written below this directory.

| Job | Peak estimate, including live intermediates | Hard AS | Time boundary |
|---|---|---|---|
| Original provenance replay | <0.1 GiB; streaming hashes, capped JSON | 1 GiB | Internal 180 seconds |
| Supplemented input ledger | <0.128 GiB; capped JSON, 1 MiB hash buffer | 1 GiB | Internal 180 seconds |
| Minimal generation | <0.15 GiB; 120 sparse grade-two basis vectors and bounded mode caches | 2 GiB | Internal 180 seconds |
| Grade-two unitary/OPE replay | <0.2 GiB; 120-vector span, 96 primary states, bounded 12,000-entry mode caches, one OPE residual | 2 GiB | Internal 600 seconds |
| Exact grade-three replay | <0.8 GiB; at most 1,600 retained sparse vectors, one reduction target, exact coefficient copies, bounded creation/vertex/mode caches; prior same-source peak 0.19 GiB | 2 GiB | Internal 600 seconds |
| Final Gate 4 replay | 0.2–0.6 GiB; streamed projected residual, bounded 16/32 MiB caches, 322-coordinate rank matrices | 2 GiB | Internal 240 seconds |
| Charged-span replay | <0.3 GiB; four sparse 322-coordinate matrices, one decoded record | 2 GiB | Internal 180 seconds |
| Gate 5 replay | 0.15–0.35 GiB; capped grade-two rows and eight exact quotient combinations | 2 GiB | Internal 180 seconds |
| Narrow Lean module | <2.5 GiB; compiler/import artifacts, no research arrays | 6 GiB | Foreground check, monitored launcher |
| TeX build | <0.3 GiB; text-only document, ordinary fonts, no external programs | 1.5 GiB | Foreground build |
| PDF rendering | <0.3 GiB per page at 90 dpi, serial page selection | 1 GiB | Foreground rendering |
| Final document audit | <0.1 GiB; source strings, small JSON, one pdfinfo child | 0.5 GiB | Foreground check |
| Archive creation and integrity check | <0.064 GiB; streamed ZIP members/hashes, at most 32 MiB of inputs per archive | 0.5 GiB | Outer 60-second timeout |

No dense transfer tensor, sparse Hamiltonian assembly, eigensolver,
optimization workspace, multiprocessing worker, or detached job is used.
The grade-three script was inspected along with the in-place reduction and
cache allocators in its imported exact engine; its 1,600-vector cap and
2 GiB address cap remain active. There is no justification for increasing
the permanent ceilings.

The first Gate-5 replay rejected a verified charged-span summary because
its CLI requires the producer schema. It was rerun against the authenticated
producer; the independent verifier is retained as a separate replay.
The first Lean check needed a missing narrow Field import. The first
supplemented-ledger check rejected the relative launcher spelling; its
parent validation now resolves that spelling against the actual parent
working directory. No resource limit was relaxed for these corrections.

Additional structural replays were reviewed before launch. The core-extension
job retains the 120-vector S2 basis, at most twelve vectors per Cartan block,
one kernel reduction target, and bounded 12,000-entry mode caches: peak
estimate <0.5 GiB, hard AS 2 GiB, internal 280-second alarm and 300-second
outer timeout. The four mixed-top job retains only sparse operators on 81
root states, at most81 reduction rows, 2048-entry coordinate/gauge caches,
and bounded 2048-bit coefficients: peak estimate <0.5 GiB, hard AS2 GiB,
internal280-second alarm and outer300-second timeout. Both run serially
with the same guard. Exit status is supplemented by semantic completion
checks, since the top producer can write a bounded-stop summary.

The Potts and PF13-membership producers have hardcoded output paths. The
reviewed `replay_structural_input.py` adapter changes only the producer's
module-local Path constructor for that one output. It authenticates the
frozen producer and original JSON, requires exactly one intercepted write,
compares the entire mathematical output with the original (excluding time
and RSS), and installs a new file exclusively. Root inspected the adapter
and both producer bodies before running it. The workloads use at most120
S2 inputs, sparse Cartan-zero S3 reductions, bounded mode caches, and small
library initialization; estimated peak <0.75GiB, AS2GiB, outer600seconds.
The membership producer's internal900second alarm is superseded by that
shorter foreground outer timeout. The full host/thread/group guard remains.


## Observed successful results

All twelve requested arithmetic/provenance replays passed their stated
checks; all computations were serialized. The main sampled RSS results
were 0.190 GiB for the 493-second exact grade-three construction,
0.039 GiB for the 6.45-second core spectral calculation, 0.026 GiB for
all four mixed tops in 3.03 seconds, 0.095 GiB for Potts in 8.23 seconds,
and 0.117 GiB for PF13 membership/stress in 180.62 seconds. Both Lean
modules passed; the larger sampled peak was 1.652 GiB. The final TeX
build used about 0.035 GiB and serial page renders used about 0.037 GiB.
No guard limit or host reserve was relaxed. All launches reported over
52 GiB host MemAvailable. The final build has 55 pages and no unresolved
references, duplicate labels, missing glyphs or overfull/underfull boxes.

The final source-binding ledger is a small streaming provenance check,
with the same reviewed 1 GiB address / 256 MiB RSS boundary. It authenticates
11 semantic replay kinds and binds the independent top-bound arithmetic
output and formalization/document artifacts explicitly as hash-only inputs.
