# Physics dataset resource review

Root coordinates every numerical job, serially through the permanent
`hi_cft_safe_run.py`. The expired September 15 exception is unused.
All launches inspect actual host and cgroup memory through that launcher,
retain at least 32 GiB host MemAvailable, enforce two CPUs/threads and
the 8 GiB process-group RSS watchdog. No worker pools or detached jobs.

| Work | Allocation review | Address cap | Time cap |
|---|---|---|---|
| Grade-two primary coupling table | 96 sparse fields, eight highest fields, one mode product at a time; grade at most two; original basis/vertex caches reduced to 6,000/4,000 entries, creation cache512. Input JSON<1MiB, stored fields<20,000 terms, output products streamed; individual product<2,000 terms. Expected<0.3GiB; internal RSS refusal512MiB. No dense ambient tensor. | 1GiB | 900s |
| Exact characters and spectrum | Fixed 12-dimensional recurrence and at most64 coefficient grades; sparse spectrum tables; no numerical linear algebra or mode engine. Expected<0.125GiB, pending source review. | 512MiB | 300s |
| Exact defect and fusion data | Fixed12x12 cyclotomic matrices and1728 Verlinde entries, small integer fusion and annulus tables. Expected<0.15GiB, pending source review. | 1GiB | 300s |
| Correlators and conformal blocks | At most81 exponential assignments, rational power series and bounded global-block order; no large lattice basis. Expected<0.1GiB, pending source review. | 512MiB | 120s |
| Complete96-primary coupling tensor | Current Ward recurrence on at most96 cubed exact coefficients, sparse pair maps; streamed nonzero table;24 extra grade-two lattice probes. Expected<0.2GiB; no higher lattice grades. | 1GiB | 300s |
| Full113-primary seeds and tensor | Add17 actual current/stress primaries to96-field basis,13highest-first slices; at most113 cubed sparse exact coefficients. Same grade-two mode and cache caps, at most24,000 input terms. Expected<0.3GiB; seed RSS refusal512MiB. | 1GiB | 900s seeds;300s completion |
| TeX builds | Ordinary fonts, text/tables and vector PDF figures, no shell escape. Expected<0.3GiB. | 1.5GiB | 120s/pass |
| Plotting / page rendering | Small exported tables; matplotlib at two threads, or one rendered page at a time; expected<0.5GiB. | 1GiB | 120s |
| PhysicsBounds Lean elaboration | Two real inequalities, narrow Mathlib imports; no project-wide build. Existing safe_lean wrapper launches the permanent guard and pinned two-thread Lean toolchain. Expected peak<2.5GiB from prior comparable imports. | 6GiB permanent maximum | 180s |
| Fresh release replay and archive | Copy<150MiB of files, hash in64KiB chunks, run six already reviewed producers sequentially as guarded children; no simultaneous children. Peak expected<0.3GiB; compressed archive streamed. | 1GiB | 1200s replay;120s archive |
| Companion anchor audit | Parse small TeX/AUX files and Poppler destination/link text; no arithmetic producers, large arrays, or worker pools. Expected<0.1GiB. Rebuild companions and the extracted three-document bundle serially using the TeX profile above. | 512MiB audit;1.5GiB builds | 120s audit;180s extracted builds |

Every additional computation receives a review before execution. Reports
separate exact identities from floating evaluations and construction
assumptions. Earlier frozen certificates and revision archives are preserved.
