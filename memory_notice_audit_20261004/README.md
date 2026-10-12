# Memory-notification audit, 4 October 2026

The repeated **“Memory Shortage Avoided”** notices correspond to real,
contained Lean compilation failures on 4 October. They do not establish
that the desktop exhausted its RAM. They did not occur during the earlier
six-hour cubic continuation. The queue behavior that produced the repeated
failures has been corrected; desktop OOM notifications remain enabled.

## Evidence and timing

The cubic window was 2 October 23:20:35 through 3 October 05:20:35 UTC
(2 October 18:20:35 through 3 October 00:20:35 Chicago time). Accessible
journals contain 43,464 records in that interval, including 56 kernel
records. No kernel OOM kill, memory-pressure service event, or memory
watchdog stop was found in that window.

The burst of 315 kernel kills occurred on **4 October 17:00:04–21:37:26 UTC**,
or **noon–4:37 p.m. CDT**. All 315 kernel cgroup names matched systemd
unit-start commands invoking this repository's `lean/safe_lean.py` on C8
lattice, lattice-export, or Theta files. All were separate
`research-guard-*.scope` units and logged a failed `oom-kill` result.

| Per-job cgroup cap | OOM kills |
| --- | ---: |
| 640 MiB | 301 |
| 821 MiB | 1 |
| 2,048 MiB | 10 |
| 4,096 MiB | 3 |

There were 305 distinct source files, 302 build attempts and 13 direct
checks. Every job had a separate 6-GiB virtual-address cap and disabled
cgroup swap. The kernel classified all events as `CONSTRAINT_MEMCG`.
There was no recorded global OOM in this burst. This identifies exhaustion
of each job's imposed cap; it does not provide a continuous host-RAM trace.
The kernel's [cgroup documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html#memory)
explains that `memory.max` can trigger an OOM kill inside the constrained
group without killing processes outside it.

The cumulative user-cgroup counter was 324 OOM kills at inspection. All
324 were matched to dated kernel records: nine before the cubic window
and 315 in the later burst. The cumulative counter alone was not used
to attribute events to a particular window. See [kernel evidence](kernel_evidence.txt).

The installed KDE plugin
`/usr/lib64/qt6/plugins/kf6/kded/oom_notifier.so` contains the exact notice
title and the generic “system is low on memory” wording. Its notification
definition is `/usr/share/knotifications6/oom_notifier.notifyrc`, event
`catastrophe`, with critical urgency and popup/sound actions. The wording
does not distinguish the per-job cap seen here from whole-machine OOM.
No notification setting, kernel memory setting, guard cap, or swap
configuration was changed during this audit.

## Cause in the C8 queue

The preserved [previous queue](before/c8q.py) shows three contributing behaviors:

1. An unseen file received 640 MiB automatically. The separately defined
   `C8Q_MEMORY_MIB` default of 3,584 MiB was not used by that estimator.
2. A detected memory failure automatically requeued the job with a larger
   cap, up to 4,096 MiB, without a new allocation/design review. Bulk
   `--keep-going` builds could continue after resource failures.
3. A retry reopened the same log with `w`, overwriting the earlier attempt.

These were ordinary theorem compilations, not intentional OOM tests.
For example, retained request `120201-eb9552` for `Lattice/S2Rel00.lean`
records one requeue and eventual success at a 2,048-MiB reservation, with
686.6 MiB sampled charged memory—above the original 640-MiB guess.
Request `120221-5200f3` for `S2Pivots` records two requeues and a final
`std::bad_alloc` at 4,096 MiB. Attempt counters can include capacity waits;
the 315-kill count comes from the kernel, not those counters.

## Corrected behavior

- Every queued compilation requires a reviewed `--memory-mib` estimate,
  or an explicitly configured `C8Q_MEMORY_MIB`. Failed or sampled history
  does not silently authorize another budget.
- A resource failure stops new admission and writes `MEMORY_STOP.json`.
  Restarting the runner cannot silently clear that record. Already-active
  independent jobs may finish; pending jobs are not admitted.
- Memory failures are not retried automatically. The root must inspect
  the actual allocation path and revise the design/estimate before
  preserving and clearing the stop record and deliberately resuming.
- Only pre-execution capacity refusals may requeue. Every attempt has a
  separate log, and earlier logs remain intact.
- Bulk `--keep-going` applies to ordinary proof errors, not resource stops.
  A batch with failed modules also returns failure instead of exit zero.

The central guard is unchanged, SHA-256
`09b9986966402a73bba8e078884a50b5762c4980485ea295e8cca2e02fc8ae63`.
The live queue was already stopped, with no pending/running requests.
This audit did not start, terminate, or resume any Lean job. Previous
uncommitted versions are preserved in `before/`; scientific Lean sources
and the sealed cubic archives are unchanged.

## Separate small failures in the cubic window

The [cubic resource review](../cubic_phase_research_20261002/resource_review.md)
records four Python `MemoryError` attempts under a 256-MiB address-space
cap. One interval calculation was redesigned to stream; three startup
failures were traced to an approximately 223-MiB locale-archive mapping
and resolved with the C locale and Python UTF-8 mode. The successful
imports used 35,180 KiB virtual size, and the complete Cauchy diagnostic
passed at 16.4 MiB sampled charged memory. No cap was raised.

There were also 31 routine wait notices across 29 logs, three slot-occupied
refusals, and one sandbox/systemd connection refusal. These did not run
out of host memory and do not contain KDE's displayed wording. Short-run
sampled peaks of zero are not claims of zero actual usage.

## Validation

The queue and bulk-build changes are checked using mocked child processes
and temporary queues, without Lean or deliberately exhausting memory.
The standard-library test path has no scientific imports or worker pool;
estimated peak is below 64 MiB. Root admission uses the unchanged shared
guard with 256-MiB address-space and cgroup caps and one CPU/thread.
All **11 mock tests passed**, in 0.040 seconds, with guard exit zero;
see [the retained test log](mock_tests_guard.log). The sampled peak was
0.0 MiB because this short run fell between watchdog samples, not because
the tests used no memory. Both source paths and their mock tests also
passed independent read-only review. The tests do not establish that an
arbitrarily selected future Lean budget is sufficient.

The cubic source archive's existing SHA-256 sidecar still verifies.
The live C8 queue's original STOP marker, empty pending/running directories,
and the global guard's source hash were unchanged after validation.

Final queue source SHA-256:
`048df4fb44e17c6e600a24c81f96fa40b70fc587c3ed04759b71d7993fb93c7b`.
Final bulk-build driver SHA-256:
`26abee615dfa6a1fde257890376560c8e7e750a9f4179f54a1c5fff35ba4a910`.
