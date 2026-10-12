# Haagerup research instructions

## Canonical machine policy

The persistent machine policy is
[/home/tzuchen/.codex/AGENTS.md](/home/tzuchen/.codex/AGENTS.md).
Read and follow it before research work and communicate it to subagents.
It is the source of truth for resource limits, reservations, concurrency,
and CPU allocation; do not duplicate numerical caps in project policy.

Only the central `~/.local/bin/research-safe-run` may admit numerical jobs.
Run it from the calculation's project directory. Root coordinates all
admission across this task's agents and respects other repositories' jobs.
If the guard is unavailable or cannot enforce a required control, do not
compute: repair it or continue read-only work. No independent fallback.

The primary lock is `/tmp/research_numerical.lock`. Its compatibility
aliases, including `/tmp/haagerup_numerical.lock`, must name the same inode.
Preserve the central guard's coordination locks; never unlink or replace
a potentially held lock or bypass an older exclusive launcher.

## Allocation and provenance

The local `hi_cft_safe_run.py` only forwards old commands and helper
imports to the global guard. Do not restore a separate local policy.
Historical window launchers and larger-memory authorizations are expired;
they do not authorize current jobs.

Audit the actual execution path, including in-place calls, workspace
allocators, temporary copies and simultaneous allocations. The old MPS
optimizer hid a workspace of about 468 D^4 complex doubles, requiring
47.18 GiB at D=51 before other live arrays. Never return to that path
without a new allocation review. Reuse checkpoints and prefer streaming,
reduced symmetry bases, matrix-free operations and analytical work.

The exact previous launcher-related sources are retained as provenance
text under `resource_guard_history/`. Historical execution records and
source hashes must not be silently rewritten or exempted from validation.
A continuation must explicitly distinguish archived historical sources
from the current shim and global guard, and record current guard hashes.
Scientific source changes require their own review; infrastructure
migration is not permission to ignore them. New bundles containing the
shim require the global guard installation.
