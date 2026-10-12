This directory vendors the extraction core of
[Pierre Senellart's result-graph](https://github.com/PierreSenellart/result-graph),
commit `e62387eb62ceedc68dbe3cb79c8974191a6218df` (Apache-2.0).
`ResultGraph/Basic.lean` is unchanged. The license is in
`LICENSE.result-graph`.

Local changes to `ResultGraph/Extract.lean`:

- When both `includePrivate` and `includeAuto` are set, keep internal declarations
  as well as named compiler companions; skip contraction in this exhaustive mode.
- Preserve recursive self references.
- Limit custom-axiom classification to the extraction scope. Under Lean 4.33's
  module system, exported library theorems can appear as `axiomInfo` when their
  private proofs are not loaded. The separate `#print axioms` audit is authoritative.

`Main.lean` supplies the module-aware, read-only extraction entry point. It uses
Lean's `Expr.getUsedConstants` on each declaration's type and body, through
result-graph's `usedConstants`, with its declaration enumeration and module
classification helpers. It streams JSON records to disk instead of accumulating
the graph and its library-boundary references in Lean. It records external
references and refuses unresolved constants, project axioms, or sorry terms.
It does not execute project initializers or modify the formalization.

The driver compiles these two upstream modules and the entry point with the
project's pinned toolchain, then extracts **one project module per process**.
It uses the existing Lake module setup to load the current module's private proofs
and the required public dependencies. The union of these dumps restores all
cross-module project arrows before taking the target's complete backward closure.
Mathlib and Lean references are recorded at the boundary and are not traversed.

This streaming design is necessary on the shared desktop: importing all private
project modules together exceeded the fixed 6 GiB address-space limit, even with
a native executable. Per-module extraction is sequential and checkpointed.
The native tool shares Lean's runtime so that the existing small-stack helper
applies. Graph assembly, slicing, and layout take place in Python after the Lean
process exits. No cap is raised. JSON checkpoint fingerprints include the extractor, all project
source and elaborated-artifact hashes, and the Lean and dependency pins; a change
invalidates the extraction cache.

From the repository root:

```sh
python lean/docs/build_dependency_graph.py
```

The driver automatically enters `~/.local/bin/research-safe-run`. All compilation, extraction,
and rendering run sequentially under its 6 GiB address cap, 8 GiB process-group RSS
watchdog, 32 GiB host reserve, and two-CPU/thread limits. It requires cached,
up-to-date project artifacts and refuses to build project prerequisites.

Intermediate data and native objects live in `lean/.lake/dependency-graph/`.
After extraction, rendering can be repeated without running Lean:

```sh
python lean/docs/build_dependency_graph.py --from-cache
```

The renderer uses a deterministic layout whose memory is proportional to the
graph and source text, rather than Graphviz's crossing-minimization layout.
The generated DOT can still be consumed by Graphviz or another graph viewer.
The HTML works offline and draws only in response to user interaction.
