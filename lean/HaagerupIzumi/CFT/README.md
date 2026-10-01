# Limited formalizations for the c=8 manuscript

Checked on 27 September 2026 with Lean 4.33.1 and Mathlib 4.33.1.
These files are independent of the repository’s analytic Evans–Gannon
existence development and are not added to its umbrella import.

| File | Kernel-checked conclusion | Explicit mathematical inputs |
|---|---|---|
| `FiniteClosure.lean` | A stable submodule containing representatives modulo two jointly nilpotent operators is the whole module | Stability, a spanning equation for every vector, and vanishing of every operator word of a fixed length |
| `FiniteClosure.lean` | Recovery from a projected residual; nonzero-scalar cancellation in a Jacobi witness | The corresponding normal-submodule memberships and linear identity |
| `TopBound.lean` | The fourteen-variable deficit identity and the cleared 17/10 inequality | Nonnegative multiplicities, the two current-character inequalities, and the printed dimension/trace coefficient definitions |

Run serially from the repository root:

```sh
python lean/safe_lean.py lean/HaagerupIzumi/CFT/FiniteClosure.lean
python lean/safe_lean.py lean/HaagerupIzumi/CFT/TopBound.lean
```

The driver applies the permanent shared-desktop resource guard: 6 GiB
address limit, 8 GiB process-group RSS watchdog, at least 32 GiB host
MemAvailable, at most two threads, CPU affinity, and one numerical job.
The final checks passed, with sampled peak group RSS of 1.54 and 1.652 GiB.
Logs are in `c8_revision_20260927/lean_finite_closure_final.log` and
`c8_revision_20260927/lean_top_bound.log`.

No `sorry` or new axioms are used. The printed axiom reports contain only
`propext`, `Quot.sound`, and, where applicable, `Classical.choice`.

These files do not formalize vertex algebras, the lattice engine, the
filtered Wick argument, the embedded Potts/parafermion construction,
the top-space identification, conformal nets, or the annulus comparison.
The independent exact-rational script
`c8_revision_20260927/check_top_bound.py` reconstructs the fourteen rows
from the manuscript’s charge formulas; it is a separate arithmetic check,
not a Lean proof of the underlying VOA embedding.
