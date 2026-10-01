# Brief for agents formalizing the c=8 proof (started 2026-09-30)

Project: Lean 4 `v4.33.1` + Mathlib (pinned commit `0df444a3`) in
`/home/tzuchen/Codes/haagerup/lean`, package `HaagerupIzumi`.  The new c=8
formalization lives in `lean/HaagerupIzumi/C8/`, namespace `HaagerupIzumi.C8`.

Mathematical source: the expanded draft
`/home/tzuchen/Codes/haagerup/c8_expanded_20260929/haagerup_c8_expanded.tex`
(appendix line numbers below refer to this file).  The formalization
assessment (what is foundational vs. focused) is
`c8_expanded_20260929/lean_scope.tex`.  Earlier limited Lean files:
`lean/HaagerupIzumi/CFT/{FiniteClosure,TopBound,PhysicsBounds}.lean`.

| Manuscript part | Lines |
|---|---|
| A. Lattice construction, currents, field `u`, initial spaces | 1872–2092 |
| B. Filtered Wick lemma, recursive strong-generation criterion | 2093–2266 |
| C. Gate 4, bootstrap lemma | 2268–2428 |
| D. Gate 5 (Jacobi), E. properness | 2430–2624 |
| F. Regularity (positive stress, C2, projective vacuum, rationality) | 2629–3035 |
| G. Branching, rank 4/6 fork, near-group exclusion, rank-6 ring, twists | 3037–4134 |
| H. Character vector | 4136–4211 |
| I. Analytic comparison (A1–A3), complete unitarity | 4217–4895 |
| J. Unitary categorical identification, K. full theories / E8 extension | 4897–5203 |

## File conventions

Every Lean file starts exactly like `lean/HaagerupIzumi/CFT/FiniteClosure.lean`:

```lean
module

public import Mathlib.Foo
public import HaagerupIzumi.C8.Bar

@[expose] public section

/-! # Title
Docstring: what is proved, which manuscript statement (label + line), and
which hypotheses are external theorems or certificate inputs. -/

namespace HaagerupIzumi.C8
...
end HaagerupIzumi.C8
```

End each file with `#print axioms` for its main theorems.  The shared
vertex-algebra interface is `HaagerupIzumi/C8/VertexAlgebra/Basic.lean`
(structure `VertexAlgebra`, `VertexOperatorAlgebra`, `normalSpan`,
`generated`, `IsSubalgebra`).  Do not change its existing fields or
names; derived lemmas go in new files.

## Hard rules

* No `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe`.  Kernel `decide`
  is allowed on small instances.  `set_option maxHeartbeats` up to 1000000 is
  fine where needed.
* External theorems (Zhu, Huang, McRae, Etingof–Penneys, Larson, DLN, GSY,
  Izumi, Henriques–Tener, ...) and finite certificate facts (identities
  computed by the lattice engine) enter only as **explicit hypotheses** of a
  theorem, phrased as the mathematical statement actually cited, never as the
  conclusion being proved.  Name them descriptively and list them in the
  docstring.  An interface whose fields restate the desired conclusion is not
  acceptable.
* Edit only the files you own (see your task).  Do not edit `lakefile.toml`,
  the umbrella `HaagerupIzumi.lean`, other agents' files, or anything outside
  `lean/HaagerupIzumi/C8/`.  Do not commit to git.

## Compiling: mandatory resource policy

This is a shared desktop with a hard machine policy
(`/home/tzuchen/.codex/AGENTS.md`).  **You must not run `lake`, `lean`,
`lake env lean`, `python lean/safe_lean.py`, `research-safe-run`, or any other
numerical job yourself.**  The root agent runs a compile queue that admits
jobs through the central resource guard.  Use only:

```sh
cd /home/tzuchen/Codes/haagerup
python3 lean/tools/c8q.py check lean/HaagerupIzumi/C8/Path/File.lean   # elaborate only
python3 lean/tools/c8q.py build lean/HaagerupIzumi/C8/Path/File.lean   # write .olean for importers
python3 lean/tools/c8q.py wait <id>                                     # keep waiting
python3 lean/tools/c8q.py status                                        # queue state
```

Use a Bash timeout of 600000 ms.  A request blocks up to 540 s; if it prints
"not finished", call `wait <id>`.  `build` requires every imported project
module to be built already; build your own files in dependency order before
checking files that import them.  There is a single compile slot shared by
about six agents and other research sessions, so a request can queue for many
minutes.  Write carefully, look up Mathlib names with `grep` in
`lean/.lake/packages/mathlib/Mathlib` instead of guessing, fix all errors of a
run at once, and never have two pending requests for the same file.  Small
experimental files are cheaper than large ones.  Reading files, `grep`, and
tiny `python3` string scripts are fine.

## Lean tips from this project

`π` needs `open Real`.  `ring` cannot use `I^2 = -1`; `field_simp` needs
`≠ 0` facts in context.  `linear_combination` coefficients can be read off a
residual goal.  For finite checks prefer `decide` on `ZMod`/`Fin`/`ℕ`, and
`norm_num` on `ℚ`/`ℝ`.  `Finset.sum_range_succ` unfolds small sums.  Keep cast
forms consistent (`push_cast`).

Two pitfalls found by root (21:30):
* `decide` gets stuck on `ℚ` arithmetic (`Rat` normalization uses well-founded `gcd` at
  elaboration time).  Use `decide +kernel` (kernel reduction; no extra axioms) for
  computations with `ℚ` literals; it is fast.  Avoid `List.mergeSort` and other
  well-founded definitions inside `decide`.
* `(List.range n).map fun i => (i : ℤ) - c` elaborates `i : ℤ` and inserts a monadic
  coercion of the list; write `fun i : ℕ => (i : ℤ) - c`.

## Final report (your last message)

1. Files written and their compile status (the last `c8q` exit code and the
   `#print axioms` output; only `propext`, `Classical.choice`, `Quot.sound`
   are acceptable).
2. Each main theorem: Lean name, informal statement, manuscript label/line.
3. Every remaining hypothesis that is an external theorem or certificate
   input, and anything left unfinished.
