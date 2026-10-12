# Successful commands for the 27 September revision

Run from `/home/tzuchen/Codes/haagerup`, serially. These output paths now
exist and must not be reused; choose fresh names for a future replay.
The resource estimates and implementation audits are in `resource_review.md`
and `structural_replay_review.md`. The original records were not overwritten.

```sh
python hi_cft_safe_run.py --limit-mib 1024 -- python hi_cft_20260923_c8two_proof_bundle.py --output c8_revision_20260927/provenance_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8_minimal_generators.py --output c8_revision_20260927/minimal_generators_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8_exact_check.py --closure --output c8_revision_20260927/unitary_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8_exact_grade3.py --output c8_revision_20260927/grade3_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8two_gate4_singlet_verify.py --output c8_revision_20260927/gate4_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8two_charged_span_verify.py --output c8_revision_20260927/charged_span_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8two_jacobi_check.py --gate4 c8_revision_20260927/gate4_replay.json --charged-span hi_cft_20260923_c8two_structure_charged_span.json --output c8_revision_20260927/gate5_replay.json
python hi_cft_safe_run.py --limit-mib 256 -- python c8_revision_20260927/check_top_bound.py
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 300s python hi_cft_20260923_next_structure_core_extension.py --seconds 280 --output c8_revision_20260927/core_extension_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 300s python hi_cft_20260923_next_81top_exact.py --sector all --seconds 280 --output c8_revision_20260927/top81_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 600s python c8_revision_20260927/replay_structural_input.py potts --output c8_revision_20260927/potts_replay.json
python hi_cft_safe_run.py --limit-mib 2048 -- timeout --signal=TERM --kill-after=10s 600s python c8_revision_20260927/replay_structural_input.py pf13_membership --output c8_revision_20260927/pf13_membership_replay.json
python lean/safe_lean.py lean/HaagerupIzumi/CFT/FiniteClosure.lean
python lean/safe_lean.py lean/HaagerupIzumi/CFT/TopBound.lean
```

The top-bound checker prints its JSON to stdout; this was redirected to
`top_bound_replay.json`, with guard diagnostics on stderr. Other command
output and diagnostics were recorded in the associated logs. The tiny
Jacobi check consumes the **producer** charged-span schema; the independently
verified charged span is an additional input ledger root, not a compatible
replacement for that CLI argument. The first incorrect schema attempt was
retained as a failed-run log and is not counted as a passed replay.

The final supplemented ledger command is preserved separately as
`final_ledger_command.sh`. Its artifact entries bind documents and logs by
hash only; semantic success checks apply to the named `--replay` kinds.
