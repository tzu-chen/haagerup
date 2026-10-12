#!/usr/bin/env python3
"""Record selected research-source hashes, without executing research code.

This is an editorial provenance record, not a scientific validation, a
repository backup, or permission to rerun an archived command. The research
files are read only. Existing snapshots are never overwritten.

The 384 MiB address cap includes the measured 223 MiB read-only system
locale mapping. Expected resident use is below 32 MiB; streaming keeps
at most two 64 KiB chunks live. The selected sources currently read less
than 32 MiB of file data. Respect lower inherited address-space limits.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import resource
import sys

sys.dont_write_bytecode = True
from build import cgroup_headroom, host_available

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parent
MIB = 1024 ** 2
HASH_CHUNK = 64 * 1024
ADDRESS_LIMIT = 384 * MIB

SELECTED = {
    "central_charge_eight": [
        "hi_cft_c8_proof.tex",
        "hi_cft_c8_manuscript_structure.tex",
        "hi_cft_c8_manuscript_analytic.tex",
        "hi_cft_c8_verification_guide.tex",
        "hi_cft_c8_explicitness_review_20260928.md",
        "hi_cft_20260923_next_c6_lattice.md",
        "hi_cft_20260923_next_structure_c6_coset_audit.md",
        "hi_cft_20260923_next_coset_finite_index_net.md",
    ],
    "coefficient_and_related_category_constructions": [
        "hi_infinitude_expanded.tex",
        "hi_infinitude_revised.tex",
        "hi_noncyclic_analytic_note.tex",
        "hi_noncyclic_determinant_linear_proof.tex",
        "hi_noncyclic_gis_gamma_proof.tex",
        "hi_noncyclic_gamma_identification_status.md",
        "hi_noncyclic_ansatz_z2xz6_exact.tex",
        "hi_noncyclic_ansatz_z2xz6_certificate.json",
        "hi_noncyclic_ansatz_z2xz6_unitary_certificate.json",
        "hi_noncyclic_reconstruction_extension.tex",
        "hi_even_cyclic_analytic_proof.tex",
        "extended_haagerup_README.md",
        "extended_haagerup_reconstruction_and_coefficients.tex",
        "extended_haagerup_coefficients_results.json",
    ],
    "formal_scope_and_selected_declarations": [
        "lean/README.md",
        "lean/HaagerupIzumi/C8/TRUST_BOUNDARY.md",
        "lean/HaagerupIzumi/Completion.lean",
        "lean/HaagerupIzumi/Analytic/GammaConstruction.lean",
    ],
    "completed_chain_status_and_interpretations": [
        "hi_cft_20261001_status.md",
        "hi_cft_20261001_theory_handoff.md",
        "hi_cft_20261005_status.md",
        "hi_cft_20261005_chain_handoff.md",
        "hi_cft_20261005_theory_handoff.md",
        "hi_cft_20261005_independent_module_interpretation.md",
        "hi_cft_20261005_chain_ward_interpretation_scope.md",
        "hi_cft_20261005_theory_density_interpretation.md",
        "hi_cft_20261005_theory_equal_energy_interpretation.md",
        "hi_cft_20261001_theory_symmetric_parent.md",
        "hi_cft_20261001_theory_short_anchor_scope.md",
        "hi_cft_20261001_theory_gapped_vacuum_fingerprint.md",
        "hi_cft_20261001_independent_amplitude_ward_review.md",
    ],
    "selected_completed_numerical_records": [
        "hi_cft_continuum_analysis_results.json",
        "hi_cft_stress_analysis_results.json",
        "hi_cft_20261001_independent_stress_lanczos_N18.json",
        "hi_cft_20261005_step0_r144_b1.json",
        "hi_cft_20261005_step0_r156_b1.json",
        "hi_cft_20261005_step0_scaling_r60_r144.json",
        "hi_cft_20261005_chain_ward_window_v2_N12.json",
        "hi_cft_20261005_chain_ward_window_v2_N15.json",
        "hi_cft_20261005_chain_ward_intermediate_N15.json",
        "hi_cft_20261005_theory_density_rank_readout.json",
        "hi_cft_20261005_theory_equal_energy_readout.json",
        "hi_cft_20261005_independent_module_resume_r18.json",
        "hi_cft_20261005_independent_module_correlations.json",
    ],
    "rational_candidate_exclusions": [
        "hi_cft_20260923_next_c2_weak_integral_orbifold.md",
        "hi_cft_20260923_c2two_w3_candidates.md",
        "hi_cft_20260923_c2two_su3_13_exact.py",
        "hi_cft_20260923_c2two_su3_13_exact.json",
        "hi_cft_20261001_theory_cardy_phase_obstruction.md",
        "hi_cft_minimal_products_complete.md",
        "hi_cft_w4_extension_audit.md",
        "hi_cft_w6_extension_audit.md",
        "hi_cft_20260925_ident2_candidates_minimal_products.md",
        "hi_cft_20261001_theory_rational_endpoint.md",
    ],
}


def selected_paths():
    groups = {name: [PROJECT / item for item in items]
              for name, items in SELECTED.items()}
    # Include active exposition and derived tables, keeping archived base
    # copies outside this selected-current-source inventory.
    for directory in ("c8_expanded_20260929", "c8_physics_20260927",
                      "proof_expanded", "proof_revised"):
        base = PROJECT / directory
        paths = [path for path in base.rglob("*")
                 if path.is_file() and path.suffix in (".tex", ".md")
                 and not {"base", "baseline"}.intersection(path.relative_to(base).parts)]
        groups["exposition_" + directory] = sorted(paths)
    groups["current_infrastructure_separate_from_historical_runs"] = [
        Path("/home/tzuchen/.codex/AGENTS.md"),
        PROJECT / "AGENTS.md",
        Path("/home/tzuchen/.local/bin/research-safe-run"),
        PROJECT / "hi_cft_safe_run.py",
    ]
    return groups


def stamp(stat):
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns,
            stat.st_ctime_ns)


def hash_record(path):
    before = path.stat()
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(HASH_CHUNK), b""):
            digest.update(chunk)
    if stamp(path.stat()) != stamp(before):
        raise RuntimeError("Source changed while being recorded: " + str(path))
    display = str(path.relative_to(PROJECT)) if path.is_relative_to(PROJECT) else str(path)
    return {"path": display, "sha256": digest.hexdigest(),
            "bytes": before.st_size, "mtime_ns": before.st_mtime_ns}, stamp(before)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true",
                        help="Check and list selections without hashing or writing")
    parser.add_argument("--output", default="editorial/scientific_source_snapshot.json")
    args = parser.parse_args()
    groups = selected_paths()
    all_paths = sorted({path for paths in groups.values() for path in paths})
    missing = [str(path) for path in all_paths if not path.is_file()]
    if missing:
        raise SystemExit("Missing selected sources: " + json.dumps(missing))
    total = sum(path.stat().st_size for path in all_paths)
    if total > 256 * MIB or any(path.stat().st_size > 64 * MIB for path in all_paths):
        raise SystemExit("Selected source inventory exceeds its bounded editorial scope")
    if args.list:
        print(json.dumps({"files": len(all_paths), "bytes": total,
                          "groups": {key: len(value) for key, value in groups.items()}}, indent=2))
        return
    output = (ROOT / args.output).resolve()
    if not output.is_relative_to(ROOT / "editorial") or output.suffix != ".json":
        raise SystemExit("Snapshot destination must be a JSON file inside editorial/")
    if output.exists():
        raise SystemExit("Preserve the existing snapshot; choose a new --output name")
    if host_available() < 8 * 1024 ** 3 + ADDRESS_LIMIT or cgroup_headroom() < ADDRESS_LIMIT:
        raise SystemExit("Insufficient host/cgroup headroom for bounded editorial hashing")
    inherited = resource.getrlimit(resource.RLIMIT_AS)
    address_limit = min([ADDRESS_LIMIT] + [value for value in inherited
                        if value != resource.RLIM_INFINITY])
    baseline = {}
    for line in Path("/proc/self/status").read_text().splitlines():
        key, _, value = line.partition(":")
        if key in ("VmSize", "VmRSS", "VmPeak"):
            baseline[key + "_bytes"] = int(value.split()[0]) * 1024
    if "VmSize_bytes" not in baseline:
        raise SystemExit("Cannot establish the imported process address-space baseline")
    if baseline["VmSize_bytes"] + 16 * MIB > address_limit:
        raise SystemExit("Imported process exceeds the bounded hashing baseline; review its mappings before retrying")
    resource.setrlimit(resource.RLIMIT_AS, (address_limit, address_limit))
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    started = datetime.now(timezone.utc).isoformat()
    inventory = {}
    records = {}
    stamps = {}
    for path in all_paths:
        records[path], stamps[path] = hash_record(path)
    for name, paths in groups.items():
        inventory[name] = [records[path] for path in paths]
    # Detect a source changing after its individual hash was read as well.
    for path in all_paths:
        if stamp(path.stat()) != stamps[path]:
            raise RuntimeError("Source changed during the snapshot: " + str(path))
    result = {
        "scope": "Selected source identities read for this textbook; not a complete repository or certificate audit",
        "started_utc": started,
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "project_root": str(PROJECT),
        "source_files": len(all_paths),
        "source_bytes": total,
        "historical_provenance": "Historical run hashes and archived sources remain unchanged in their original records; current infrastructure hashes below do not replace them",
        "execution_scope": "No research sources were imported or executed; no Lean build, numerical continuation, or certificate replay",
        "editorial_limits": {"address_space_bytes": address_limit,
                             "read_chunk_bytes": HASH_CHUNK,
                             "cpu_seconds": 30, "cpus": 1},
        "baseline_process_memory": baseline,
        "peak_rss_kib_before_snapshot_write": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "groups": inventory,
    }
    payload = json.dumps(result, indent=2) + "\n"
    with output.open("x") as stream:
        stream.write(payload)
    print(json.dumps({"snapshot": str(output.relative_to(ROOT)),
                      "source_files": len(all_paths), "source_bytes": total}, indent=2))


if __name__ == "__main__":
    main()
