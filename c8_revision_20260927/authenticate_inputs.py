"""Authenticate the supplemented c=8 finite-proof input ledger.

Run from the repository root through ~/.local/bin/research-safe-run, for example:

  ~/.local/bin/research-safe-run --limit-mib 1024 -- \
    python c8_revision_20260927/authenticate_inputs.py \
      --output c8_revision_20260927/finite_input_ledger.json

Optional --replay KIND=PATH arguments bind fresh successful replay outputs.
Kinds: provenance, minimal_generation, unitary, grade3, gate4, charged_span,
gate5, core_extension, top81, potts, pf13_membership.
--artifact PATH binds an additional document or log without asserting
mathematical correctness. No existing record is changed and no VOA mode,
matrix solve, or numerical library is run by this script.

The 23 September combined ledger omitted the minimal-generation certificate
which links the saved weight-two fields to the explicit generated algebra.
This new ledger supplements that boundary and also binds the separate exact
grade-three dimension certificate. The original 640-file ledger stays intact.

Allocation review: standard-library imports, at most 8 MiB of JSON input at
once, a 1 MiB hashing buffer, and small dictionaries of at most 4096 paths.
Expected RSS is below 128 MiB; explicit RSS review boundary is 256 MiB.
The launcher imposes the normal desktop reserve/group watchdog and limits
CPU affinity and threads. A 180-second alarm bounds this read-only replay.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
from time import monotonic


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "hi_cft_20260923_"
MIB = 1024 ** 2
GIB = 1024 ** 3
MAX_JSON = 8 * MIB
MAX_FILES = 4096
MAX_HASHED_BYTES = 32 * GIB
SHA256 = re.compile(r"[0-9a-f]{64}\Z")

ORIGINALS = {
    "provenance": "c8two_proof_bundle.json",
    "minimal_generation": "c8_minimal_generators.json",
    "unitary": "c8_exact_unitary_certificate.json",
    "grade3": "c8_grade3_exact_v2.json",
    "gate4": "c8two_gate4_verified.json",
    "charged_span": "c8two_charged_span_verified.json",
    "gate5": "c8two_gate5_verified.json",
    "core_extension": "next_structure_core_extension.json",
    "top81": "next_81top_all.json",
    "potts": "proof_potts_exact.json",
    "pf13_membership": "proof_pf13_membership.json",
}

# These three producers had no hash entry in the frozen combined ledger,
# although their output certificates were present. The older artifact-audit
# manifest does record their historical hashes, as well as the two recursive
# fields used by the OPE producers. Authenticate those entries explicitly.
SUPPLEMENTAL_PRODUCERS = {
    "pf13_exact_field_producer": PREFIX + "proof_pf13_exact.py",
    "pf13_independent_dly_comparison_producer": PREFIX + "proof_pf13_dly.py",
    "pf13_weight_six_truncation_producer": PREFIX + "proof_pf13_weight7.py",
}
SUPPLEMENTAL_FIELDS = {
    "pf13_recursive_W5": PREFIX + "proof_pf13_W5.json",
    "pf13_recursive_W6": PREFIX + "proof_pf13_W6.json",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def validate(kind, value):
    """Return the precise terminal facts whose equality a replay must retain."""
    if kind == "provenance":
        facts = {
            "format": "c8-completed-proof-provenance-ledger-v1",
            "status": "all_finite_certificate_premises_authenticated",
            "lower_exact_identities": 3970,
            "P4_current_controls": 18,
            "P4_Virasoro_controls": 6,
            "Gate4_identities": 2898,
            "Gate5_independent_channels": 24,
            "charged_quotient_dimension": 322,
        }
    elif kind == "minimal_generation":
        facts = {
            "input": "six explicitly embedded affine currents, the ambient stress, "
                     "and the displayed three-vertex weight-two field",
            "arithmetic": "Q(sqrt(13),sqrt(-3))",
            "initial_span_dimension": 24,
            "resulting_weight_two_dimension": 120,
            "processed_basis_vectors": 120,
            "all_previously_located_highest_vectors_and_stress_are_generated": True,
        }
    elif kind == "unitary":
        facts = {
            "coefficient_field": "Q(sqrt(13),sqrt(-3))",
            "exact_grade_two_dimension": 120,
            "exact_OPE_closure": True,
            "exact_PCT_preservation": True,
            "exact_complementary_Virasoro_modes": True,
        }
        rows = value.get("primary_checks")
        require(isinstance(rows, list) and len(rows) == 8,
                "unitary certificate requires eight primary multiplets")
        require(all(row.get("exact_primary_and_eigenvalue_checks") is True
                    for row in rows), "incomplete exact primary checks")
    elif kind == "grade3":
        facts = {
            "arithmetic": "Q(sqrt(13),sqrt(-3))",
            "prime": 0,
            "grade_three_span_dimension": 956,
            "characteristic_zero_lower_bound": 956,
            "characteristic_zero_span_dimension_certified": True,
        }
        require(any(row.get("stage") == "affine_and_translation_descendants"
                    and row.get("dimension") == 634
                    for row in value.get("history", [])),
                "missing exact normal grade-three dimension")
    elif kind == "gate4":
        facts = {
            "format": "verified-H4-raising-certificate-v1",
            "derivation_method": "exact-raised-controls-and-joint-singlet-recovery",
            "status": "all_Gate4_identities_proved_by_exact_seeds_and_raising",
            "old_exact_seed_count": 2145,
            "additional_direct_exact_count": 118,
            "additional_singlet_exact_count": 12,
            "independent_projected_integer_residuals_zero": 12,
            "implied_A0P3_identity_count": 2898,
        }
    elif kind == "charged_span":
        facts = {
            "format": "independently-verified-charged-quotient-span-v1",
            "status": "charged_pair_current_span_is_exact_P3_quotient",
            "exact_quotient_dimension": 322,
            "lowering_image_rank": 294,
            "combined_rank": 322,
            "sl2_and_cross_commutators_verified": True,
        }
    elif kind == "gate5":
        facts = {
            "format": "exact-Jacobi-Gate5-data-v1",
            "status": "all_Gate5_families_proved_by_Jacobi",
            "all_eight_charged_pair_data_passed": True,
            "all_eight_charged_families_derived": True,
            "Gate4_certificate_authenticated": True,
            "charged_pair_span_certificate_authenticated": True,
            "neutral_family_derived": True,
            "all24_independent_Gate5_channels": True,
        }
    elif kind == "core_extension":
        facts = {
            "arithmetic": "Q(sqrt(13),sqrt(-3)); exact sparse elimination",
            "S2_dimension": 120,
            "known_T_tensor_PF13_grade2_dimension": 15,
            "zero_s_energy_dimension": 25,
            "extra_zero_s_energy_dimension": 10,
            "classified_dimension": 25,
            "order13_target_weight_count": 6,
            "all_six_order13_target_weights_present": True,
            "PF13_actual_top_labels_at_12over13": [[13, 1], [13, 12]],
            "order13_target_multiplicities": {
                "(-1, -5)": 1, "(-1, 5)": 1,
                "(0, -8)": 1, "(0, 8)": 1,
                "(1, -5)": 1, "(1, 5)": 1,
            },
        }
    elif kind == "top81":
        facts = {
            "format": "exact-mixed-top-v1",
            "status": "complete",
            "arithmetic": "Q(sqrt(13),sqrt(-3))",
        }
        rows = value.get("sectors")
        require(isinstance(rows, list) and len(rows) == 4,
                "top81 requires all four sectors")
        require({(row.get("glue_sign"), row.get("sector_sign")) for row in rows}
                == {(1, 1), (1, -1), (-1, 1), (-1, -1)},
                "top81 sector signs are incomplete or repeated")
        for row in rows:
            require(type(row.get("cyclic_dimension")) is int
                    and row["cyclic_dimension"] == 81
                    and type(row.get("seed_eigenspace_dimension")) is int
                    and row["seed_eigenspace_dimension"] == 1
                    and row.get("irreducible") is True
                    and row.get("exact_weighted_adjoint_checks") is True,
                    "top81 lacks complete cyclic/adjoint/eigenline checks")
            require(len(row.get("rows", [])) == 81
                    and len(row.get("recipes", [])) == 81,
                    "top81 missing exact cyclic rows or recipes")
    elif kind == "potts":
        facts = {
            "arithmetic": "Q(sqrt(13),sqrt(-3))",
            "exact_p_central_charge": "4/5",
            "exact_weight_three_primary": True,
            "exact_membership_in_generated_S3": True,
            "Cartan_zero_span_rank_at_membership": 41,
            "tested_zero_weight_pairs": 1,
            "w2_eigenvalues_on_H_E_F": [
                ["0", "0", "0", "0"],
                ["2", "0", "0", "0"],
                ["-2", "0", "0", "0"],
            ],
        }
        require(bool(value.get("weight_three_primary"))
                and bool(value.get("potts_stress")), "Potts fields are missing")
    elif kind == "pf13_membership":
        facts = {
            "exact_membership_in_generated_S3": True,
            "Cartan_zero_span_rank_at_membership": 58,
            "zero_weight_pairs": 154,
            "positive_stress_decomposition_coefficients": [
                "1", "3403/4563", "25/6", "25/26"],
            "decomposition_order": [
                "omega_A1_1", "omega_A1_39", "SU2_average_Potts_stress",
                "SU2_average_c8over5_stress"],
            "PCT_stable_weight_three_line": True,
            "parafermion_identification_proved": False,
        }
    else:
        raise ValueError("unsupported replay kind: " + kind)
    for key, expected in facts.items():
        actual = value.get(key)
        require(type(actual) is type(expected) and actual == expected,
                f"{kind}: incomplete or incorrect {key}")
    return facts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--replay", action="append", default=[], metavar="KIND=PATH")
    parser.add_argument("--artifact", action="append", default=[], metavar="PATH")
    args = parser.parse_args()
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    require(0 < soft <= GIB and 0 < hard <= 6 * GIB,
            "run through ~/.local/bin/research-safe-run --limit-mib 1024")
    require(len(os.sched_getaffinity(0)) <= 2, "CPU affinity exceeds two CPUs")
    parent = Path(f"/proc/{os.getppid()}/cmdline").read_bytes().split(b"\0")
    require(len(parent) > 1, "cannot identify watchdog parent command")
    parent_launcher = Path(os.fsdecode(parent[1]))
    if not parent_launcher.is_absolute():
        parent_cwd = Path(os.readlink(f"/proc/{os.getppid()}/cwd"))
        parent_launcher = parent_cwd / parent_launcher
    require(parent_launcher.resolve() == (Path.home() / ".local/bin/research-safe-run").resolve(),
            "active ~/.local/bin/research-safe-run watchdog parent is required")
    started = monotonic()

    def timeout(*_):
        raise TimeoutError("revision-ledger 180-second deadline")

    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(180)
    hashes, snapshots = {}, {}
    hashed_bytes = 0
    output = Path(args.output).resolve()
    temporary = output.with_suffix(output.suffix + ".tmp")
    require(not output.exists() and not temporary.exists(),
            "output and temporary paths must be fresh")

    def resolve(path):
        path = Path(path)
        return (path if path.is_absolute() else ROOT / path).resolve()

    def stamp(path):
        stat = path.stat()
        return stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns

    def boundary():
        require(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss <= 256 * 1024,
                "256 MiB RSS review boundary exceeded")
        require(monotonic() - started <= 180, "revision-ledger time budget exceeded")

    def bind(path, expected=None):
        nonlocal hashed_bytes
        path = resolve(path)
        name = str(path)
        require(path != output and path != temporary, "output cannot be an input")
        if expected is not None:
            require(isinstance(expected, str) and SHA256.fullmatch(expected),
                    "invalid SHA-256 for " + name)
        if name not in hashes:
            require(len(hashes) < MAX_FILES, "too many authenticated files")
            before = stamp(path)
            require(before[2] <= 8 * GIB, "individual input exceeds 8 GiB")
            require(hashed_bytes + before[2] <= MAX_HASHED_BYTES,
                    "hashing exceeds reviewed 32 GiB work budget")
            digest = hashlib.sha256()
            read_bytes = 0
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(MIB), b""):
                    read_bytes += len(chunk)
                    require(read_bytes <= before[2], "input grew during hashing")
                    digest.update(chunk)
                    boundary()
            require(read_bytes == before[2] and stamp(path) == before,
                    "input changed during hashing: " + name)
            hashes[name], snapshots[name] = digest.hexdigest(), before
            hashed_bytes += read_bytes
        else:
            require(stamp(path) == snapshots[name], "input changed after authentication")
        if expected is not None:
            require(hashes[name] == expected, "source hash mismatch: " + name)
        return name

    def graphs(value, depth=0):
        require(depth <= 64, "JSON nesting exceeds reviewed boundary")
        if isinstance(value, dict):
            for key, item in value.items():
                if (key.endswith("source_sha256")
                    or key == "ancestor_files_sha256"
                    or (key == "sources" and isinstance(item, dict)
                        and all(isinstance(digest, str) and SHA256.fullmatch(digest)
                                for digest in item.values()))):
                    require(isinstance(item, dict), "unexpected source-graph encoding")
                    require(len(item) <= MAX_FILES, "oversized source graph")
                    for path, expected in item.items():
                        bind(path, expected)
                elif isinstance(item, (dict, list)):
                    graphs(item, depth + 1)
        elif isinstance(value, list):
            for item in value:
                graphs(item, depth + 1)

    def read(path):
        path = resolve(path)
        name = bind(path)
        require(snapshots[name][2] <= MAX_JSON, "JSON exceeds 8 MiB cap")
        with path.open("rb") as stream:
            raw = stream.read(MAX_JSON + 1)
        require(len(raw) <= MAX_JSON and stamp(path) == snapshots[name],
                "JSON changed or exceeded its cap")
        require(hashlib.sha256(raw).hexdigest() == hashes[name],
                "JSON changed between authentication and parsing")
        value = json.loads(raw, object_pairs_hook=unique_object)
        require(isinstance(value, dict), "certificate must be a JSON object")
        graphs(value)
        return value

    originals, original_facts = {}, {}
    for kind, filename in ORIGINALS.items():
        path = ROOT / (PREFIX + filename)
        value = read(path)
        original_facts[kind] = validate(kind, value)
        originals[kind] = str(path)

    minimal_name = str(ROOT / (PREFIX + ORIGINALS["minimal_generation"]))
    old_bundle = read(ROOT / (PREFIX + ORIGINALS["provenance"]))
    old_graph = {str(resolve(path)): digest
                 for path, digest in old_bundle["source_sha256"].items()}
    require(len(old_graph) == 640, "unexpected frozen combined-ledger size")
    require(minimal_name not in old_graph,
            "frozen ledger no longer matches the documented omission")
    supplement = {
        "explicit_generation": originals["minimal_generation"],
        "independent_exact_grade3_dimension": originals["grade3"],
    }
    older_audit_path = ROOT / (PREFIX + "proof_artifact_audit.json")
    older_audit = read(older_audit_path)
    require(older_audit.get("all_integrity_checks_passed") is True,
            "older structural artifact audit did not pass")
    older_manifest = older_audit.get("manifest_sha256")
    require(isinstance(older_manifest, dict), "missing older structural manifest")
    supplemental_producers, supplemental_fields = {}, {}
    for table, destination in ((SUPPLEMENTAL_PRODUCERS, supplemental_producers),
                               (SUPPLEMENTAL_FIELDS, supplemental_fields)):
        for label, filename in table.items():
            require(filename in older_manifest, "missing older hash: " + filename)
            destination[label] = bind(ROOT / filename, older_manifest[filename])

    replays = {}
    for argument in args.replay:
        kind, separator, filename = argument.partition("=")
        require(separator and kind in ORIGINALS and filename,
                "expected --replay KIND=PATH with a supported kind")
        require(kind not in replays, "duplicate replay kind: " + kind)
        path = resolve(filename)
        require(str(path) != originals[kind], "a replay must have a fresh path")
        value = read(path)
        require(validate(kind, value) == original_facts[kind],
                "replay terminal facts differ from the original")
        replays[kind] = str(path)

    artifacts = [bind(path) for path in args.artifact]
    bind(__file__)
    bind(Path.home() / ".local/bin/research-safe-run")
    for name, snapshot in snapshots.items():
        require(stamp(Path(name)) == snapshot, "authenticated input changed: " + name)
    boundary()
    result = {
        "format": "c8-revision-supplemented-finite-ledger-v1",
        "status": "finite_inputs_and_explicit_generation_authenticated",
        "original_frozen_ledger_files": len(old_graph),
        "original_certificates": originals,
        "supplemental_explicit_inputs": supplement,
        "supplemental_producer_sources_hashed_only": supplemental_producers,
        "supplemental_recursive_fields_hashed_only": supplemental_fields,
        "supplemental_historical_hash_manifest": str(older_audit_path),
        "terminal_facts": original_facts,
        "fresh_successful_replay_outputs": replays,
        "additional_artifacts_hashed_only": artifacts,
        "source_sha256": dict(sorted(hashes.items())),
        "authenticated_file_count": len(hashes),
        "hashed_bytes": hashed_bytes,
        "scope": "Source hashes and exact terminal fields are authenticated. "
                 "This ledger supplements the explicit-generation omission in the "
                 "frozen combined ledger. It performs no new lattice mode or linear "
                 "algebra calculation and does not formally prove the VOA lemmas, "
                 "VOA-to-net comparison, complete unitarity, or categorical identification.",
        "gate5_replay_note": "The frozen Jacobi checker --charged-span option takes "
                             "the producer c8two_structure_charged_span.json schema. "
                             "The independent charged-span verifier is bound separately.",
        "seconds": monotonic() - started,
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    encoded = (json.dumps(result, indent=2) + "\n").encode()
    require(len(encoded) <= MAX_JSON, "output exceeds reviewed JSON cap")
    with temporary.open("xb") as stream:
        stream.write(encoded)
        stream.flush()
        os.fsync(stream.fileno())
    # A hard-link installation fails if output exists; it cannot replace an
    # original certificate even if another process creates that path meanwhile.
    os.link(temporary, output)
    temporary.unlink()
    signal.alarm(0)
    print(json.dumps({key: result[key] for key in
                      ("status", "authenticated_file_count", "seconds", "peak_rss_KiB")}))


if __name__ == "__main__":
    main()
