"""Exact saved-catalog filter after the ten audited current-host exclusions.

Standard library only. No Lie-algebra enumeration or new embedding claim.
Run only in root's coordinated safe-run slot; expected RSS below64MiB.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path


EXCLUDED = frozenset({0, 372, 379, 483, 496, 514, 579, 600, 613, 617})


def read_hashed(path):
    raw = path.read_bytes()
    return json.loads(raw), sha256(raw).hexdigest()


def summarize(rows, dimension=None):
    selected = []
    witnesses = 0
    by_charge = defaultdict(list)
    for row in rows:
        support = [w for w in row["possible_full_W1_hosts"]
                   if dimension is None or w["W1_dimension"] == dimension]
        if not support:
            continue
        selected.append(row)
        witnesses += len(support)
        by_charge[Fraction(row["coset_c"])].append({
            "denominator_semisimple_database_number": row["semisimple_database_number"],
            "denominator_abelian_rank": row["abelian_rank"],
            "hosts": sorted({w["host_semisimple_database_number"] for w in support}),
            "all_current_in_some_host": any(w["is_all_current_denominator"] for w in support),
        })
    ordered = sorted(by_charge)
    nearest = sorted(ordered, key=lambda c: (abs(c-2), c))
    below = [c for c in ordered if c < 2]
    above = [c for c in ordered if c > 2]
    return {
        "denominator_rows": len(selected),
        "host_witness_pairs": witnesses,
        "distinct_coset_c": list(map(str, ordered)),
        "nearest_to_two": [{"c": str(c), "distance": str(abs(c-2)),
                            "denominator_rows": by_charge[c]} for c in nearest[:10]],
        "largest_below_two": str(max(below)) if below else None,
        "smallest_above_two": str(min(above)) if above else None,
        "charge_to_rows": {str(c): by_charge[c] for c in ordered},
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path,
                        default=Path("hi_cft_sixhour_e8_proper_current_results.json"))
    parser.add_argument("--characters", type=Path,
                        default=Path("hi_cft_sixhour_e8_character_results.json"))
    parser.add_argument("--output", type=Path,
                        default=None)
    parser.add_argument("--exclude-host615", action="store_true",
                        help="Also apply the independently audited Potts-pair host615 exclusion.")
    parser.add_argument("--exclude-host614", action="store_true",
                        help="After host615, also apply the audited lattice-times-tricritical-Potts host614 exclusion.")
    parser.add_argument("--exclude-host497", action="store_true",
                        help="After host614, apply the jointly audited A3_1/A1_5 flavoured-character contradiction.")
    args = parser.parse_args()
    if args.exclude_host614 and not args.exclude_host615:
        parser.error("--exclude-host614 requires --exclude-host615 in the reviewed filter sequence")
    if args.exclude_host497 and not args.exclude_host614:
        parser.error("--exclude-host497 requires --exclude-host614 in the reviewed filter sequence")
    excluded = (EXCLUDED | ({615} if args.exclude_host615 else set())
                | ({614} if args.exclude_host614 else set())
                | ({497} if args.exclude_host497 else set()))
    if args.output is None:
        args.output = Path("hi_cft_third_e8_filtered_grid_host13_results.json"
                           if args.exclude_host497 else
                           "hi_cft_third_e8_filtered_grid_host12_results.json"
                           if args.exclude_host614 else
                           "hi_cft_third_e8_filtered_grid_host11_results.json"
                           if args.exclude_host615 else
                           "hi_cft_third_e8_filtered_grid_results.json")
    old, catalog_hash = read_hashed(args.catalog)
    characters, character_hash = read_hashed(args.characters)
    rows, removed_pairs = [], Counter()
    for source in old["candidate_rows"]:
        support = []
        for witness in source["possible_full_W1_hosts"]:
            host = witness["host_semisimple_database_number"]
            if host in excluded:
                removed_pairs[host] += 1
            else:
                support.append(witness)
        if support:
            row = dict(source)
            row["possible_full_W1_hosts"] = support
            rows.append(row)
    all_hosts = [r for r in characters["candidate_rows"]
                 if r["passes_all_including_small_residual_field"]]
    remaining_hosts = [r for r in all_hosts
                       if r["semisimple_database_number"] not in excluded]
    eliminated_hosts = [r for r in all_hosts
                        if r["semisimple_database_number"] in excluded]
    found_ids = {r["semisimple_database_number"] for r in eliminated_hosts}
    assert found_ids == excluded, (sorted(found_ids), sorted(excluded))
    assert len({(r["semisimple_database_number"], r["abelian_rank"], r["W1_dimension"])
                for r in all_hosts}) == len(all_hosts)
    summary = {"all": summarize(rows), "6": summarize(rows, 6), "19": summarize(rows, 19)}
    charges = {Fraction(r["coset_c"]) for r in rows}
    checks = {
        "all_requested_exclusion_ids_found": found_ids == excluded,
        "no_excluded_host_in_retained_witnesses": all(
            w["host_semisimple_database_number"] not in excluded
            for r in rows for w in r["possible_full_W1_hosts"]),
        "no_c_equal_two": Fraction(2) not in charges,
        "no_c_equal_72_over_35": Fraction(72, 35) not in charges,
        "six_current_denominators_all_current": all(
            w["is_all_current_denominator"] for r in rows
            for w in r["possible_full_W1_hosts"] if w["W1_dimension"] == 6),
        "retained_rows_plus_removed_rows_equals_input":
            len(rows) + sum(not any(w["host_semisimple_database_number"] not in excluded
                                   for w in r["possible_full_W1_hosts"])
                            for r in old["candidate_rows"]) == len(old["candidate_rows"]),
    }
    if args.exclude_host615:
        checks["no_c_equal_21_over_10"] = Fraction(21, 10) not in charges
    if args.exclude_host497:
        checks["no_c_equal_13_over_7"] = Fraction(13, 7) not in charges
    elif args.exclude_host614:
        support_13_7 = {w["host_semisimple_database_number"]
                        for r in rows if Fraction(r["coset_c"]) == Fraction(13, 7)
                        for w in r["possible_full_W1_hosts"]}
        checks["c_13_over_7_retained_only_through_host497"] = support_13_7 == {497}
    assert all(checks.values()), checks
    result = {
        "producer_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "inputs": {str(args.catalog): catalog_hash, str(args.characters): character_hash},
        "excluded_host_ids": sorted(excluded),
        "exclusion_scope": "Conditional on the unitary finite-index E8 Haagerup fixed-algebra setup, strongly rational current frame and residual VOA/net bridge; not a chain-to-coset identification.",
        "input_denominator_rows": len(old["candidate_rows"]),
        "remaining_denominator_rows": len(rows),
        "input_full_current_hosts": len(all_hosts),
        "eliminated_full_current_host_rows": len(eliminated_hosts),
        "remaining_full_current_host_rows": len(remaining_hosts),
        "removed_witness_pairs_by_host": dict(sorted(removed_pairs.items())),
        "checks": checks,
        "summaries": summary,
        "candidate_rows": rows,
        "remaining_full_current_hosts": [{k: r[k] for k in
            ("semisimple_database_number", "abelian_rank", "W1_dimension",
             "current_Sugawara_c", "residual_c", "factor_description")}
            for r in remaining_hosts],
        "scope": "This removes certified impossible full-current host witnesses from the saved necessary denominator graph/rank catalog. Retained rows are not certified simultaneous embeddings, VOAs, hypergroup actions or physical CFT candidates.",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in
        ("input_denominator_rows", "remaining_denominator_rows", "input_full_current_hosts",
         "eliminated_full_current_host_rows", "remaining_full_current_host_rows", "checks")}, indent=2))
    print(json.dumps({key: {k: value[k] for k in
        ("denominator_rows", "host_witness_pairs", "largest_below_two", "smallest_above_two",
         "nearest_to_two")} for key, value in summary.items()}, indent=2))


if __name__ == "__main__":
    main()
