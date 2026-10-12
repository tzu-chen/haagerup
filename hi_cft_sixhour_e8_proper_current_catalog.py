"""Necessary proper-current denominator catalog inside possible Haagerup W1.

Pure standard-library exact algebra. Run only in the coordinated guarded slot.
Graph containment concerns semisimple parts; it does not certify a simultaneous
placement of the abelian completion, or any Haagerup action on the commutant.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

from hi_cft_sixhour_e8_subalgebra_refine import extra_data, unitary_residual


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--database", type=Path, default=Path("/tmp/hi_cft_sla_sssdb.dat"))
    parser.add_argument("--scan", type=Path, default=Path("hi_cft_sixhour_e8_subalgebra_results.json"))
    parser.add_argument("--refined", type=Path, default=Path("hi_cft_sixhour_e8_subalgebra_refined_results.json"))
    parser.add_argument("--characters", type=Path, default=Path("hi_cft_sixhour_e8_character_results.json"))
    parser.add_argument("--output", type=Path, default=Path("hi_cft_sixhour_e8_proper_current_results.json"))
    args = parser.parse_args()
    scan = json.loads(args.scan.read_text())
    refined = json.loads(args.refined.read_text())
    characters = json.loads(args.characters.read_text())
    raw = args.database.read_bytes()
    assert sha256(raw).hexdigest() == scan["database_sha256"]
    _, graph = extra_data(raw.decode())
    entries = {r["database_number"]: r for r in scan["all_semisimple_embeddings"]}
    adjacency = defaultdict(set)
    for large, small in graph:
        assert (248 if large == 0 else entries[large]["dimension"]) > entries[small]["dimension"]
        adjacency[large].add(small)
    # Here a semisimple_database_number of zero means the zero Lie algebra,
    # whereas the database graph's vertex zero means ambient E8. Do not reuse
    # adjacency[0] in the zero-algebra case.
    closures = {0: {0}}

    def downset(number):
        if number not in closures:
            found, todo = {0, number}, [number]
            while todo:
                node = todo.pop()
                new = adjacency[node]-found
                found.update(new)
                todo.extend(new)
            closures[number] = found
        return closures[number]

    full = [r for r in characters["candidate_rows"]
            if r["passes_all_including_small_residual_field"]]
    candidates, rejects = [], Counter()
    for old in refined["denominator_refined_candidates"]:
        row = old.copy()
        number, abelian = row["semisimple_database_number"], row["abelian_rank"]
        rank = entries[number]["rank"] if number else 0
        if not row["passes_torus_necessary_test"]:
            rejects["denominator_ambient_torus_bound"] += 1
            continue
        charge = F(row["denominator_c"])
        witnesses = []
        for host in full:
            hn, hr = host["semisimple_database_number"], host["abelian_rank"]
            host_rank = (entries[hn]["rank"] if hn else 0)+hr
            if number not in downset(hn):
                rejects["pair_semisimple_graph"] += 1
                continue
            if rank+abelian > host_rank:
                rejects["pair_rank"] += 1
                continue
            if row["current_dimension"] > host["W1_dimension"]:
                rejects["pair_dimension"] += 1
                continue
            difference = F(host["current_Sugawara_c"])-charge
            valid, reason = unitary_residual(difference)
            if not valid:
                rejects["pair_Sugawara_difference_"+reason] += 1
                continue
            equal = row["current_dimension"] == host["W1_dimension"]
            if equal:
                # An injective inclusion of equal-dimensional reductive Lie
                # algebras is equality. The inclusion graph is strict in dim.
                assert (number, abelian) == (hn, hr)
                assert difference == 0
            if host["W1_dimension"] == 6:
                # c_den >=11/2 >5 and c_den<=dim(A)<=6 force dim(A)=6.
                assert equal
            witnesses.append({
                "W1_dimension": host["W1_dimension"],
                "host_semisimple_database_number": hn,
                "host_abelian_rank": hr,
                "host_total_rank": host_rank,
                "host_current_Sugawara_c": host["current_Sugawara_c"],
                "host_residual_c": host["residual_c"],
                "Sugawara_difference_c": str(difference),
                "Sugawara_difference_Virasoro_class": reason,
                "is_all_current_denominator": equal,
                "pure_Cartan6_rank1_current_obstruction_if_no_joint_neutral_current":
                    host["W1_dimension"] == 19 and number == 0 and abelian == 6,
            })
        if witnesses:
            row["possible_full_W1_hosts"] = witnesses
            row["simultaneous_toral_placement_certified"] = False
            candidates.append(row)
        else:
            rejects["denominator_no_host_witness"] += 1
    summaries = {}
    for dim in (6, 19):
        rows = [r for r in candidates if any(w["W1_dimension"] == dim
                                             for w in r["possible_full_W1_hosts"])]
        proper = [r for r in rows if any(w["W1_dimension"] == dim and
                    not w["is_all_current_denominator"] for w in r["possible_full_W1_hosts"])]
        values = sorted({F(r["coset_c"]) for r in rows})
        proper_values = sorted({F(r["coset_c"]) for r in proper})
        non2 = sorted((x for x in values if x != 2), key=lambda x: (abs(x-2), x))
        summaries[str(dim)] = {
            "denominator_embedding_rows": len(rows),
            "proper_denominator_embedding_rows": len(proper),
            "distinct_coset_c": list(map(str, values)),
            "distinct_proper_coset_c": list(map(str, proper_values)),
            "nearest_non2_c": str(non2[0]) if non2 else None,
            "nearest_non2_distance": str(abs(non2[0]-2)) if non2 else None,
        }
    assert summaries["6"]["proper_denominator_embedding_rows"] == 0
    result = {
        "source_database_sha256": scan["database_sha256"],
        "input_full_W1_hosts": len(full),
        "input_denominator_rows": len(refined["denominator_refined_candidates"]),
        "remaining_denominator_rows": len(candidates),
        "candidate_rows": candidates,
        "summaries": summaries,
        "rejection_counts_at_first_failed_test": dict(rejects),
        "scope": "Necessary filters only for reductive current denominators A inside a putative full W1 of dimension6 or19. Graph containment, rank and dimension do not certify simultaneous abelian placement. The nonconjugate A2 linear-equivalence exception remains a general-catalog caveat. No physical chain-to-coset map or Haagerup action is constructed.",
    }
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k not in
                     ("candidate_rows", "scope")}), flush=True)


if __name__ == "__main__":
    main()
