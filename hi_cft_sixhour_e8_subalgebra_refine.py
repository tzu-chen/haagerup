"""Exact small-rank refinements of the SLA E8 embedding scan.

No numerical linear algebra. Run only in the coordinated guarded slot.
The torus certificate distinguishes an actual centralizer rank from8-rank(K).
"""
import argparse
import ast
from collections import Counter, defaultdict
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json
import re

import hi_cft_sixhour_e8_subalgebra_scan as base


def gap_positive_roots(cartan):
    """Literal algorithm in GAP algliess.gi CartanMatrixToPositiveRoots."""
    n = len(cartan)
    positive = [tuple(int(i == j) for i in range(n)) for j in range(n)]
    found = set(positive)
    begin = 0
    while begin < len(positive):
        end = len(positive)
        for a in positive[begin:end]:
            for j in range(n):
                b = list(a)
                r = -1
                while tuple(b) in found:
                    b[j] -= 1
                    r += 1
                q = r-sum(cartan[i][j]*a[i] for i in range(n))
                b = list(a)
                b[j] += 1
                if q > 0 and tuple(b) not in found:
                    positive.append(tuple(b))
                    found.add(tuple(b))
        begin = end
    return positive


def sparse_support(row):
    """Ignore GAP coefficient expressions, keeping their sparse basis indices."""
    parts, begin, depth = [], 1, 0
    for i in range(1, len(row)-1):
        if row[i] == "(":
            depth += 1
        elif row[i] == ")":
            depth -= 1
        elif row[i] == "," and depth == 0:
            parts.append(row[begin:i].strip())
            begin = i+1
    parts.append(row[begin:-1].strip())
    assert len(parts) % 2 == 0
    indices = [int(x) for x in parts[1::2]]
    assert all(1 <= x <= 240 for x in indices)
    return indices


def extra_data(raw):
    section = raw.split('      type := [ [ "E", 8 ] ],', 1)[1]
    before, after = section.split("      graph :=", 1)
    positions = list(re.finditer(r"num\s*:=\s*(\d+),\s*dim\s*:=\s*(\d+),\s*type\s*:=", before))
    supports = {}
    for n, match in enumerate(positions):
        end = positions[n+1].start() if n+1 < len(positions) else len(before)
        chunk = before[match.end():end]
        lists = base.children(chunk.split("cangens :=", 1)[1])
        supports[int(match[1])] = [[sparse_support(row) for row in base.children(group)] for group in lists[:2]]
    start = after.index("[")
    graph = ast.literal_eval(after[start:base.bracket_end(after, start)])
    return supports, graph


def nullspace(rows, columns=8):
    matrix = [list(map(F, row)) for row in rows]
    pivots = []
    r = 0
    for j in range(columns):
        i = next((i for i in range(r, len(matrix)) if matrix[i][j]), None)
        if i is None:
            continue
        matrix[r], matrix[i] = matrix[i], matrix[r]
        scale = matrix[r][j]
        matrix[r] = [x/scale for x in matrix[r]]
        for i in range(len(matrix)):
            if i != r and matrix[i][j]:
                factor = matrix[i][j]
                matrix[i] = [a-factor*b for a, b in zip(matrix[i], matrix[r])]
        pivots.append(j)
        r += 1
        if r == len(matrix):
            break
    answer = []
    for j in range(columns):
        if j not in pivots:
            vector = [F(0)]*columns
            vector[j] = F(1)
            for i, pivot in enumerate(pivots):
                vector[pivot] = -matrix[i][j]
            answer.append(tuple(vector))
    return answer


def unitary_residual(charge):
    if charge == 0 or charge >= 1:
        return True, "zero" if charge == 0 else "c>=1"
    if charge < 0:
        return False, "negative"
    mprod = 6/(1-charge)
    if mprod.denominator != 1:
        return False, "nonminimal0<c<1"
    disc = 1+4*mprod.numerator
    root = isqrt(disc)
    if root*root == disc and (root-1) % 2 == 0 and (root-1)//2 >= 3:
        return True, "unitary_minimal_m="+str((root-1)//2)
    return False, "nonminimal0<c<1"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--database", type=Path, default=Path("/tmp/hi_cft_sla_sssdb.dat"))
    p.add_argument("--scan", type=Path, default=Path("hi_cft_sixhour_e8_subalgebra_results.json"))
    p.add_argument("--output", type=Path, default=Path("hi_cft_sixhour_e8_subalgebra_refined_results.json"))
    args = p.parse_args()
    raw = args.database.read_text()
    entries = base.entries(raw)
    supports, graph = extra_data(raw)
    previous = json.loads(args.scan.read_text())
    records = {r["database_number"]: r for r in previous["all_semisimple_embeddings"]}
    positive = gap_positive_roots(base.C)
    assert len(positive) == 120 and set(positive) == {r for r in base.roots(base.C) if min(r) >= 0}
    basis_roots = positive+[tuple(-x for x in row) for row in positive]
    e6a2 = [n for n, r in records.items() if [(x["letter"], x["rank"], x["level"]) for x in r["factors"]] == [("A", 2, 1), ("E", 6, 1)]]
    assert len(e6a2) == 1
    adjacency = defaultdict(set)
    for large, small in graph:
        assert (248 if large == 0 else records[large]["dimension"]) > records[small]["dimension"]
        adjacency[large].add(small)
    contained = set(e6a2)
    todo = list(e6a2)
    while todo:
        node = todo.pop()
        for child in adjacency[node]-contained:
            contained.add(child)
            todo.append(child)
    refined = {}
    for entry in entries:
        number = entry["number"]
        h = entry["coroots"]
        es, fs = supports[number]
        # Strong independent check of the GAP root ordering: each stored
        # raising/lowering term has its required simple-root Cartan weight.
        gram = [[base.dot(a, b) for b in h] for a in h]
        cartan = base.cartan_from_gram(gram)
        for sign, rows in ((1, es), (-1, fs)):
            for j, row in enumerate(rows):
                for index in row:
                    weight = [base.dot(basis_roots[index-1], a) for a in h]
                    assert weight == [sign*cartan[i][j] for i in range(len(h))], (number, j, index)
        support = sorted({index for rows in (es, fs) for row in rows for index in row})
        equations = [[sum(base.C[i][j]*basis_roots[index-1][j] for j in range(8)) for i in range(8)] for index in support]
        torus = nullspace(equations)
        row = {"database_number": number,
               "lies_in_E6_1_A2_1_by_inclusion_graph": number in contained,
               "explicit_commuting_Cartan_torus_dimension": len(torus),
               "explicit_commuting_Cartan_basis": [[str(x) for x in a] for a in torus],
               "centralizer_rank_lower_bound": len(torus),
               "centralizer_rank_upper_bound": 8-len(h)}
        if entry["dimension"] <= 19:
            centralizer_dimension = records[number]["Lie_centralizer_dimension_exact"]
            zero_roots = [a for a in basis_roots if all(base.dot(a, b) == 0 for b in torus)]
            zero_dimension = base.low_dim_centralizer(cartan, h, zero_roots)
            row["centralizer_zero_torus_weight_dimension"] = zero_dimension
            row["centralizer_rank_upper_bound"] = min(row["centralizer_rank_upper_bound"], centralizer_dimension)
            if zero_dimension == len(torus):
                row["centralizer_rank_exact"] = len(torus)
                row["centralizer_rank_upper_bound"] = len(torus)
            else:
                # Z_c(S) is reductive with S in its center. If its remaining
                # dimension is1or2 it is necessarily abelian too.
                if zero_dimension-len(torus) <= 2:
                    row["centralizer_rank_exact"] = zero_dimension
                    row["centralizer_rank_lower_bound"] = zero_dimension
                    row["centralizer_rank_upper_bound"] = zero_dimension
        refined[number] = row
    assert refined[1]["centralizer_rank_exact"] == 7
    assert refined[69]["centralizer_rank_exact"] == 0
    full = []
    for old in previous["all_current_W1_candidate_superset"]:
        row = old.copy()
        number, abelian = row["semisimple_database_number"], row["abelian_rank"]
        if number:
            info = refined[number]
            row["passes_torus_necessary_test"] = abelian <= info["centralizer_rank_upper_bound"]
            row["toral_completion_proved_in_E8"] = abelian <= info["centralizer_rank_lower_bound"]
            row["passes_E6_A2_semisimple_containment"] = info["lies_in_E6_1_A2_1_by_inclusion_graph"]
        else:
            row.update(passes_torus_necessary_test=True, toral_completion_proved_in_E8=True,
                       passes_E6_A2_semisimple_containment=True)
        ok, reason = unitary_residual(F(row["residual_c"]))
        row["passes_residual_Virasoro_unitarity"] = ok
        row["residual_Virasoro_class"] = reason
        row["passes_all_current_necessary_tests"] = all(row[key] for key in (
            "passes_torus_necessary_test", "passes_E6_A2_semisimple_containment",
            "passes_residual_Virasoro_unitarity", "passes_grade2_necessary_test"))
        full.append(row)
    denominator = []
    for old in previous["reductive_denominator_candidate_superset"]:
        row = old.copy()
        number, abelian = row["semisimple_database_number"], row["abelian_rank"]
        if number:
            info = refined[number]
            row["passes_torus_necessary_test"] = abelian <= info["centralizer_rank_upper_bound"]
            row["toral_completion_proved_in_E8"] = abelian <= info["centralizer_rank_lower_bound"]
            row["semisimple_contained_in_E6_A2"] = info["lies_in_E6_1_A2_1_by_inclusion_graph"]
        else:
            row.update(passes_torus_necessary_test=True, toral_completion_proved_in_E8=True,
                       semisimple_contained_in_E6_A2=True)
        denominator.append(row)
    result = {"base_scan": str(args.scan), "E6_A2_database_number": e6a2[0],
              "E6_A2_contained_semisimple_embedding_count": len(contained),
              "centralizer_certificates": list(refined.values()),
              "full_W1_refined_candidates": full, "denominator_refined_candidates": denominator,
              "scope": "All filters are necessary. The torus is certified in E8; simultaneous containment of its completion in the E6+A2 fixed algebra needs a separate certificate. No Hg action is constructed."}
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"full_W1_before": len(full),
        "full_W1_after": sum(row["passes_all_current_necessary_tests"] for row in full),
        "torus_excluded": sum(not row["passes_torus_necessary_test"] for row in full),
        "alpha_containment_excluded": sum(not row["passes_E6_A2_semisimple_containment"] for row in full),
        "Virasoro_excluded": sum(not row["passes_residual_Virasoro_unitarity"] for row in full),
        "small_centralizers_rank_certified": sum("centralizer_rank_exact" in r for r in refined.values()),
        "output": str(args.output)}), flush=True)


if __name__ == "__main__":
    main()
