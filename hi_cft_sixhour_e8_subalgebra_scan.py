"""Exact scan of de Graaf/SLA's stored E8 semisimple embeddings.

Reads only sparse Cartan generators and type metadata. No GAP Lie algebra,
248-square structure constants, numerical eigensolve, or floating arithmetic.
Run under the coordinated safe-run guard; input is the public SLA database.
"""
import argparse
import ast
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re


C = [[2 if i == j else 0 for j in range(8)] for i in range(8)]
EDGES = ((0, 2), (2, 3), (1, 3), (3, 4), (4, 5), (5, 6), (6, 7))
for i, j in EDGES:
    C[i][j] = C[j][i] = -1


def bracket_end(text, start):
    assert text[start] == "["
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return i+1
    raise ValueError("Unclosed database list")


def children(text):
    """Return the top-level sublists; don't evaluate GAP coefficient code."""
    start = text.index("[")+1
    result = []
    while start < len(text):
        if text[start] == "[":
            end = bracket_end(text, start)
            result.append(text[start:end])
            start = end
        elif text[start] == "]":
            return result
        else:
            start += 1
    raise ValueError("Malformed list")


def cartan_rows(text):
    result = []
    for row in children(text):
        if re.sub(r"[-0-9/,\s\[\]]", "", row):
            raise ValueError("Nonrational stored Cartan coefficient")
        tokens = re.findall(r"-?\d+(?:/\d+)?", row)
        assert len(tokens) % 2 == 0
        vector = [F(0)]*8
        for a, b in zip(tokens[::2], tokens[1::2]):
            index = int(b)-241
            assert 0 <= index < 8
            vector[index] += F(a)
        result.append(tuple(int(x) if x.denominator == 1 else x for x in vector))
    return result


def entries(text):
    marker = '      type := [ [ "E", 8 ] ],'
    section = text.split(marker, 1)[1].split("      graph :=", 1)[0]
    positions = list(re.finditer(r"num\s*:=\s*(\d+),\s*dim\s*:=\s*(\d+),\s*type\s*:=", section))
    result = []
    for n, match in enumerate(positions):
        end = positions[n+1].start() if n+1 < len(positions) else len(section)
        chunk = section[match.end():end]
        type_start = chunk.index("[")
        types = ast.literal_eval(chunk[type_start:bracket_end(chunk, type_start)])
        generators = chunk.split("cangens :=", 1)[1]
        lists = children(generators)
        assert len(lists) == 3
        h = cartan_rows(lists[2])
        assert len(h) == sum(rank for _, rank in types)
        result.append({"number": int(match[1]), "dimension": int(match[2]),
                       "types": types, "coroots": h})
    assert len(result) == 1183
    assert [x["number"] for x in result] == list(range(1, 1184))
    return result


def dot(a, b):
    return F(2*sum(x*y for x, y in zip(a, b))
             -sum(a[i]*b[j]+a[j]*b[i] for i, j in EDGES))


def lie_data(letter, rank):
    if letter == "A":
        return rank*(rank+2), rank+1
    if letter == "B":
        return rank*(2*rank+1), 2*rank-1
    if letter == "C":
        return rank*(2*rank+1), rank+1
    if letter == "D":
        return rank*(2*rank-1), 2*rank-2
    return {("G", 2): (14, 4), ("F", 4): (52, 9),
            ("E", 6): (78, 12), ("E", 7): (133, 18),
            ("E", 8): (248, 30)}[letter, rank]


def roots(cartan):
    """All simple-coordinate roots, by exact simple reflections."""
    rank = len(cartan)
    found = {tuple(int(i == j) for i in range(rank)) for j in range(rank)}
    todo = list(found)
    while todo:
        a = todo.pop()
        for j in range(rank):
            b = list(a)
            b[j] -= sum(cartan[j][i]*a[i] for i in range(rank))
            b = tuple(b)
            if b not in found:
                found.add(b)
                todo.append(b)
    return sorted(found)


def cartan_from_gram(gram):
    result = []
    for i in range(len(gram)):
        row = []
        for j in range(len(gram)):
            value = 2*gram[i][j]/gram[j][j]
            assert value.denominator == 1
            row.append(int(value))
        result.append(row)
    return result


def low_dim_centralizer(cartan, h, e8_roots):
    """Multiplicity of the trivial module in the restricted adjoint.

    Constant coefficient of ch(adj_E8)*prod_positive(1-e^-beta).
    At Lie dimension<=19 there are at most8 positive roots, so this
    is a small exact finite sum. It gives centralizer DIMENSION, not rank.
    """
    rank = len(h)
    multiplicities = Counter({(0,)*rank: 8})
    for a in e8_roots:
        weight = tuple(dot(a, b) for b in h)
        assert all(x.denominator == 1 for x in weight)
        multiplicities[tuple(map(int, weight))] += 1
    positive = [a for a in roots(cartan) if all(x >= 0 for x in a)]
    assert len(positive) <= 8
    denominator = Counter({(0,)*rank: 1})
    for a in positive:
        weight = tuple(sum(cartan[j][i]*a[i] for i in range(rank)) for j in range(rank))
        updated = denominator.copy()
        for term, coefficient in denominator.items():
            shifted = tuple(x+y for x, y in zip(term, weight))
            updated[shifted] -= coefficient
        denominator = Counter({a: n for a, n in updated.items() if n})
    answer = sum(coefficient*multiplicities[weight] for weight, coefficient in denominator.items())
    assert isinstance(answer, int) and answer >= 0
    return answer


def affine_grade2(current_dimension, factors):
    # First integrable vacuum singular vector appears at grade k+1.
    # For k=1 it is the finite irreducible representation of highest2theta.
    dim2theta = {("A", 1): 5, ("A", 2): 27, ("B", 2): 35,
                 ("C", 2): 35, ("G", 2): 77, ("A", 3): 84}
    nulls = sum(dim2theta[f["letter"], f["rank"]] for f in factors if f["level"] == 1)
    return current_dimension*(current_dimension+3)//2-nulls


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--database", type=Path, default=Path("/tmp/hi_cft_sla_sssdb.dat"))
    p.add_argument("--output", type=Path, default=Path("hi_cft_sixhour_e8_subalgebra_results.json"))
    args = p.parse_args()
    raw = args.database.read_bytes()
    parsed = entries(raw.decode())
    all_roots = roots(C)
    assert len(all_roots) == 240 and all(dot(a, a) == 2 for a in all_roots)
    records = []
    denominator_candidates, full_current_candidates = [], []
    for entry in parsed:
        h = entry["coroots"]
        gram = [[dot(a, b) for b in h] for a in h]
        cartan = cartan_from_gram(gram)
        factors, offset, central = [], 0, F(0)
        for letter, rank in entry["types"]:
            indices = range(offset, offset+rank)
            # Long-root coroots have the shortest norm,2, in standard
            # affine normalization. E8_1 restricts at this embedding index.
            level = min(gram[i][i] for i in indices)/2
            assert level.denominator == 1 and level > 0
            level = int(level)
            dim, dual_coxeter = lie_data(letter, rank)
            charge = F(level*dim, level+dual_coxeter)
            central += charge
            factors.append({"letter": letter, "rank": rank, "level": level,
                            "dimension": dim, "dual_coxeter": dual_coxeter,
                            "c": str(charge)})
            norms = sorted({gram[i][i]/(2*level) for i in indices})
            assert norms == ([F(1)] if letter in "ADE" else [F(1), F(3 if letter == "G" else 2)])
            assert all(gram[i][j] == 0 for i in indices
                       for j in range(offset+rank, len(h)))
            offset += rank
        assert sum(x["dimension"] for x in factors) == entry["dimension"]
        assert 0 < central <= 8
        record = {"database_number": entry["number"], "factors": factors,
                  "dimension": entry["dimension"], "rank": len(h),
                  "Sugawara_c": str(central), "E8_coset_c": str(8-central),
                  "abelian_rank_upper_bound": 8-len(h),
                  "stored_simple_coroots": [[str(x) for x in row] for row in h]}
        if entry["dimension"] <= 19:
            record["Lie_centralizer_dimension_exact"] = low_dim_centralizer(cartan, h, all_roots)
        records.append(record)
        # A conservative COMPLETE superset for reductive subalgebras.
        # Actual abelian rank is bounded by the centralizer rank, not just
        # this ambient-rank bound; retain this distinction in every output.
        for abelian in range(9-len(h)):
            charge = central+abelian
            if charge > 8:
                continue
            if F(11, 2) <= charge <= F(13, 2):
                denominator_candidates.append({
                    "semisimple_database_number": entry["number"],
                    "abelian_rank": abelian, "denominator_c": str(charge),
                    "coset_c": str(8-charge),
                    "current_dimension": entry["dimension"]+abelian,
                    "toral_completion_status": "Necessary rank bound only; actual commuting torus still to verify",
                })
            for target_dimension, W2 in ((6, 120), (19, 198)):
                if entry["dimension"]+abelian != target_dimension:
                    continue
                grade2 = affine_grade2(target_dimension, factors)
                minimum_grade2 = grade2+int(charge < 8)
                full_current_candidates.append({
                    "semisimple_database_number": entry["number"],
                    "abelian_rank": abelian, "W1_dimension": target_dimension,
                    "current_Sugawara_c": str(charge), "residual_c": str(8-charge),
                    "affine_vacuum_grade2": grade2,
                    "including_independent_coset_stress_minimum_grade2": minimum_grade2,
                    "proposed_W_grade2": W2,
                    "passes_grade2_necessary_test": minimum_grade2 <= W2,
                    "toral_completion_status": "Necessary rank bound only",
                })
    # Purely abelian choices are not semisimple database entries.
    for abelian in (6,):
        denominator_candidates.append({"semisimple_database_number": 0,
            "abelian_rank": abelian, "denominator_c": str(abelian),
            "coset_c": str(8-abelian), "current_dimension": abelian,
            "toral_completion_status": "Exists: a rational subspace of the E8 Cartan"})
        full_current_candidates.append({"semisimple_database_number": 0,
            "abelian_rank": abelian, "W1_dimension": 6,
            "current_Sugawara_c": "6", "residual_c": "2",
            "affine_vacuum_grade2": 27,
            "including_independent_coset_stress_minimum_grade2": 28,
            "proposed_W_grade2": 120, "passes_grade2_necessary_test": True,
            "toral_completion_status": "Exists as an E8 current subalgebra; Hg invariance unconstructed"})
    assert records[0]["factors"][0]["level"] == 1
    assert records[0]["Lie_centralizer_dimension_exact"] == 133
    assert records[68]["factors"] == [{
        "letter": "A", "rank": 1, "level": 1240,
        "dimension": 3, "dual_coxeter": 2, "c": str(F(3*1240, 1242))}]
    assert records[68]["Lie_centralizer_dimension_exact"] == 0
    assert any([(f["letter"], f["rank"], f["level"]) for f in row["factors"]]
               == [("F", 4, 1), ("G", 2, 1)] for row in records)
    report = {
        "source": "https://github.com/gap-packages/sla/blob/master/gap/sssdb.dat",
        "database_sha256": hashlib.sha256(raw).hexdigest(),
        "classification": "de Graaf arXiv1004.1972,1183 E8 semisimple subalgebras up to linear equivalence",
        "semisimple_embedding_count": len(records),
        "normalization": "Long E8 roots squared2; minimum simple-coroot squared norm/2 is affine level",
        "all_semisimple_embeddings": records,
        "denominator_window": ["11/2", "13/2"],
        "reductive_denominator_candidate_superset": denominator_candidates,
        "all_current_W1_candidate_superset": full_current_candidates,
        "scope": "Stored semisimple embeddings are actual. Abelian completions marked necessary-only need actual centralizer rank and rational lattice checks. No assertion of a Haagerup action or complete VOA-subalgebra classification.",
    }
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "semisimple_embeddings": len(records),
        "denominator_window_candidate_count": len(denominator_candidates),
        "denominator_window_distinct_coset_c": sorted({x["coset_c"] for x in denominator_candidates}, key=F),
        "full_W1_candidates": len(full_current_candidates),
        "full_W1_passes_grade2": sum(x["passes_grade2_necessary_test"] for x in full_current_candidates),
        "output": str(args.output),
    }), flush=True)


if __name__ == "__main__":
    main()
