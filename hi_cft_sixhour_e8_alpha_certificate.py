"""Sufficient exact simultaneous fixed-current certificates in E8.

Enumerate the6561 elements of its maximal torus of exponent3. No dense Lie
algebra is built. A failed toral search is NOT an exclusion of an embedding.
Run in the shared numerical slot with the safe launcher and128MiB AS.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import resource
import hashlib

import hi_cft_sixhour_e8_subalgebra_scan as base
import hi_cft_sixhour_e8_subalgebra_refine as refine


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database', type=Path, default=Path('/tmp/hi_cft_sla_sssdb.dat'))
    parser.add_argument('--refined', type=Path, default=Path('hi_cft_sixhour_e8_subalgebra_refined_results.json'))
    parser.add_argument('--characters', type=Path, default=Path('hi_cft_sixhour_e8_character_results.json'))
    parser.add_argument('--output', type=Path, default=Path('hi_cft_sixhour_e8_alpha_results.json'))
    args = parser.parse_args()
    limit = resource.getrlimit(resource.RLIMIT_AS)[0]
    if limit == resource.RLIM_INFINITY or limit > 128*1024**2:
        raise RuntimeError('Use the coordinated safe launcher with128MiB AS')
    raw = args.database.read_text()
    supports, unused = refine.extra_data(raw)
    del unused, raw
    refined = json.loads(args.refined.read_text())
    certificates = {row['database_number']: row for row in refined['centralizer_certificates']}
    characters = json.loads(args.characters.read_text())
    positive = refine.gap_positive_roots(base.C)
    assert len(positive) == 120
    weights = [tuple(sum(base.C[i][j]*root[j] for j in range(8)) % 3 for i in range(8))
               for root in positive]
    distribution, three_b = Counter(), []
    for vector in product(range(3), repeat=8):
        bits = sum(1 << index for index, weight in enumerate(weights)
                   if sum(a*b for a, b in zip(vector, weight)) % 3 == 0)
        fixed_roots = 2*bits.bit_count()
        distribution[fixed_roots] += 1
        if fixed_roots == 78:
            half_norm = base.dot(vector, vector)/2
            assert half_norm.denominator == 1 and half_norm.numerator % 3 == 0
            three_b.append((vector, bits))
    assert sum(distribution.values()) == 3**8 and distribution[240] == 1
    # Independently recover simple roots of one fixed root system. Its two
    # components have Dynkin diagrams E6 and A2, hence dimension8+78=86.
    fixed = {root for index, root in enumerate(positive) if three_b[0][1] >> index & 1}
    simple = [root for root in fixed if not any(
        tuple(a-b for a, b in zip(root, beta)) in fixed for beta in fixed)]
    graph = [{j for j, beta in enumerate(simple) if j != i and base.dot(root, beta) != 0}
             for i, root in enumerate(simple)]
    components, unseen = [], set(range(len(simple)))
    while unseen:
        seen, todo = set(), [next(iter(unseen))]
        while todo:
            node = todo.pop()
            if node not in seen:
                seen.add(node); todo.extend(graph[node]-seen)
        unseen -= seen; components.append(sorted(seen))
    assert sorted(map(len, components)) == [2, 6]
    big = next(component for component in components if len(component) == 6)
    center = next(node for node in big if len(graph[node]) == 3)
    arms = []
    for neighbor in graph[center]:
        previous, node, length = center, neighbor, 1
        while graph[node]-{previous}:
            following, = graph[node]-{previous}
            previous, node = node, following; length += 1
        arms.append(length)
    assert sorted(arms) == [1, 2, 2]
    rows = []
    for candidate in characters['candidate_rows']:
        if not candidate['passes_all_including_small_residual_field']:
            continue
        row = {key: candidate[key] for key in ('W1_dimension', 'semisimple_database_number',
            'abelian_rank', 'factor_description', 'residual_c')}
        number = row['semisimple_database_number']
        mask = 0
        if number:
            for generators in supports[number]:
                for support in generators:
                    for index in support:
                        mask |= 1 << ((index-1) % 120)
            torus_dimension = certificates[number]['explicit_commuting_Cartan_torus_dimension']
        else:
            torus_dimension = 8
        witness = next((vector for vector, bits in three_b if mask & ~bits == 0), None)
        row.update(explicit_ambient_Cartan_completion_available=row['abelian_rank'] <= torus_dimension,
            toral_three_B_witness_in_E8_coroot_coordinates=witness,
            simultaneous_full_current_fixed_certificate=(witness is not None and row['abelian_rank'] <= torus_dimension))
        rows.append(row)
    result = {'database_sha256': hashlib.sha256(args.database.read_bytes()).hexdigest(),
        'fixed_root_count_distribution': dict(sorted(distribution.items())),
        'three_B_toral_element_count': len(three_b),
        'sample_fixed_root_system_simple_roots': simple,
        'sample_fixed_root_system_components': components,
        'sample_E6_arm_lengths': sorted(arms), 'candidate_rows': rows,
        'simultaneous_certified_count': sum(row['simultaneous_full_current_fixed_certificate'] for row in rows),
        'scope': 'Sufficient certificates only. A failed search is not an exclusion. The abelian currents can be chosen inside the recorded commuting Cartan torus. No Haagerup noninvertible action or chain-to-coset mapping is constructed.'}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('fixed_root_count_distribution',
        'three_B_toral_element_count', 'simultaneous_certified_count')}), flush=True)


if __name__ == '__main__':
    main()
