"""Exact finite combinatorial certificates for unitary path-error bounds.

The parameter is the number of tensor factors, not an HI group order.
After gauging a spanning tree to identity, each remaining rotation is
bounded using one face and earlier rotations. All recorded costs are <= 1.
"""

from collections import deque
from itertools import combinations
import json
from pathlib import Path

from hi_pentagon_stability import trees, rotations, intervals


def build(n):
    ts = trees(0, n)
    index = {t: i for i, t in enumerate(ts)}
    adj = {i: {index[s] for s in rotations(t)} for i, t in enumerate(ts)}
    edges = sorted({tuple(sorted((i, j))) for i in adj for j in adj[i]})
    edge_id = {edge: i + 1 for i, edge in enumerate(edges)}
    proper = sorted(set.union(*(intervals(t) for t in ts))
                    - {(0, n)} - {(i, i + 1) for i in range(n)})
    face_sets = set()
    for fixed in combinations(proper, n - 4):
        vertices = frozenset(i for i, t in enumerate(ts) if set(fixed) <= intervals(t))
        if len(vertices) in (4, 5) and all(len(adj[i] & vertices) == 2 for i in vertices):
            face_sets.add(vertices)
    faces = []
    for vertices in sorted(face_sets, key=lambda s: tuple(sorted(s))):
        cycle = [min(vertices)]
        while len(cycle) < len(vertices):
            cycle.append(min((adj[cycle[-1]] & vertices) - set(cycle)))
        cycle.append(cycle[0])
        words = [edge_id[tuple(sorted((i, j)))] * (1 if i < j else -1)
                 for i, j in zip(cycle, cycle[1:])]
        faces.append(words)
    seen, queue, costs = {0}, deque([0]), {}
    while queue:
        u = queue.popleft()
        for v in sorted(adj[u]):
            if v not in seen:
                seen.add(v)
                queue.append(v)
                costs[edge_id[tuple(sorted((u, v)))]] = 0
    tree_edges = sorted(costs)
    steps = []
    while len(costs) < len(edges):
        options = []
        for k, face in enumerate(faces):
            unknown = [abs(e) for e in face if abs(e) not in costs]
            if len(unknown) == 1:
                cost = int(len(face) == 5) + sum(costs[abs(e)] for e in face if abs(e) in costs)
                options.append((cost, unknown[0], k))
        assert options, "no triangular elimination step available"
        cost, edge, face_id = min(options)
        costs[edge] = cost
        steps.append({"edge": edge, "face": face_id, "cost": cost})
    assert max(costs.values()) == 1
    return {"tensor_factors": n, "vertices": len(ts), "edges": edges,
            "faces": faces, "tree_edges": tree_edges, "steps": steps}


def replay(data):
    n, vertices = data["tensor_factors"], data["vertices"]
    edges = [tuple(e) for e in data["edges"]]
    ts = trees(0, n)
    index = {t: i for i, t in enumerate(ts)}
    assert len(ts) == vertices
    expected = {tuple(sorted((i, index[s]))) for i, t in enumerate(ts) for s in rotations(t)}
    assert set(edges) == expected and len(edges) == len(expected)
    proper_intervals = [intervals(t) - {(0, n)} - {(i, i + 1) for i in range(n)} for t in ts]
    costs = {e: 0 for e in data["tree_edges"]}
    assert len(costs) == vertices - 1
    adj = {v: set() for v in range(vertices)}
    for e in costs:
        a, b = edges[e - 1]
        adj[a].add(b)
        adj[b].add(a)
    seen, queue = {0}, deque([0])
    while queue:
        for v in adj[queue.popleft()]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    assert len(seen) == vertices
    for face in data["faces"]:
        assert len(face) in (4, 5)
        arrows = [edges[abs(e) - 1] if e > 0 else tuple(reversed(edges[abs(e) - 1])) for e in face]
        assert all(arrows[i][1] == arrows[(i + 1) % len(arrows)][0] for i in range(len(arrows)))
        vs = {a for a, _ in arrows}
        assert len(vs) == len(face)
        fixed = set.intersection(*(proper_intervals[v] for v in vs))
        assert len(fixed) == n - 4
        assert {i for i, ints in enumerate(proper_intervals) if fixed <= ints} == vs
    for step in data["steps"]:
        edge = step["edge"]
        face = data["faces"][step["face"]]
        assert [abs(e) for e in face if abs(e) not in costs] == [edge]
        cost = int(len(face) == 5) + sum(costs[abs(e)] for e in face if abs(e) != edge)
        assert cost == step["cost"] <= 1
        costs[edge] = cost
    assert set(costs) == set(range(1, len(edges) + 1))
    print("EXACT_PATH_CERTIFICATE", n, "tensor factors;", vertices, "vertices;", len(edges),
          "edges;", len(data["faces"]), "faces;", len(data["steps"]), "eliminations; max cost", max(costs.values()))


if __name__ == "__main__":
    target = Path(__file__).with_name("hi_associahedron_path_bound_certificates.json")
    target.write_text(json.dumps([build(n) for n in (4, 5, 6, 7)], indent=2) + "\n")
    for data in json.loads(target.read_text()):
        replay(data)
    print("ALL EXACT PATH CERTIFICATES PASSED; THIS IS NOT AN HI EXISTENCE SEARCH")
