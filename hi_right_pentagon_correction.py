"""Exact transport constants and off-solution right-cochain regressions.

The correction theorem is uniform; the numerical examples below use only
Fibonacci fusion spaces to test the formulas. They are not new HI examples.
"""

from collections import deque
from fractions import Fraction
from itertools import product
import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm

from hi_associahedron_path_bound import replay
from hi_pentagon_stability import trees, rotations, inverse, reduce_word
from hi_unitary_handle_bound import (
    Trial, Morph, ONE, TAU, SIMPLES, PHI, GLOBAL, DIMS, identity, zero, tensor,
    tensor_obj, inclusion,
)


def transport_certificate():
    root = Path(__file__).parent
    lines = (root / "hi_pentagon_stability_results.txt").read_text().splitlines()
    face_rows = [json.loads(s[5:]) for s in lines if s.startswith("FACE ")]
    edges = {int(k): tuple(v) for k, v in json.loads(next(s[6:] for s in lines if s.startswith("EDGES "))).items()}
    product_order = json.loads(next(s[14:] for s in lines if s.startswith("PRODUCT_ORDER ")))
    factors = {x["id"]: tuple(x["whisker"]) + tuple(x["word"]) + inverse(x["whisker"]) for x in face_rows}
    assert reduce_word(tuple(e for k in product_order for e in factors[k])) == ()
    path_data = next(x for x in json.loads((root / "hi_associahedron_path_bound_certificates.json").read_text())
                     if x["tensor_factors"] == 5)
    replay(path_data)
    assert list(edges.values()) == [tuple(e) for e in path_data["edges"]]
    costs = {e: 0 for e in path_data["tree_edges"]}
    costs.update({x["edge"]: x["cost"] for x in path_data["steps"]})
    ts = trees(0, 5)
    index = {t: i for i, t in enumerate(ts)}
    adj = {i: {index[s] for s in rotations(t)} for i, t in enumerate(ts)}
    edge_id = {v: k for k, v in edges.items()}
    right_base = {0: 5, 1: 2, 2: 1, 3: 0, 7: 9, 8: 0}
    standard = {0: (3,), 1: (2,), 2: (1,), 3: (), 7: (1, 4, 9), 8: ()}
    signs = {0: -1, 1: 1, 2: -1, 3: 1, 7: -1, 8: 1}
    cost_sum = 0
    for row in face_rows:
        k = row["id"]
        if k not in right_base:
            continue
        w = tuple(row["word"])
        arrows = [edges[abs(e)] if e > 0 else edges[abs(e)][::-1] for e in w]
        vs, start = {a for a, _ in arrows}, arrows[0][0]
        queue = deque([(start,)])
        while queue[0][-1] != right_base[k]:
            path = queue.popleft()
            queue.extend(path + (v,) for v in sorted(adj[path[-1]] & vs) if v not in path)
        path = queue[0]
        shift = tuple(edge_id[tuple(sorted((a, b)))] * (1 if a < b else -1)
                      for a, b in zip(path, path[1:]))
        right_loop = reduce_word(inverse(shift) + w + shift)
        assert len(right_loop) == 5
        # Check against the standard right-based pentagon on the face atoms.
        begin, end = row["interval"]
        if end - begin == 2:
            atoms = list(range(begin)) + [(begin, begin + 1)] + list(range(end, 5))
            embed = lambda t: t
        else:
            atoms = list(range(begin, end))
            embed = (lambda t: (t, 4)) if begin == 0 else (lambda t: (0, t))
        a, b, c, d = atoms
        vertices = [(a, (b, (c, d))), ((a, b), (c, d)), (((a, b), c), d),
                    ((a, (b, c)), d), (a, ((b, c), d)), (a, (b, (c, d)))]
        vertices = [index[embed(t)] for t in vertices]
        canonical = tuple(edge_id[tuple(sorted((a, b)))] * (1 if a < b else -1)
                          for a, b in zip(vertices, vertices[1:]))
        assert right_loop == (canonical if signs[k] == 1 else inverse(canonical))
        old = reduce_word((3,) + tuple(row["whisker"]) + shift)
        comparison_loop = reduce_word(old + inverse(standard[k]))
        cost = sum(costs[abs(e)] for e in comparison_loop)
        cost_sum += cost
        print("RIGHT_COFACE", json.dumps({"face": k, "old_transport": old,
                                         "standard_transport": standard[k],
                                         "comparison_loop": comparison_loop, "cost": cost}))
    assert cost_sum == 5
    print("EXACT_BIANCHI_TRANSPORT_BOUND", 2 * cost_sum, "times q")
    assert Fraction(4, 3) <= Fraction(7, 6) ** 2
    remainder = 15 * Fraction(4, 3) + 21 * Fraction(7, 6) + Fraction(25, 2)
    assert remainder == 57
    e0 = Fraction(1, 130)
    assert (4 * 2 + 57) * e0 == Fraction(1, 2)
    assert e0 + 5 * 2 * e0 < 1
    assert 2 * Fraction(1, 4) < 1
    print("EXACT_CORRECTION_CONSTANTS: beta=57; e0<=1/130 gives eta<=1/2; displacement<=2e0")


def right_obj(objects):
    out = objects[-1]
    for a in reversed(objects[:-1]):
        out = tensor_obj(a, out)
    return out


def right_tensor(morphisms):
    out = morphisms[-1]
    for f in reversed(morphisms[:-1]):
        out = tensor(f, out)
    return out


def cochain(c, objects):
    """Natural extension of a normalized Fibonacci cochain."""
    if any(a[1] == 0 for a in objects):
        return zero(right_obj(objects))
    assert all(a[1] == 1 for a in objects)
    inc = right_tensor([inclusion(a, 1) for a in objects])
    return inc @ c @ inc.adjoint()


def append(trial, head, last):
    if len(head) == 1:
        return identity(tensor_obj(head[0], last))
    return tensor(identity(head[0]), append(trial, head[1:], last)) @ trial.F(head[0], right_obj(head[1:]), last)


def cofaces(trial, c, m, objects=None):
    objects = (TAU,) * (m + 1) if objects is None else tuple(objects)
    out = [tensor(identity(objects[0]), cochain(c, objects[1:]))]
    for pos in range(m):
        merged = objects[:pos] + (tensor_obj(objects[pos], objects[pos + 1]),) + objects[pos + 2:]
        value = cochain(c, merged)
        if pos < m - 1:
            f = trial.F(objects[pos], objects[pos + 1], right_obj(objects[pos + 2:]))
            for obj in reversed(objects[:pos]):
                f = tensor(identity(obj), f)
            value = f @ value @ f.adjoint()
        out.append(value)
    f = append(trial, objects[:-1], objects[-1])
    out.append(f @ tensor(cochain(c, objects[:-1]), identity(objects[-1])) @ f.adjoint())
    return out


def differential(trial, c, m):
    result = zero(right_obj((TAU,) * (m + 1)))
    for i, value in enumerate(cofaces(trial, c, m)):
        result = result + value.scale((-1) ** i)
    return result


def average(trial, c, m):
    # The unit-label summand vanishes for a normalized cochain.
    return trial.trace(1, right_obj((TAU,) * (m - 1)), c).scale(PHI / GLOBAL)


def right_pentagon(trial):
    a = b = c = d = TAU
    ab = bc = cd = tensor_obj(TAU, TAU)
    long = tensor(identity(a), trial.F(b, c, d)) @ trial.F(a, bc, d) @ tensor(trial.F(a, b, c), identity(d))
    short = trial.F(a, b, cd) @ trial.F(ab, c, d)
    return long @ short.adjoint()


def skew(c):
    return (c - c.adjoint()).scale(0.5)


def random_skew(rng, m):
    obj = right_obj((TAU,) * m)
    blocks = []
    for d in obj:
        a = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        blocks.append((a - a.conj().T) / 2)
    result = Morph(obj, obj, tuple(blocks))
    return result.scale(1 / result.norm())


def update(trial, u, scale):
    return Trial(expm(scale * u.blocks[1]) @ trial.matrix,
                 np.exp(scale * u.blocks[0][0, 0]) * trial.scalar)


def regressions():
    rng = np.random.default_rng(8701)
    standard = np.array([[1 / PHI, 1 / np.sqrt(PHI)], [1 / np.sqrt(PHI), -1 / PHI]])
    for scale in (0.0, 0.0005, 0.01, 0.1):
        trial = Trial(np.diag(np.exp(1j * scale * rng.normal(size=2))) @ standard
                      @ np.diag(np.exp(1j * scale * rng.normal(size=2))), np.exp(1j * 0.73 * scale))
        p = right_pentagon(trial)
        q = (p - identity(p.source)).norm()
        r = skew(p)
        e = r.norm()
        mu = max(trial.imbalance(b) for b in range(2))
        y, u = random_skew(rng, 4), random_skew(rng, 3)
        averaged_faces = [zero(y.source) for _ in range(6)]
        for a in range(2):
            for j, face in enumerate(cofaces(trial, y, 4, (SIMPLES[a],) + (TAU,) * 4)):
                averaged_faces[j] = averaged_faces[j] + trial.trace(a, y.source, face).scale(DIMS[a] / GLOBAL)
        faces_after_average = cofaces(trial, average(trial, y, 4), 3)
        middle_error = max((averaged_faces[j] - faces_after_average[j - 1]).norm() for j in (2, 3, 4))
        assert (averaged_faces[0] - y).norm() < 1e-10
        assert middle_error < 1e-10
        handle_error = (averaged_faces[1] - faces_after_average[0]).norm()
        boundary_error = (averaged_faces[5] - faces_after_average[4]).norm()
        assert handle_error <= 4 * q + mu + 1e-10
        assert boundary_error <= 2 * q + 1e-10
        homotopy = y - differential(trial, average(trial, y, 4), 3) - average(trial, differential(trial, y, 4), 5)
        assert homotopy.norm() <= 6 * q + mu + 1e-10
        fs = cofaces(trial, u, 3)
        plus, minus = fs[0] + fs[2] + fs[4], fs[1] + fs[3]
        derivative = skew(plus @ p - p @ minus)
        assert (derivative - differential(trial, u, 3)).norm() <= 5 * q + 1e-10
        eps = 1e-6
        finite_difference = (skew(right_pentagon(update(trial, u, eps)))
                             - skew(right_pentagon(update(trial, u, -eps)))).scale(1 / (2 * eps))
        assert (derivative - finite_difference).norm() < 1e-8
        bianchi = differential(trial, r, 4).norm()
        assert bianchi <= 15 * q * q + 10 * q * e + 1e-10
        if scale == 0:
            assert homotopy.norm() < 1e-11
        print("RIGHT_COCHAIN_REGRESSION", scale, "q", q, "homotopy", homotopy.norm(),
              "homotopy_bound", 6 * q + mu, "Bianchi", bianchi,
              "Bianchi_bound", 15 * q * q + 10 * q * e,
              "exact_middle", middle_error, "handle", handle_error,
              "boundary", boundary_error, flush=True)
        if scale == 0.0005:
            initial = trial
    trial = initial
    e0 = skew(right_pentagon(trial)).norm()
    q0 = (right_pentagon(trial) - identity(right_pentagon(trial).source)).norm()
    assert q0 < 1 / 130
    distance = 0.0
    for step in range(8):
        p = right_pentagon(trial)
        r = skew(p)
        e = r.norm()
        mu = max(trial.imbalance(b) for b in range(2))
        print("CORRECTION", step, "q", (p - identity(p.source)).norm(), "e", e,
              "mu", mu, "path_length", distance, flush=True)
        if e < 1e-12:
            break
        assert mu <= 4 * distance + 1e-10
        h = average(trial, r, 4)
        assert h.norm() <= e + 1e-10
        new = update(trial, h, -1)
        enew = skew(right_pentagon(new)).norm()
        assert enew <= mu * e + 57 * e**2 + 1e-10
        assert enew <= e / 2 + 1e-10
        distance += h.norm()
        assert distance <= 2 * e0 + 1e-10
        trial = new
    assert skew(right_pentagon(trial)).norm() < 1e-10
    print("ALL RIGHT-COCHAIN AND CORRECTION REGRESSIONS PASSED; NO NEW HI EXISTENCE CLAIM")


if __name__ == "__main__":
    transport_certificate()
    regressions()
