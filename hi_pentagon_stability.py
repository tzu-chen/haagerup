"""Exact K5 boundary certificate and bounded pentagon-defect regressions.

The free-word certificate uses no pentagon relation. Numerical matrix tests
check the stated norm estimates; they are not HI existence certificates.
"""

from __future__ import annotations

from functools import cache
from fractions import Fraction
import json

import numpy as np
from scipy.linalg import expm


@cache
def trees(start: int, stop: int):
    if stop - start == 1:
        return (start,)
    return tuple((a, b) for cut in range(start + 1, stop)
                 for a in trees(start, cut) for b in trees(cut, stop))


def show(t):
    return chr(97 + t) if isinstance(t, int) else f"({show(t[0])}{show(t[1])})"


def rotations(t):
    if isinstance(t, int):
        return []
    a, b = t
    out = []
    if isinstance(a, tuple):
        out.append((a[0], (a[1], b)))
    if isinstance(b, tuple):
        out.append(((a, b[0]), b[1]))
    out.extend((s, b) for s in rotations(a))
    out.extend((a, s) for s in rotations(b))
    return out


def intervals(t):
    if isinstance(t, int):
        return {(t, t + 1)}
    s = intervals(t[0]) | intervals(t[1])
    return s | {(min(a for a, _ in s), max(b for _, b in s))}


def inverse(word):
    return tuple(-s for s in reversed(word))


def reduce_word(word):
    out = []
    for s in word:
        if out and out[-1] == -s:
            out.pop()
        else:
            out.append(s)
    return tuple(out)


def certificate():
    ts = trees(0, 5)
    index = {t: i for i, t in enumerate(ts)}
    adj = {i: {index[s] for s in rotations(t)} for i, t in enumerate(ts)}
    edges = sorted({tuple(sorted((i, j))) for i in adj for j in adj[i]})
    edge_index = {e: i + 1 for i, e in enumerate(edges)}

    def word(path):
        return tuple(edge_index[tuple(sorted((a, b)))] * (1 if a < b else -1)
                     for a, b in zip(path, path[1:]))

    faces = []
    for length in (2, 3, 4):
        for start in range(6 - length):
            interval = (start, start + length)
            vs = {i for i, t in enumerate(ts) if interval in intervals(t)}
            cycle = [min(vs)]
            while len(cycle) < len(vs):
                nxt = sorted((adj[cycle[-1]] & vs) - set(cycle))
                assert nxt
                cycle.append(nxt[0])
            assert cycle[0] in adj[cycle[-1]]
            assert all(len(adj[v] & vs) == 2 for v in vs)
            faces.append((interval, tuple(cycle + [cycle[0]])))
    assert (len(ts), len(edges), len(faces)) == (14, 21, 9)
    assert sorted(len(c) - 1 for _, c in faces) == [4] * 3 + [5] * 6
    assert all(sum(abs(e) in map(abs, word(c)) for _, c in faces) == 2
               for e in range(1, 22))

    # Orient neighboring faces oppositely along their common edge.
    oriented = {0: faces[0][1]}
    while len(oriented) < 9:
        added = False
        for k, (_, cycle) in enumerate(faces):
            if k in oriented:
                continue
            for old in list(oriented.values()):
                shared = set(map(abs, word(cycle))) & set(map(abs, word(old)))
                if shared:
                    assert len(shared) == 1
                    e = shared.pop()
                    s = next(v for v in word(cycle) if abs(v) == e)
                    if s in word(old):
                        cycle = tuple(reversed(cycle))
                    oriented[k] = cycle
                    added = True
                    break
        assert added
    assert all(sum(word(c).count(e) for c in oriented.values()) == 1
               and sum(word(c).count(-e) for c in oriented.values()) == 1
               for e in range(1, 22))

    # Shell the sphere, retaining the first face's initial vertex on its boundary.
    # If old boundary is p S q and the new face is T S^-1, then
    # new boundary = p T q = (p (T S^-1) p^-1) (old boundary).
    def shell(boundary, used, factors, steps):
        if len(used) == 8:
            k = next(k for k in range(9) if k not in used)
            target = inverse(word(boundary))
            cycle = oriented[k]
            words = [word(cycle[j:-1] + cycle[:j + 1]) for j in range(len(cycle) - 1)]
            if target not in words:
                return None
            return [(k, target)] + factors, steps + [(k, (), target)]
        for k, cycle in oriented.items():
            if k in used:
                continue
            for i in range(len(boundary) - 1):
                for j in range(i + 1, len(boundary)):
                    shared_path = boundary[i:j + 1]
                    if len(shared_path) >= len(cycle):
                        continue
                    u, v = shared_path[0], shared_path[-1]
                    if u not in cycle or v not in cycle:
                        continue
                    pos = cycle.index(u)
                    rotated = cycle[pos:-1] + cycle[:pos + 1]
                    pos_v = rotated.index(v)
                    if rotated[pos_v:] != tuple(reversed(shared_path)):
                        continue
                    replacement = rotated[:pos_v + 1]
                    new = boundary[:i] + replacement + boundary[j + 1:]
                    if len(set(new[:-1])) != len(new) - 1 or new[0] != new[-1]:
                        continue
                    p = word(boundary[:i + 1])
                    face_word = word(rotated)
                    factor = p + face_word + inverse(p)
                    assert reduce_word(factor + word(boundary)) == word(new)
                    ans = shell(new, used | {k}, [(k, factor)] + factors,
                                steps + [(k, p, face_word)])
                    if ans is not None:
                        return ans
        return None

    first = oriented[0]
    ans = shell(first, {0}, [(0, word(first))], [(0, (), word(first))])
    assert ans is not None
    factors, steps = ans
    assert sorted(k for k, _ in factors) == list(range(9))
    assert reduce_word(tuple(s for _, factor in factors for s in factor)) == ()
    print("VERTICES", json.dumps({i: show(t) for i, t in enumerate(ts)}))
    print("EDGES", json.dumps({i + 1: e for i, e in enumerate(edges)}))
    for k, p, w in steps:
        print("FACE", json.dumps({"id": k, "interval": faces[k][0],
                                   "length": len(w), "whisker": p, "word": w}))
    print("PRODUCT_ORDER", [k for k, _ in factors])
    print("EXACT_FREE_WORD_BOUNDARY_PASSED: six pentagons, three squares, empty reduced word")
    transport_lengths = []
    for k, p, w in steps:
        interval, cycle = faces[k]
        if len(cycle) != 6:
            continue
        start, stop = interval
        if stop - start == 2:
            atoms = list(range(start)) + [(start, start + 1)] + list(range(stop, 5))
            embed = lambda t: t
        else:
            assert stop - start == 4
            atoms = list(range(start, stop))
            embed = (lambda t: (t, 4)) if start == 0 else (lambda t: (0, t))
        a, b, c, d = atoms
        standard = [(((a, b), c), d), ((a, (b, c)), d), (a, ((b, c), d)),
                    (a, (b, (c, d))), ((a, b), (c, d)), (((a, b), c), d)]
        canonical = tuple(index[embed(t)] for t in standard)
        cw = word(canonical)
        edge = edges[abs(w[0]) - 1]
        face_start = edge[0] if w[0] > 0 else edge[1]
        paths = [(face_start,)]
        while paths[0][-1] != canonical[0]:
            path = paths.pop(0)
            paths.extend(path + (v,) for v in sorted(adj[path[-1]] & set(cycle))
                         if v not in path)
        q = word(paths[0])
        assert len(q) <= 2
        signs = [s for s in (1, -1)
                 if reduce_word(q + (cw if s == 1 else inverse(cw)) + inverse(q)) == w]
        assert len(signs) == 1
        transported = p + q
        transport_lengths.append(len(transported))
        print("CANONICAL_FACE", json.dumps({"id": k, "sign": signs[0],
                                          "transport": transported, "pentagon": cw}))
    assert sum(transport_lengths) == 28
    print("EXACT_TRANSPORT_LENGTH_SUM", sum(transport_lengths), "B_LIPSCHITZ_BOUND", 56)
    # Dimension-independent sufficient constants in the proved correction test.
    radius, e0 = Fraction(1, 200), Fraction(1, 1000)
    theta = Fraction(1, 4) + (25 + 56) * radius
    beta = 20 + Fraction(25, 2)
    eta = theta + beta * e0
    displacement = e0 / (1 - eta)
    assert eta == Fraction(11, 16)
    assert displacement == Fraction(2, 625) < radius
    assert Fraction(1, 2) + 5 * radius < 1
    assert Fraction(16, 5) * Fraction(1, 4) == Fraction(4, 5) < 1
    print("EXACT_CORRECTION_CONSTANTS", "radius", radius, "e0", e0,
          "eta", eta, "displacement", displacement)
    print("EXACT_DUALITY_MARGIN: e0 <= 1/(4d) gives displacement <= 4/(5d) < 1/d")
    return edges, faces, factors, word


def op(a):
    return float(np.linalg.norm(a, 2))


def skew(a):
    return (a - a.conj().T) / 2


def matrix_checks(edges, faces, factors, word):
    rng = np.random.default_rng(851)
    worst_ratio = 0.0
    for dim in (2, 3, 7):
        ident = np.eye(dim, dtype=complex)
        for scale in (0.002, 0.02, 0.1):
            matrices = {}
            for k in range(1, len(edges) + 1):
                x = skew(rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim)))
                matrices[k] = expm(scale * x / op(x))
            # The three squares are disjoint. Solving for one edge on each
            # makes their holonomies exactly identity, with no pentagon imposed.
            for _, cycle in faces:
                if len(cycle) == 5:
                    w = word(cycle)
                    rest = ident.copy()
                    for s in w[:-1]:
                        rest = rest @ (matrices[abs(s)] if s > 0 else matrices[abs(s)].conj().T)
                    matrices[abs(w[-1])] = rest.conj().T if w[-1] > 0 else rest

            def evaluate(w):
                result = ident.copy()
                for s in w:
                    result = result @ (matrices[abs(s)] if s > 0 else matrices[abs(s)].conj().T)
                return result

            ps = []
            for k, factor in factors:
                p = evaluate(factor)
                if len(faces[k][1]) == 5:
                    assert op(p - ident) < 1e-12
                else:
                    ps.append(p)
            prod = ident.copy()
            for p in ps:
                prod = prod @ p
            assert op(prod - ident) < 1e-11
            error = max(op(p - ident) for p in ps)
            linear = op(sum((p - ident for p in ps), np.zeros_like(ident)))
            assert linear <= 15 * error**2 + 1e-11
            residual = max(op(skew(p)) for p in ps)
            bianchi = op(sum((skew(p) for p in ps), np.zeros_like(ident)))
            assert error < 1
            assert error <= 2 / np.sqrt(3) * residual + 1e-11
            assert bianchi <= 20 * residual**2 + 1e-11
            worst_ratio = max(worst_ratio, bianchi / residual**2)
            print("UNITARY_REGRESSION", dim, scale, "q", error, "r", residual,
                  "B_over_r_squared", bianchi / residual**2)

    # Check the five-factor second derivative by an exact Leibniz expansion.
    dim = 4
    us, xs = [], []
    for _ in range(5):
        a = skew(rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim)))
        x = skew(rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim)))
        us.append(expm(a))
        xs.append(x / op(x))
    second = np.zeros((dim, dim), dtype=complex)
    for i in range(5):
        for j in range(5):
            term = np.eye(dim, dtype=complex)
            for k in range(5):
                factor = us[k]
                if k == i:
                    factor = factor @ xs[k]
                if k == j:
                    factor = factor @ xs[k]
                term = term @ factor
            second += term
    assert op(second) <= 25 + 1e-11
    print("FIVE_FACTOR_SECOND_DERIVATIVE", op(second), "bound", 25)
    print("MATRIX_REGRESSIONS_PASSED; max B/r^2", worst_ratio)
    print("NO_HI_EXISTENCE_OR_OFF_SOLUTION_HOMOTOPY_CERTIFIED")


if __name__ == "__main__":
    matrix_checks(*certificate())
