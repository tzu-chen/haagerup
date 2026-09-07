"""Algebraic partial traces and GL pentagon-correction regressions.

All inverses of associators are actual inverses. Adjoint notation occurs
only for the fixed, orthonormal fusion-basis inclusions. The numerical
examples are Fibonacci/Yang--Lee trials, not new HI existence certificates.
"""

from collections import deque
from itertools import product
import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm

from hi_associahedron_path_bound import replay
from hi_pentagon_stability import inverse as inverse_word, reduce_word, trees
from hi_right_pentagon_correction import right_obj, cochain, append
from hi_unitary_handle_bound import (
    Trial, Morph, ONE, TAU, SIMPLES, PHI, fusion, identity, zero, tensor,
    tensor_obj, tensor_basis, inclusion,
)


def inv(f):
    return Morph(f.target, f.source, tuple(np.linalg.inv(b) for b in f.blocks))


class GLTrial(Trial):
    def __init__(self, matrix, scalar, delta):
        super().__init__(np.asarray(matrix, dtype=complex), complex(scalar))
        self.dims = (1 + 0j, complex(delta))
        self.global_dim = sum(d * d for d in self.dims)
        self.S = sum(abs(d) ** 2 for d in self.dims) / abs(self.global_dim)
        self.M = max(1, abs(self.scalar), 1 / abs(self.scalar),
                     np.linalg.norm(self.matrix, 2),
                     np.linalg.norm(np.linalg.inv(self.matrix), 2))

    def F(self, a, b, c):
        key = (a, b, c)
        if key in self.associators:
            return self.associators[key]
        ab, bc = tensor_obj(a, b), tensor_obj(b, c)
        source, target = tensor_obj(ab, c), tensor_obj(a, bc)
        result = zero(source, target)
        for out in range(2):
            target_index = {t: i for i, t in enumerate(tensor_basis(a, bc, out))}
            bc_indices = [{t: i for i, t in enumerate(tensor_basis(b, c, f))}
                          for f in range(2)]
            for col, (e, k, xab, z) in enumerate(tensor_basis(ab, c, out)):
                i, j, x, y = tensor_basis(a, b, e)[xab]
                left, right, matrix = self.basic(i, j, k, out)
                for ri, f in enumerate(right):
                    ybc = bc_indices[f][j, k, y, z]
                    row = target_index[i, f, x, ybc]
                    result.blocks[out][row, col] = matrix[ri, left.index(e)]
        self.associators[key] = result
        return result

    def cup(self, a):
        return inclusion(tensor_obj(SIMPLES[a], SIMPLES[a]), 0).scale(
            np.sqrt(self.dims[a]))

    def cap(self, a):
        # For negative delta this is intentionally not cup(a).adjoint().
        return inclusion(tensor_obj(SIMPLES[a], SIMPLES[a]), 0).adjoint().scale(
            np.sqrt(self.dims[a]))

    def trace(self, a, t, operator):
        sa = SIMPLES[a]
        f = self.F(sa, sa, t)
        plus = f @ tensor(self.cup(a), identity(t))
        minus = tensor(self.cap(a), identity(t)) @ inv(f)
        return minus @ tensor(identity(sa), operator) @ plus

    def holonomy(self, a=TAU, b=TAU, c=TAU, d=TAU):
        ab, bc, cd = tensor_obj(a, b), tensor_obj(b, c), tensor_obj(c, d)
        long = tensor(identity(a), self.F(b, c, d)) @ self.F(a, bc, d) @ tensor(self.F(a, b, c), identity(d))
        short = self.F(a, b, cd) @ self.F(ab, c, d)
        return long @ inv(short)

    def errors(self):
        ps = [self.holonomy(*(SIMPLES[i] for i in labels))
              for labels in product(range(2), repeat=4)]
        return (max((p - identity(p.source)).norm() for p in ps),
                max((inv(p) - identity(p.source)).norm() for p in ps))

    def handle(self, b, t, operators):
        sb = SIMPLES[b]
        bt = tensor_obj(sb, t)
        left, rl, rr = zero(bt), zero(bt), zero(bt)
        for a in range(2):
            sa = SIMPLES[a]
            ab = tensor_obj(sa, sb)
            extension = zero(tensor_obj(ab, t))
            for z in fusion(a, b):
                sz = SIMPLES[z]
                i = inclusion(ab, z)
                it = tensor(i, identity(t))
                extension = extension + it @ operators[z] @ it.adjoint()
                f1 = self.F(sa, sa, sb)
                jp = tensor(identity(sa), i.adjoint()) @ f1 @ tensor(self.cup(a), identity(sb))
                jm = tensor(self.cap(a), identity(sb)) @ inv(f1) @ tensor(identity(sa), i)
                f = self.F(sa, sz, t)
                lp, lm = f @ tensor(jp, identity(t)), tensor(jm, identity(t)) @ inv(f)
                op = tensor(identity(sa), operators[z])
                rl = rl + (lm @ op @ lp).scale(self.dims[a] / self.global_dim)
                ell = inclusion(tensor_obj(sb, sz), a)
                f2 = self.F(sb, sz, sz)
                sp = tensor(ell.adjoint(), identity(sz)) @ inv(f2) @ tensor(identity(sb), self.cup(z))
                sm = tensor(identity(sb), self.cap(z)) @ f2 @ tensor(ell, identity(sz))
                rp, rm = f @ tensor(sp, identity(t)), tensor(sm, identity(t)) @ inv(f)
                rr = rr + (rm @ op @ rp).scale(self.dims[z] / self.global_dim)
            f = self.F(sa, sb, t)
            left = left + self.trace(a, bt, f @ extension @ inv(f)).scale(self.dims[a] / self.global_dim)
        averaged = zero(t)
        for z in range(2):
            averaged = averaged + self.trace(z, t, operators[z]).scale(self.dims[z] / self.global_dim)
        return left, tensor(identity(sb), averaged), rl, rr

    def imbalance(self, b):
        result = 0.0
        for a in range(2):
            for z in fusion(a, b):
                l1, r1, f1 = self.basic(a, a, b, b)
                l2, r2, f2 = self.basic(b, z, z, b)
                x = self.dims[a] ** 2 * f1[r1.index(z), l1.index(0)] * np.linalg.inv(f1)[l1.index(0), r1.index(z)]
                y = self.dims[z] ** 2 * f2[r2.index(0), l2.index(a)] * np.linalg.inv(f2)[l2.index(a), r2.index(0)]
                result += abs(x - y) / abs(self.global_dim)
        return result


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
            value = f @ value @ inv(f)
        out.append(value)
    f = append(trial, objects[:-1], objects[-1])
    out.append(f @ tensor(cochain(c, objects[:-1]), identity(objects[-1])) @ inv(f))
    return out


def differential(trial, c, m):
    result = zero(right_obj((TAU,) * (m + 1)))
    for i, value in enumerate(cofaces(trial, c, m)):
        result = result + value.scale((-1) ** i)
    return result


def average(trial, c, m):
    return trial.trace(1, right_obj((TAU,) * (m - 1)), c).scale(
        trial.dims[1] / trial.global_dim)


def update(trial, u, scale=1.0):
    return GLTrial(expm(scale * u.blocks[1]) @ trial.matrix,
                   np.exp(scale * u.blocks[0][0, 0]) * trial.scalar, trial.dims[1])


def random_operator(rng, obj):
    blocks = tuple(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)) for d in obj)
    out = Morph(obj, obj, blocks)
    return out.scale(1 / out.norm())


def exact_transport_checks():
    root = Path(__file__).parent
    data = next(x for x in json.loads((root / "hi_associahedron_path_bound_certificates.json").read_text())
                if x["tensor_factors"] == 5)
    replay(data)
    adjacency = {v: [] for v in range(data["vertices"])}
    for e in data["tree_edges"]:
        a, b = data["edges"][e - 1]
        adjacency[a].append(b)
        adjacency[b].append(a)
    depth, queue = {0: 0}, deque([0])
    while queue:
        a = queue.popleft()
        for b in adjacency[a]:
            if b not in depth:
                depth[b] = depth[a] + 1
                queue.append(b)
    assert max(depth.values()) == 3
    costs = dict.fromkeys(data["tree_edges"], 0)
    for step in data["steps"]:
        face = data["faces"][step["face"]]
        known_costs = [costs[abs(e)] for e in face if abs(e) != step["edge"]]
        # Each nonidentity gauged edge is one conjugated pentagon or the
        # inverse of an earlier edge, with no additional nonidentity factor.
        assert sum(known_costs) + int(len(face) == 5) <= 1
        costs[step["edge"]] = step["cost"]
    lines = (root / "hi_right_pentagon_correction_results.txt").read_text().splitlines()
    rows = [json.loads(x[len("RIGHT_COFACE "):]) for x in lines if x.startswith("RIGHT_COFACE ")]
    assert sorted(len(x["old_transport"]) for x in rows) == [1, 3, 4, 6, 7, 10]
    assert max(len(x["standard_transport"]) for x in rows) == 3
    assert sorted(x["cost"] for x in rows) == [0, 0, 0, 1, 2, 2]
    for row in rows:
        loop = reduce_word(tuple(row["old_transport"]) + inverse_word(row["standard_transport"]))
        assert list(loop) == row["comparison_loop"]
        assert sum(costs[abs(e)] for e in loop) == row["cost"]
        assert sum(costs[abs(e)] for e in row["standard_transport"]) == 0
        assert sum(costs[abs(e)] for e in row["old_transport"]) == row["cost"] <= 2
    boundary_lines = (root / "hi_pentagon_stability_results.txt").read_text().splitlines()
    faces = [json.loads(x[5:]) for x in boundary_lines if x.startswith("FACE ")]
    order = json.loads(next(x[14:] for x in boundary_lines if x.startswith("PRODUCT_ORDER ")))
    factors = {f["id"]: (3,) + tuple(f["whisker"]) + tuple(f["word"])
               + inverse_word(f["whisker"]) + (-3,) for f in faces}
    assert reduce_word(tuple(e for k in order for e in factors[k])) == ()
    ts = trees(0, 5)
    index = {t: i for i, t in enumerate(ts)}
    edge_id = {tuple(e): i + 1 for i, e in enumerate(data["edges"])}
    signs = {0: -1, 1: 1, 2: -1, 3: 1, 7: -1, 8: 1}
    for row in rows:
        face = next(f for f in faces if f["id"] == row["face"])
        begin, end = face["interval"]
        if end - begin == 2:
            atoms = list(range(begin)) + [(begin, begin + 1)] + list(range(end, 5))
            embed = lambda t: t
        else:
            atoms = list(range(begin, end))
            embed = (lambda t: (t, 4)) if begin == 0 else (lambda t: (0, t))
        a, b, c, d = atoms
        vs = [(a, (b, (c, d))), ((a, b), (c, d)), (((a, b), c), d),
              ((a, (b, c)), d), (a, ((b, c), d)), (a, (b, (c, d)))]
        vs = [index[embed(t)] for t in vs]
        canonical = tuple(edge_id[tuple(sorted((u, v)))] * (1 if u < v else -1)
                          for u, v in zip(vs, vs[1:]))
        old = tuple(row["old_transport"])
        recovered = reduce_word(inverse_word(old) + factors[row["face"]] + old)
        sign = signs[row["face"]]
        assert recovered == (canonical if sign == 1 else inverse_word(canonical))
        row["canonical"], row["sign"] = canonical, sign
    from fractions import Fraction as Q
    assert 15 * Q(4, 3) ** 6 + 4 < 90
    assert Q(9, 8) ** 4 < 2
    assert Q(5, 4) * (Q(5, 4) ** 2 + 1) < 4
    assert 90 * 2 ** 2 + 40 == 400
    assert 14 + 400 + Q(25, 2) < 427
    assert 427 + 8 == 435
    assert Q(435, 870) == Q(1, 2)
    print("EXACT_GL_CONSTANTS: tree depth 3; canonical face conjugation <=M^6; old paths have <=2 nonidentity gauged edges")
    print("EXACT_GL_CONSTANTS: Bianchi=400*M^12*q^2; correction=427*S^2*M^14; with drift=435*S^2*M^14")
    return data, faces, factors, order, rows


def boundary_regressions(data, faces, factors, order, rows):
    rng = np.random.default_rng(8917)
    op = lambda a: float(np.linalg.norm(a, 2))
    for dim in (2, 3, 7):
        ident = np.eye(dim, dtype=complex)
        for scale in (0.0001, 0.001, 0.004):
            matrices = {}
            for e in range(1, len(data["edges"]) + 1):
                a = rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim))
                matrices[e] = expm(scale * a / op(a))

            def evaluate(word):
                result = ident.copy()
                for e in word:
                    result = result @ (matrices[e] if e > 0 else np.linalg.inv(matrices[-e]))
                return result

            for f in faces:
                w = f["word"]
                if len(w) == 4:
                    rest = evaluate(w[:-1])
                    matrices[abs(w[-1])] = np.linalg.inv(rest) if w[-1] > 0 else rest
            for f in faces:
                if len(f["word"]) == 4:
                    assert op(evaluate(f["word"]) - ident) < 3e-14
            M = max(max(op(a), op(np.linalg.inv(a))) for a in matrices.values())
            ps = [evaluate(row["canonical"]) for row in rows]
            q = max(op(p - ident) for p in ps)
            assert q <= 1 / (16 * M ** 6)
            t = 2 * M ** 6 * q
            boundary = sum((evaluate(factors[k]) - ident for k in order), np.zeros_like(ident))
            assert op(evaluate(tuple(e for k in order for e in factors[k])) - ident) < 5e-14
            bhat, standard, compare = np.zeros_like(ident), np.zeros_like(ident), np.zeros_like(ident)
            for row, p in zip(rows, ps):
                old = evaluate(row["old_transport"])
                std = evaluate(row["standard_transport"])
                assert max(op(old), op(np.linalg.inv(old))) <= M ** 3 * (1 + t) ** 2 + 2e-14
                sign = row["sign"]
                bhat += sign * old @ (p - ident) @ np.linalg.inv(old)
                standard += sign * std @ (p - ident) @ np.linalg.inv(std)
                y = rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim))
                y /= op(y)
                compare += sign * (old @ y @ np.linalg.inv(old) - std @ y @ np.linalg.inv(std))
            assert op(bhat) <= 360 * M ** 12 * q * q + 3e-14
            assert op(compare) <= 40 * M ** 12 * q + 3e-14
            assert op(standard) <= 400 * M ** 12 * q * q + 3e-14
            print("GL_BOUNDARY_REGRESSION", dim, scale, "M", M, "q", q,
                  "linear_boundary", op(boundary), "Bhat", op(bhat),
                  "standard_Bianchi", op(standard), flush=True)


def regressions():
    rng = np.random.default_rng(8901)
    initial = None
    for label, delta in (("Fibonacci", PHI), ("Yang-Lee", -1 / PHI)):
        t = 1 / np.sqrt(complex(delta))
        standard = np.array([[t * t, t], [t, -t * t]])
        for kind in ("balanced", "unbalanced"):
            for scale in (0.0, 1e-5, 0.003, 0.02):
                if kind == "balanced":
                    matrix = standard @ np.diag([1 + scale, 1 - scale])
                else:
                    v = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
                    matrix = expm(scale * v) @ standard
                trial = GLTrial(matrix, 1 + scale * (0.73 + 0.2j), delta)
                q, qi = trial.errors()
                mu = max(trial.imbalance(b) for b in range(2))
                S, M = trial.S, trial.M
                worst_handle = 0.0
                for obj in (TAU, (2, 3)):
                    operators = [random_operator(rng, tensor_obj(s, obj)) for s in SIMPLES]
                    for a in range(2):
                        traced = trial.trace(a, obj, identity(tensor_obj(SIMPLES[a], obj)))
                        assert (traced - identity(obj).scale(trial.dims[a])).norm() < 2e-12
                    for b in range(2):
                        l, r, rl, rr = trial.handle(b, obj, operators)
                        assert (l - rl).norm() <= S * M ** 4 * (q + qi) + 2e-11
                        assert (r - rr).norm() <= S * M ** 4 * (q + qi) + 2e-11
                        assert (rl - rr).norm() <= M * M * trial.imbalance(b) + 2e-11
                        worst_handle = max(worst_handle, (l - r).norm())
                y, u = random_operator(rng, right_obj((TAU,) * 4)), random_operator(rng, right_obj((TAU,) * 3))
                af = [zero(y.source) for _ in range(6)]
                for a in range(2):
                    for i, f in enumerate(cofaces(trial, y, 4, (SIMPLES[a],) + (TAU,) * 4)):
                        af[i] = af[i] + trial.trace(a, y.source, f).scale(trial.dims[a] / trial.global_dim)
                fa = cofaces(trial, average(trial, y, 4), 3)
                assert (af[0] - y).norm() < 3e-11
                middle = max((af[i] - fa[i - 1]).norm() for i in (2, 3, 4))
                assert middle < 3e-11
                assert (af[1] - fa[0]).norm() <= 2 * S * M ** 4 * (q + qi) + M * M * mu + 3e-11
                assert (af[5] - fa[4]).norm() <= S * M ** 8 * (q + qi) + 3e-11
                homotopy = y - differential(trial, average(trial, y, 4), 3) - average(trial, differential(trial, y, 4), 5)
                bound = S * (2 * M ** 4 + M ** 8) * (q + qi) + M * M * mu
                assert homotopy.norm() <= bound + 5e-11
                assert average(trial, y, 4).norm() <= S * M * M + 1e-11
                p = trial.holonomy()
                fs = cofaces(trial, u, 3)
                plus, minus = fs[0] + fs[2] + fs[4], fs[1] + fs[3]
                derivative = plus @ p - p @ minus
                assert (derivative - differential(trial, u, 3)).norm() <= 5 * M ** 4 * q + 3e-11
                eps = 2e-6
                fd = (update(trial, u, eps).holonomy() - update(trial, u, -eps).holonomy()).scale(1 / (2 * eps))
                assert (derivative - fd).norm() < 1e-7
                changed = update(trial, u, eps)
                drift = abs(max(changed.imbalance(b) for b in range(2)) - mu)
                assert drift <= 4 * S * (M * np.exp(eps)) ** 2 * eps + 1e-11
                if kind == "balanced":
                    assert mu < 3e-14
                if scale == 0:
                    assert q < 2e-14 and homotopy.norm() < 5e-13
                if label == "Yang-Lee" and kind == "balanced" and scale == 0.003:
                    initial = trial
                print("GL_REGRESSION", label, kind, "scale", scale, "M", M, "q", q,
                      "mu", mu, "handle_sample", worst_handle, "homotopy_sample", homotopy.norm(),
                      "middle_error", middle, flush=True)
    # A numerical iteration, outside the deliberately conservative sufficient
    # threshold. This tests the formula but does not certify that threshold.
    trial = initial
    for j in range(5):
        p = trial.holonomy()
        residual = p - identity(p.source)
        correction = average(trial, residual, 4).scale(-1)
        new = update(trial, correction)
        nq = new.errors()[0]
        print("YANG_LEE_CORRECTION", j, "q", residual.norm(), "step", correction.norm(), "new_q", nq, flush=True)
        assert nq < residual.norm() * 0.4 + 3e-14
        trial = new
        if nq < 3e-14:
            break
    assert trial.errors()[0] < 3e-14
    print("ALL GL PARTIAL-TRACE AND CORRECTION REGRESSIONS PASSED; NO NEW HI EXISTENCE CLAIM")


if __name__ == "__main__":
    boundary_regressions(*exact_transport_checks())
    regressions()
