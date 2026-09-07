"""Off-pentagon regressions for the uniform partial-trace handle bound.

Uses arbitrary unitary associators on Fibonacci fusion spaces, including
incoherent ones. No new HI category or uniform existence is asserted.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import cache
from itertools import product

import numpy as np
from scipy.linalg import expm

ONE, TAU = (1, 0), (0, 1)
SIMPLES = (ONE, TAU)
PHI = (1 + np.sqrt(5)) / 2
DIMS = (1.0, PHI)
GLOBAL = sum(d * d for d in DIMS)


def fusion(a, b):
    return (a + b,) if a * b == 0 else (0, 1)


@cache
def tensor_basis(a, b, out):
    return tuple((i, j, x, y) for i, j in product(range(2), repeat=2)
                 if out in fusion(i, j)
                 for x in range(a[i]) for y in range(b[j]))


def tensor_obj(a, b):
    return tuple(len(tensor_basis(a, b, k)) for k in range(2))


@dataclass
class Morph:
    source: tuple
    target: tuple
    blocks: tuple

    def __matmul__(self, other):
        assert self.source == other.target
        return Morph(other.source, self.target,
                     tuple(a @ b for a, b in zip(self.blocks, other.blocks)))

    def adjoint(self):
        return Morph(self.target, self.source, tuple(b.conj().T for b in self.blocks))

    def __add__(self, other):
        assert self.source == other.source and self.target == other.target
        return Morph(self.source, self.target,
                     tuple(a + b for a, b in zip(self.blocks, other.blocks)))

    def __sub__(self, other):
        return self + other.scale(-1)

    def scale(self, scalar):
        return Morph(self.source, self.target, tuple(scalar * b for b in self.blocks))

    def norm(self):
        return max((float(np.linalg.norm(b, 2)) if min(b.shape) else 0)
                   for b in self.blocks)


def identity(a):
    return Morph(a, a, tuple(np.eye(d, dtype=complex) for d in a))


def zero(a, b=None):
    b = a if b is None else b
    return Morph(a, b, tuple(np.zeros((y, x), dtype=complex) for x, y in zip(a, b)))


def tensor(f, g):
    source = tensor_obj(f.source, g.source)
    target = tensor_obj(f.target, g.target)
    result = zero(source, target)
    for k in range(2):
        for row, (i, j, x, y) in enumerate(tensor_basis(f.target, g.target, k)):
            for col, (i0, j0, x0, y0) in enumerate(tensor_basis(f.source, g.source, k)):
                if (i, j) == (i0, j0):
                    result.blocks[k][row, col] = f.blocks[i][x, x0] * g.blocks[j][y, y0]
    return result


def inclusion(a, label):
    assert a[label] == 1
    result = zero(SIMPLES[label], a)
    result.blocks[label][0, 0] = 1
    return result


class Trial:
    def __init__(self, matrix, scalar):
        self.matrix = matrix
        self.scalar = scalar
        self.associators = {}

    def basic(self, a, b, c, out):
        left = [e for e in fusion(a, b) if out in fusion(e, c)]
        right = [f for f in fusion(b, c) if out in fusion(a, f)]
        if (a, b, c) == (1, 1, 1):
            matrix = self.matrix if out else np.array([[self.scalar]])
        else:
            matrix = np.eye(len(left))
        return left, right, matrix

    def F(self, a, b, c):
        key = (a, b, c)
        if key in self.associators:
            return self.associators[key]
        ab, bc = tensor_obj(a, b), tensor_obj(b, c)
        source, target = tensor_obj(ab, c), tensor_obj(a, bc)
        result = zero(source, target)
        for out in range(2):
            target_index = {t: i for i, t in enumerate(tensor_basis(a, bc, out))}
            bc_indices = [{t: i for i, t in enumerate(tensor_basis(b, c, f))} for f in range(2)]
            for col, (e, k, xab, z) in enumerate(tensor_basis(ab, c, out)):
                i, j, x, y = tensor_basis(a, b, e)[xab]
                left, right, matrix = self.basic(i, j, k, out)
                for ri, f in enumerate(right):
                    ybc = bc_indices[f][j, k, y, z]
                    row = target_index[i, f, x, ybc]
                    result.blocks[out][row, col] = matrix[ri, left.index(e)]
        assert (result.adjoint() @ result - identity(source)).norm() < 1e-12
        self.associators[key] = result
        return result

    def cup(self, a):
        return inclusion(tensor_obj(SIMPLES[a], SIMPLES[a]), 0).scale(np.sqrt(DIMS[a]))

    def trace(self, a, t, operator):
        sa = SIMPLES[a]
        v = self.F(sa, sa, t) @ tensor(self.cup(a), identity(t))
        assert (v.adjoint() @ v - identity(t).scale(DIMS[a])).norm() < 1e-11
        return v.adjoint() @ tensor(identity(sa), operator) @ v

    def pentagon(self, a, b, c, d):
        ab, bc, cd = tensor_obj(a, b), tensor_obj(b, c), tensor_obj(c, d)
        long = tensor(identity(a), self.F(b, c, d)) @ self.F(a, bc, d) @ tensor(self.F(a, b, c), identity(d))
        short = self.F(a, b, cd) @ self.F(ab, c, d)
        return (long - short).norm()

    def handle(self, b, t, operators):
        sb = SIMPLES[b]
        bt = tensor_obj(sb, t)
        left, reduced_left, reduced_right = zero(bt), zero(bt), zero(bt)
        for a in range(2):
            sa = SIMPLES[a]
            ab = tensor_obj(sa, sb)
            extension = zero(tensor_obj(ab, t))
            for z in fusion(a, b):
                sz = SIMPLES[z]
                i = inclusion(ab, z)
                it = tensor(i, identity(t))
                extension = extension + it @ operators[z] @ it.adjoint()
                j = tensor(identity(sa), i.adjoint()) @ self.F(sa, sa, sb) @ tensor(self.cup(a), identity(sb))
                kl = self.F(sa, sz, t) @ tensor(j, identity(t))
                reduced_left = reduced_left + (kl.adjoint() @ tensor(identity(sa), operators[z]) @ kl).scale(DIMS[a] / GLOBAL)
                ell = inclusion(tensor_obj(sb, sz), a)
                s = tensor(ell.adjoint(), identity(sz)) @ self.F(sb, sz, sz).adjoint() @ tensor(identity(sb), self.cup(z))
                kr = self.F(sa, sz, t) @ tensor(s, identity(t))
                reduced_right = reduced_right + (kr.adjoint() @ tensor(identity(sa), operators[z]) @ kr).scale(DIMS[z] / GLOBAL)
            f = self.F(sa, sb, t)
            left = left + self.trace(a, bt, f @ extension @ f.adjoint()).scale(DIMS[a] / GLOBAL)
        averaged = zero(t)
        for z in range(2):
            averaged = averaged + self.trace(z, t, operators[z]).scale(DIMS[z] / GLOBAL)
        right = tensor(identity(sb), averaged)
        return left, right, reduced_left, reduced_right

    def imbalance(self, b):
        result = 0.0
        for a in range(2):
            for z in fusion(a, b):
                l1, r1, f1 = self.basic(a, a, b, b)
                l2, r2, f2 = self.basic(b, z, z, b)
                x = DIMS[a] ** 2 * abs(f1[r1.index(z), l1.index(0)]) ** 2
                y = DIMS[z] ** 2 * abs(f2[r2.index(0), l2.index(a)]) ** 2
                result += abs(x - y) / GLOBAL
        return result


def run():
    rng = np.random.default_rng(8601)
    standard = np.array([[1 / PHI, 1 / np.sqrt(PHI)], [1 / np.sqrt(PHI), -1 / PHI]])
    for kind in ("balanced", "unbalanced"):
        for scale in (0.0, 0.001, 0.02, 0.2):
            if kind == "balanced":
                matrix = np.diag(np.exp(1j * scale * rng.normal(size=2))) @ standard @ np.diag(np.exp(1j * scale * rng.normal(size=2)))
            else:
                h = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
                h = (h + h.conj().T) / 2
                matrix = standard @ expm(1j * scale * h)
            trial = Trial(matrix, np.exp(1j * scale * 0.73))
            q = max(trial.pentagon(*(SIMPLES[i] for i in labels)) for labels in product(range(2), repeat=4))
            worst = 0.0
            for t in (ONE, TAU, (2, 3)):
                operators = []
                for z in range(2):
                    obj = tensor_obj(SIMPLES[z], t)
                    cs = []
                    for dim in obj:
                        raw = rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim))
                        raw = (raw + raw.conj().T) / 2
                        if dim:
                            raw /= np.linalg.norm(raw, 2)
                        cs.append(raw)
                    operators.append(Morph(obj, obj, tuple(cs)))
                for b in range(2):
                    left, right, rl, rr = trial.handle(b, t, operators)
                    mu = trial.imbalance(b)
                    assert (left - rl).norm() <= 2 * q + 1e-10
                    assert (right - rr).norm() <= 2 * q + 1e-10
                    assert (rl - rr).norm() <= mu + 1e-10
                    actual = (left - right).norm()
                    assert actual <= 4 * q + mu + 1e-10
                    worst = max(worst, actual)
                    ones = [identity(tensor_obj(sz, t)) for sz in SIMPLES]
                    for op in trial.handle(b, t, ones):
                        assert (op - identity(tensor_obj(SIMPLES[b], t))).norm() < 1e-10
            mu = max(trial.imbalance(b) for b in range(2))
            if kind == "balanced":
                assert mu < 1e-12
            if scale == 0:
                assert q < 1e-12 and worst < 1e-12
            print(kind, "scale", scale, "q", q, "mu", mu, "handle_sample", worst, "bound", 4 * q + mu, flush=True)
    print("ALL OFF-PENTAGON HANDLE REGRESSIONS PASSED; NO HI EXISTENCE CLAIM")


if __name__ == "__main__":
    run()
