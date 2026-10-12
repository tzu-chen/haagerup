"""E8 roots built from the manuscript's E6+A2 lattice basis, with the Z3 coset label.

Simple roots 0..7 have Gram diagonal 2 and -1 on the edges
(0,1),(1,2),(2,3),(3,4),(2,5) [E6] and (6,7) [A2], exactly as in
hi_cft_c8_proof.tex, Appendix A.  E8 = L u (L+g) u (L+2g) with g a
(27,3) glue vector.  Label 0 = roots of L = E6+A2 (78), labels 1,2 =
the two index-three cosets (81 each).
"""
import itertools
import numpy as np

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (6, 7)]


def gram():
    G = 2 * np.eye(8)
    for i, j in EDGES:
        G[i, j] = G[j, i] = -1
    return G


def weyl_orbit(start, G, nodes):
    """Orbit of a vector (in simple-root coordinates) under reflections in `nodes`."""
    start = np.array(start, float)
    seen = {tuple(np.round(start, 6)): start}
    frontier = [start]
    while frontier:
        new = []
        for v in frontier:
            for i in nodes:
                e = np.zeros(8); e[i] = 1
                w = v - (v @ G @ e) * e  # (alpha_i, alpha_i) = 2
                key = tuple(np.round(w, 6))
                if key not in seen:
                    seen[key] = w; new.append(w)
        frontier = new
    return list(seen.values())


def e8_roots():
    G = gram()
    Ginv = np.linalg.inv(G)
    e6 = [0, 1, 2, 3, 4, 5]
    a2 = [6, 7]
    # roots of L: orbits of the simple roots
    L = {}
    for i in range(8):
        e = np.zeros(8); e[i] = 1
        for v in weyl_orbit(e, G, e6 if i in e6 else a2):
            L[tuple(np.round(v, 6))] = v
    L = list(L.values())
    # fundamental weights (simple-root coordinates) = columns of Ginv
    w27 = Ginv[:, 0]    # minuscule E6 weight at an end of the long chain
    w3 = Ginv[:, 6]     # A2 fundamental weight
    O27 = weyl_orbit(w27, G, e6)
    O3 = weyl_orbit(w3, G, a2)
    assert len(O27) == 27 and len(O3) == 3
    c1 = [a + b for a in O27 for b in O3]
    c2 = [-v for v in c1]
    roots, label = [], []
    for lab, S in ((0, L), (1, c1), (2, c2)):
        for v in S:
            assert abs(v @ G @ v - 2) < 1e-9
            roots.append(v); label.append(lab)
    roots = np.array(roots); label = np.array(label)
    # Euclidean coordinates
    R = np.linalg.cholesky(G).T          # G = R^T R
    X = roots @ R.T
    # integrality of the full set (E8 is even unimodular)
    ip = X @ X.T
    assert np.allclose(ip, np.round(ip)), 'inner products not integral'
    return X, label, roots, G


def petrie_plane(X):
    """Coxeter-plane basis (two orthonormal 8-vectors) for the root set X."""
    rng = np.random.default_rng(1)
    f = rng.normal(size=8)
    pos = X[X @ f > 0]
    sums = {tuple(np.round(a + b, 6)) for a, b in itertools.combinations(pos, 2)}
    simple = np.array([a for a in pos if tuple(np.round(a, 6)) not in sums])
    assert len(simple) == 8
    C = np.eye(8)
    for a in simple:
        C = C @ (np.eye(8) - np.outer(a, a))  # (a,a)=2
    w, V = np.linalg.eig(C)
    k = np.argmin(np.abs(w - np.exp(2j * np.pi / 30)))
    v = V[:, k]
    p, q = v.real, v.imag
    p /= np.linalg.norm(p)
    q -= (q @ p) * p; q /= np.linalg.norm(q)
    return p, q


if __name__ == '__main__':
    X, lab, roots, G = e8_roots()
    print('roots', len(X), 'by label', np.bincount(lab))
    ip = X @ X.T
    print('neighbours (ip=1) per root', set((np.isclose(ip, 1)).sum(1)))
