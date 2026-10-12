"""Exact roots and Cartan character of the rank-two lattice neighbor.

Root-only research job: safe_run with <=2 GiB AS, <=180 seconds.
Two rank-eight affine LDL spheres of radius squared two; at most 500
momenta retained. Expected RSS below 0.1 GiB, no dense tensor or workers.
This checks lattice and character data, not the PF reconstruction theorem.
"""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_next_81top_exact as top


def shifted_ball(gram, shift):
    lower = [[Q(i == j) for j in range(8)] for i in range(8)]
    diagonal = []
    for j in range(8):
        diagonal.append(Q(gram[j][j])-sum(lower[j][k]**2*diagonal[k] for k in range(j)))
        assert diagonal[-1] > 0
        for i in range(j+1, 8):
            lower[i][j] = (gram[i][j]-sum(lower[i][k]*lower[j][k]*diagonal[k] for k in range(j)))/diagonal[j]
    for i in range(8):
        for j in range(8):
            assert sum(lower[i][k]*diagonal[k]*lower[j][k] for k in range(8)) == gram[i][j]
    values, out = [Q(0)]*8, []
    def visit(i, remaining):
        if i < 0:
            out.append(tuple(values))
            assert len(out) < 500
            return
        offset = shift[i]+sum(lower[j][i]*values[j] for j in range(i+1, 8))
        square = remaining/diagonal[i]
        radius = isqrt(square.numerator//square.denominator)+2
        center = (-offset).numerator//(-offset).denominator
        for integer in range(center-radius, center+radius+1):
            cost = diagonal[i]*(integer+offset)**2
            if cost <= remaining:
                values[i] = integer+shift[i]
                visit(i-1, remaining-cost)
    visit(7, Q(2))
    return out


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(180)
    started = monotonic()
    inverse = x.inverse(x.G)
    lam = tuple(inverse[i][0]+inverse[i][6] for i in range(8))
    assert x.norm(lam) == 2
    m = [[Q(i == j) for j in range(8)] for i in range(8)]
    m[7] = list(lam)
    n = x.inverse(m)
    assert all(v.denominator == 1 for row in n for v in row)
    gram = top.integers(top.multiply(top.multiply(m, x.G), top.transpose(m)))
    def old(v):
        return tuple(sum(v[i]*m[i][j] for i in range(8)) for j in range(8))
    a0 = tuple(map(Q, (-1,-2,-3,-2,-1,-2,0,0)))
    seeds = [tuple(map(Q, a)) for a in ((0,0,0,0,0,-1,1,1),
                                       (0,0,0,1,1,-1,0,0),
                                       (1,1,0,0,0,-1,0,0))]
    t = tuple(sum(a[i] for a in seeds) for i in range(8))
    alpha = tuple(v/2 for v in t)
    gamma = tuple(4*v-w for v, w in zip(a0, alpha))
    assert (x.norm(t), x.dot(a0, t), x.norm(alpha), x.norm(gamma), x.dot(alpha, gamma)) == (24,3,6,26,0)
    shifted = tuple(sum(alpha[i]*n[i][j] for i in range(8)) for j in range(8))
    assert all((2*v).denominator == 1 for v in shifted)
    assert any(v.denominator == 2 for v in shifted)
    roots, sector_sizes, b_roots = set(), [], set()
    for shift in ((Q(0),)*8, shifted):
        candidates = list(map(old, shifted_ball(gram, shift)))
        sector = {a for a in candidates if x.norm(a) == 2 and x.dot(a,t) % 2 == 0}
        sector_sizes.append(len(sector))
        assert not (roots & sector)
        roots.update(sector)
        momentum_shift = old(shift)
        b_roots.update(a for a in sector if all((u-v).denominator == 1 for u,v in zip(a,momentum_shift)))
    assert len(roots) == 240
    assert all(x.dot(a,b).denominator == 1 for a in roots for b in roots)
    betas = [tuple(a[i]-alpha[i] for i in range(8)) for a in seeds]
    assert all(b in roots for b in betas)
    assert [[x.dot(a,b) for b in betas] for a in betas] == [[2,0,0],[0,2,0],[0,0,2]]
    assert tuple(sum(a[i] for a in betas) for i in range(8)) == tuple(-v for v in alpha)
    weights = Counter({(0,0):8})
    for a in roots:
        h, k = x.dot(alpha,a), x.dot(gamma,a)
        assert h.denominator == k.denominator == 1
        weights[int(h),int(k)] += 1
    original = weights.copy()
    decomposition = []
    while weights:
        h,k = max(weights)
        assert h >= 0 and k >= 0
        multiplicity = weights[h,k]
        decomposition.append([h,k,multiplicity])
        for i in range(-h,h+1,2):
            for j in range(-k,k+1,2):
                assert weights[i,j] >= multiplicity
                weights[i,j] -= multiplicity
                if weights[i,j] == 0:
                    del weights[i,j]
    assert sum((h+1)*(k+1)*v for h,k,v in decomposition) == 248
    centralizer = sum((k+1)*v for h,k,v in decomposition if h == 0)
    direct_centralizer = sum(v for (h,k),v in original.items() if h == 0)-sum(v for (h,k),v in original.items() if h == 2)
    assert centralizer == direct_centralizer
    result = {
        'root_count':len(roots), 'neighbor_root_sector_sizes':sector_sizes,
        'neighbor_B_root_count':len(b_roots),
        'alpha_squared':6, 'gamma_squared':26, 'alpha_gamma_pairing':0,
        'three_orthogonal_roots_verified':True,
        'adjoint_sl2_pair_highest_weights':decomposition,
        'centralizer_of_level3_sl2_dimension':centralizer,
        'Cartan_weight_multiplicities':[[h,k,v] for (h,k),v in sorted(original.items())],
        'scope':'Exact neighbor lattice and Cartan character; affine currents/PF reconstruction are separate proof inputs.',
        'seconds':monotonic()-started,
        'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                         (Path(__file__),Path(x.__file__),Path(top.__file__))}}
    output = Path('hi_cft_20260923_next_neighbor_roots.json')
    assert not output.exists()
    output.write_text(json.dumps(result,indent=2)+'\n')
    signal.alarm(0)
    print(json.dumps({k:v for k,v in result.items() if k not in ('Cartan_weight_multiplicities','source_sha256')},indent=2),flush=True)


if __name__ == '__main__':
    main()
