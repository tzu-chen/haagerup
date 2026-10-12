"""Render: 'The 248' -- E8 roots in the Petrie projection, coloured by the Z3
coset of E6+A2, with the roots used by the six currents of U ringed."""
import numpy as np
import look as L
from e8data import e8_roots, petrie_plane

X, lab, roots, G = e8_roots()
p, q = petrie_plane(X)
P = np.stack([X @ p, X @ q], 1)
rmax = np.linalg.norm(P, axis=1).max()
S = 610 / rmax
cx, cy = L.W / 2, L.H / 2 + 8
xy = np.stack([cx + S * P[:, 0], cy - S * P[:, 1]], 1)

col = np.array([L.PAL['gold'], L.PAL['teal'], L.PAL['coral']])

img = L.backdrop(center=(0.5, 0.5), strength=0.9, seed=2)

# guide rings (the eight Petrie orbits)
radii = np.unique(np.round(np.linalg.norm(P, axis=1) * S, 1))
for r in radii:
    L.ring(img, cx, cy, r, L.PAL['ice'], width=1.0, intensity=0.035)

# edges of the Gosset polytope: pairs of roots with inner product one
ip = X @ X.T
i, j = np.where(np.triu(np.isclose(ip, 1.0), 1))
same = lab[i] == lab[j]
ecol = 0.5 * (col[lab[i]] + col[lab[j]])
# mixed edges are dimmer so the three cosets read as layers of colour
w = np.where(same, 0.055, 0.028)[:, None]
L.segments(img, xy[i], xy[j], ecol * w, intensity=1.0, density=1.2)

# the six currents of U: roots +-alpha_L and +-alpha_i (c_i != 0)
alphaL = np.array([-1, -2, -3, -2, -1, -2, 0, 0], float)
simple = [np.eye(8)[k] for k in (0, 1, 2, 3, 4, 6, 7)]
marked = []
for v in [alphaL] + simple:
    for s in (1, -1):
        k = np.where(np.all(np.isclose(roots, s * v), axis=1))[0]
        assert len(k) == 1
        marked.append(k[0])
marked = np.array(marked)
assert len(marked) == 16 and np.all(lab[marked] == 0)

# nodes
for k in range(len(X)):
    c = col[lab[k]]
    L.disc(img, xy[k, 0], xy[k, 1], 5.2, c * 2.2, soft=1.0, halo=0.22, halo_r=3.2)
for k in marked:
    L.ring(img, xy[k, 0], xy[k, 1], 12.5, L.PAL['ice'], width=2.0, intensity=1.25)

# the eight Cartan currents at the centre: a small octagon of light
for t in range(8):
    a = 2 * np.pi * t / 8 + np.pi / 8
    L.disc(img, cx + 16 * np.cos(a), cy + 16 * np.sin(a), 3.0, L.PAL['ice'] * 2.0, halo=0.3)

img = L.bloom(img, threshold=0.45, strength=0.9)
out = L.finish(img, exposure=1.15, seed=2)
lay, d = L.overlay()
L.save(out, 'r2_e8_248', lay)
print('marked labels', np.bincount(lab[marked], minlength=3), 'edges', len(i),
      'same-coset edges', same.sum())
