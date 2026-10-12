"""Post-process render 1: composite, bloom, tone-map, label the six objects."""
import numpy as np
import look as L

px, A = L.load_render('r1_fusion')
h, w = px.shape[:2]
k = w / L.W
img = L.composite(px, center=(0.5, 0.42), strength=1.0, seed=1)
img = L.bloom(img, threshold=0.7, strength=0.85,
              levels=tuple((s * k, wt) for s, wt in ((3, 0.35), (10, 0.25), (28, 0.18), (70, 0.12), (160, 0.08))))
out = L.finish(img, exposure=1.05, seed=1, grain=0.009)
lay, d = L.overlay_like(out)
MI = L.MI
tn = {'rho': [(MI['rho'], 'n')], 'alpha rho': [(MI['alpha'] + MI['rho'], 'n')],
      'alpha^2 rho': [(MI['alpha'], 'n'), ('2', 'sup'), (MI['rho'], 'n')]}
gn = {'1': [('1', 'n')], 'alpha': [(MI['alpha'], 'n')], 'alpha^2': [(MI['alpha'], 'n'), ('2', 'sup')]}
T = np.array([a[:2] for a in A['teal']]); G = np.array([a[:2] for a in A['gold']])
# back sphere: label to its right; front spheres: straight below, clear of the rings
offs_t = [np.array([250, 20]), np.array([0, 300]), np.array([0, 300])]
for (x, y), n, o in zip(T, A['names_t'], offs_t):
    L.mtext(d, (x + o[0] * k, y + o[1] * k), tn[n], int(64 * k), fill=(200, 255, 248), alpha=240)
offs_g = [np.array([0, -80]), np.array([-84, 0]), np.array([84, 0])]
for (x, y), n, o in zip(G, A['names_g'], offs_g):
    L.mtext(d, (x + o[0] * k, y + o[1] * k), gn[n], int(54 * k), fill=(255, 214, 150), alpha=240)
L.save(out, 'r1_fusion_graph', lay)
