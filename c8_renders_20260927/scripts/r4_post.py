"""Post-process render 4: the (Z/13)^2 torus and its two isotropic lines."""
import numpy as np
import look as L

px, A = L.load_render('r4_torus')
h, w = px.shape[:2]
k = w / L.W
img = L.composite(px, center=(0.5, 0.5), strength=0.95, seed=4)
img = L.bloom(img, threshold=0.65, strength=0.9,
              levels=tuple((s * k, wt) for s, wt in ((3, 0.35), (10, 0.25), (28, 0.18), (70, 0.12), (160, 0.08))))
out = L.finish(img, exposure=1.08, seed=4, grain=0.009)
lay, d = L.overlay_like(out)
math = 'math'
x, y, _ = A['vac']
L.label(d, (x, y + 70 * k), '(0, 0)', key=math, size=int(40 * k), fill=(255, 214, 150), alpha=235)
x, y, _ = A['plus']      # realized line k = -5j (coral), left of the vacuum
L.label(d, (x - 60 * k, y + 40 * k), '\U0001D458 = −5\U0001D457', key=math, size=int(46 * k),
        fill=(255, 170, 195), anchor='rm', alpha=240)
x, y, _ = A['minus']     # excluded line k = 5j (violet), right of the vacuum
L.label(d, (x + 60 * k, y + 40 * k), '\U0001D458 = 5\U0001D457', key=math, size=int(46 * k),
        fill=(190, 180, 255), anchor='lm', alpha=225)
L.mtext(d, (w - 90 * k, h - 80 * k), [('5', 'n'), ('2', 'sup'), (' \u2261 \u22121  (mod 13)', 'n')],
        int(52 * k), anchor='rm', alpha=225)
L.save(out, 'r4_five_squared', lay)
