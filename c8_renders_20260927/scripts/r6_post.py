"""Post-process render 6: the landscape of G0(x)."""
import numpy as np
import look as L

px, A = L.load_render('r6_landscape')
h, w = px.shape[:2]
k = w / L.W
img = L.composite(px, center=(0.5, 0.35), strength=1.0, seed=6)
img = L.bloom(img, threshold=0.75, strength=0.8,
              levels=tuple((s * k, wt) for s, wt in ((3, 0.3), (10, 0.22), (28, 0.16), (70, 0.1), (160, 0.07))))
out = L.finish(img, exposure=1.0, seed=6, grain=0.009)
lay, d = L.overlay_like(out)
MI = L.MI
x_ = MI['x']
ice = (225, 232, 255)
for key, v, dy in (('p0', '0', -95), ('p1', '1', -95)):
    x, y, _ = A[key]
    L.mtext(d, (x, y + dy * k), [(x_, 'n'), (' = ' + v, 'n')], int(48 * k), fill=(255, 214, 150), alpha=240)
x, y, _ = A['zf']
L.mtext(d, (x + 95 * k, y - 185 * k), [(x_, 'n'), (' = 1/2 \u2212 ', 'n'), (MI['i'], 'n'), ('/', 'n'), ('2', 'sqrt')],
        int(42 * k), fill=(170, 245, 238), alpha=235, anchor='lm')
# the formula, top-left
fx, fy = 110 * k, 128 * k
sz = int(52 * k)
lhs = [(MI['G'], 'n'), ('0', 'sub'), ('(', 'n'), (x_, 'n'), (') =', 'n')]
num = [('3 \u2212 4', 'n'), (x_, 'n'), (' + 4', 'n'), (x_, 'n'), ('2', 'sup')]
den = [('3', 'n'), (x_, 'n'), ('4', 'sup'), ('(1 \u2212 ', 'n'), (x_, 'n'), (')', 'n'), ('4', 'sup')]
wl = L.mtext(d, (fx, fy), lhs, sz, fill=ice, alpha=235, anchor='lm')
x0 = fx + wl + 22 * k
wn = L.mtext(d, (0, 0), num, sz, measure=True)
wd = L.mtext(d, (0, 0), den, sz, measure=True)
wf = max(wn, wd)
L.mtext(d, (x0 + wf / 2, fy - 40 * k), num, sz, fill=ice, alpha=235)
d.line([(x0, fy), (x0 + wf, fy)], fill=ice + (220,), width=max(2, int(3 * k)))
L.mtext(d, (x0 + wf / 2, fy + 44 * k), den, sz, fill=ice, alpha=235)
L.save(out, 'r6_correlator_landscape', lay)
