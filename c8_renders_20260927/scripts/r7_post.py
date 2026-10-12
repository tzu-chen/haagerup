"""Post-process render 7: the diptych of the two c = 8 theories."""
import numpy as np
from PIL import Image
import look as L

panels = []
for name in ('diag', 'e8'):
    px, A = L.load_render(f'r7_city_{name}')
    img = L.composite(px, center=(0.5, 0.35), strength=1.0, seed=7)
    k = px.shape[1] / 1200
    img = L.bloom(img, threshold=0.8, strength=0.8,
                  levels=tuple((s * k, wt) for s, wt in ((3, 0.3), (10, 0.22), (28, 0.16), (70, 0.1), (140, 0.07))))
    panels.append(L.finish(img, exposure=1.02, seed=7, grain=0.009, vignette=0.2))
    anchors = A
out = np.concatenate(panels, 1)
h, w = out.shape[:2]
k = w / L.W
# a hairline divider
yb = int(h - 120 * w / L.W)
out[:yb, w // 2 - 1:w // 2 + 1] = (out[:yb, w // 2 - 1:w // 2 + 1] * 0.4 + 60).astype(np.uint8)
lay, d = L.overlay_like(out)
ice = (225, 232, 255)
titles = ([('Diagonal U theory', 'n')], [('E', 'n'), ('8', 'sub'), (' extension', 'n')])
for i, (title, a, b) in enumerate(((titles[0], '2,941', 'relevant scalar components'),
                                    (titles[1], '0', 'relevant scalar components'))):
    x = (i * 1200 + 70) * k
    L.mtext(d, (x, 90 * k), title, int(46 * k), fill=ice, anchor='lm', alpha=240, key='sansb')
    L.label(d, (x, 158 * k), a, key='sansbl', size=int(58 * k), fill=(255, 214, 150), anchor='lm', alpha=245)
    wa = d.textlength(a, font=L.font('sansbl', int(58 * k)))
    L.label(d, (x + wa + 18 * k, 162 * k), b, key='sansl', size=int(34 * k), fill=ice,
            anchor='lm', alpha=220)
L.mtext(d, (w / 2, h - 60 * k), [('Both at c = 8.   Bar height: log', 'n'), ('10', 'sub'),
        (' of the number of Virasoro primaries at (h, ', 'n'), ('h', 'bar'), (')', 'n')],
        int(30 * k), fill=ice, alpha=200, key='sansl')
# the marginal line: label it where it meets the h axis in each panel
(x2, y2, _), _ = anchors['two']
for i in range(2):
    L.mtext(d, (i * w / 2 + x2 + 62 * k, y2 + 14 * k),
            [('\u0394 = 2', 'n')], int(34 * k), fill=(255, 150, 180), anchor='lm', alpha=235)
L.save(out, 'r7_two_cities', lay)
