"""Render 5 (2D): the twelve anyons of Z(H3) on a thirteen-hour clock, and the
Gauss-sum walk that produces sqrt(13).

Twists (defects.tex): 0, b, a, c0 -> 1; c1, c2 -> e^{2 pi i/3}, e^{4 pi i/3};
d_j -> e^{2 pi i 6 j^2/13}, i.e. hours {6, 11, 2, 5, 7, 8} = the quadratic
non-residues mod 13.  Bead areas are proportional to quantum dimensions
(1, d^2, s, s, s, s, 3d x 6) with d = (3+sqrt13)/2, s = 2 + 3d.
Right: sqrt13 = sum_j (j/13) zeta13^j, the identity defects.py uses.
"""
import numpy as np
import look as L

d = (3 + np.sqrt(13)) / 2
s = 2 + 3 * d
q = dict(zero=1.0, b=d * d, a=s, c0=s, c1=s, c2=s, d=3 * d)
leg = lambda j: 1 if pow(j, 6, 13) == 1 else -1
hours = {j: (6 * j * j) % 13 for j in range(1, 7)}
assert sorted(hours.values()) == [j for j in range(1, 13) if leg(j) == -1]

W, H = L.W, L.H
img = L.backdrop(center=(0.42, 0.5), strength=0.95, seed=5)
cx, cy, R = 640, 690, 430
rad = lambda qd: 9.0 * np.sqrt(qd)


def hour_xy(m, r, n=13):
    a = np.pi / 2 - 2 * np.pi * m / n
    return cx + r * np.cos(a), cy - r * np.sin(a)


# dial
L.ring(img, cx, cy, R, L.PAL['ice'], width=1.8, intensity=0.30)
L.ring(img, cx, cy, R - 16, L.PAL['ice'], width=1.0, intensity=0.10)
for m in range(13):
    x0, y0 = hour_xy(m, R - 30); x1, y1 = hour_xy(m, R - 16)
    L.segments(img, [[x0, y0]], [[x1, y1]], L.PAL['ice'] * 0.6, 1.0, 2.0)
    if m and leg(m) == 1:   # residues: empty sockets
        x, y = hour_xy(m, R)
        L.ring(img, x, y, 11, L.PAL['ice'], width=1.4, intensity=0.45)
# inner three-hour dial for the cube-root twists
Ri = 205
L.ring(img, cx, cy, Ri, L.PAL['violet'], width=1.4, intensity=0.28)
for m in range(3):
    x0, y0 = hour_xy(m, Ri - 14, 3); x1, y1 = hour_xy(m, Ri + 14, 3)
    L.segments(img, [[x0, y0]], [[x1, y1]], L.PAL['violet'] * 0.8, 1.0, 2.0)

beads = []   # (x, y, r, colour, label)
for j, m in hours.items():
    x, y = hour_xy(m, R)
    beads.append((x, y, rad(q['d']), L.PAL['coral'], f'd{j}'))
for lab, m in (('c1', 1), ('c2', 2)):
    x, y = hour_xy(m, Ri, 3)
    beads.append((x, y, rad(q[lab]), L.PAL['violet'], lab))
# twist one: the centre of the clock
beads.append((cx, cy, rad(q['zero']), L.PAL['gold'], '0'))
for lab, ang in (('b', 90), ('a', 210), ('c0', 330)):
    a = np.radians(ang)
    x, y = cx + 92 * np.cos(a), cy - 92 * np.sin(a)
    beads.append((x, y, rad(q[lab]), L.PAL['gold'], lab))
for x, y, r, col, _ in beads:
    L.disc(img, x, y, r, col * 1.9, soft=1.2, halo=0.28, halo_r=2.6)
    L.disc(img, x - 0.28 * r, y - 0.28 * r, 0.35 * r, L.PAL['ice'] * 0.5, soft=r * 0.3)

# Gauss sum walk
ox, oy, u = 1285, 830, 250
steps = [leg(j) * np.exp(2j * np.pi * j / 13) for j in range(1, 13)]
ps = np.concatenate([[0], np.cumsum(steps)])
assert abs(ps[-1] - np.sqrt(13)) < 1e-12
P = np.stack([ox + u * ps.real, oy - u * ps.imag], 1)
# real axis and the target
L.segments(img, [[ox - 60, oy]], [[ox + u * 4.25, oy]], L.PAL['ice'] * 0.22, 1.0, 2.0)
tx = ox + u * np.sqrt(13)
L.ring(img, tx, oy, 24, L.PAL['gold'], width=2.2, intensity=1.3)
for jj in range(12):
    col = L.PAL['teal'] if leg(jj + 1) == 1 else L.PAL['coral']
    a, b = P[jj], P[jj + 1]
    for off in (-1.3, 0, 1.3):
        n = np.array([-(b - a)[1], (b - a)[0]]); n /= np.linalg.norm(n)
        L.segments(img, [a + off * n], [b - 18 * (b - a) / np.linalg.norm(b - a) + off * n],
                   col * 1.7, 1.0, 2.0)
    # arrowhead
    v = (b - a) / np.linalg.norm(b - a); n = np.array([-v[1], v[0]])
    tip = b - 6 * v
    for sgn in (1, -1):
        L.segments(img, [tip], [tip - 22 * v + sgn * 10 * n], col * 1.7, 1.0, 2.5)
    L.disc(img, *a, 5.5, L.PAL['ice'] * 1.4, halo=0.2)
L.disc(img, ox, oy, 8, L.PAL['gold'] * 2.4, halo=0.35)

img = L.bloom(img, threshold=0.55, strength=0.9)
out = L.finish(img, exposure=1.08, seed=5, grain=0.010)
lay, dr = L.overlay()
MI = L.MI
for x, y, r, col, lab in beads:
    parts = [('0', 'n')] if lab == '0' else [(MI[lab[0]], 'n')] + ([(lab[1:], 'sub')] if lab[1:] else [])
    if lab.startswith('d'):
        vx, vy = x - cx, y - cy; n = np.hypot(vx, vy)
        lx, ly = x - vx / n * (r + 44), y - vy / n * (r + 44)
    elif lab in ('c1', 'c2'):
        lx, ly = x, y + r + 36
    elif lab == '0':
        lx, ly = cx + 34, cy - 20
    elif lab == 'b':
        lx, ly = x, y - r - 28
    else:                       # a, c0: straight below their beads
        lx, ly = x, y + r + 30
    L.mtext(dr, (lx, ly), parts, 42, fill=(235, 238, 255), alpha=235)
for m in range(13):
    x, y = hour_xy(m, R + 58)
    L.label(dr, (x, y), str(m), key='sansl', size=34, fill=(219, 230, 255), alpha=200)
for jj in range(12):
    a, b = P[jj], P[jj + 1]
    m = (a + b) / 2; v = b - a; n = np.array([v[1], -v[0]]) / np.linalg.norm(v)
    L.label(dr, tuple(m + 30 * n), str(jj + 1), key='sansl', size=27, fill=(219, 230, 255), alpha=175)
L.mtext(dr, (tx + 44, oy + 2), [('13', 'sqrt')], 56, fill=(255, 214, 150), alpha=245, anchor='lm')
L.label(dr, (ox - 34, oy + 40), '0', key='math', size=34, fill=(255, 214, 150), alpha=220)
L.save(out, 'r5_thirteen_hours', lay)
