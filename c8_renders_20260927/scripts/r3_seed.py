"""Render 3 (2D): the defining field u as three interfering waves.

u = e^{a1} + zeta' e^{a2} + conj(zeta') e^{a3}; in the positive unitary basis
the coefficients are (1, zeta, conj zeta) up to a common scale, with
zeta = (sqrt13 + 3 sqrt(-3))/sqrt40 and |zeta| = 1 because 13 + 27 = 40.
The momenta a_j have norm 4 and pairwise inner product 2, so relative to
their centroid they are three wave vectors at 120 degrees.  We draw the
classical profile f(x) = sum_j c_j exp(i k_j . x) on the plane they span:
brightness |f|^2/9, colour arg f.  Its zeros form a honeycomb of phase
vortices.
"""
import numpy as np
import look as L
from e8data import gram

G = gram()
R = np.linalg.cholesky(G).T
a = np.array([[0, 0, 0, 0, 0, -1, 1, 1],
              [0, 0, 0, 1, 1, -1, 0, 0],
              [1, 1, 0, 0, 0, -1, 0, 0]], float)
A = a @ R.T                                   # Euclidean momenta
gm = A @ A.T
assert np.allclose(gm, [[4, 2, 2], [2, 4, 2], [2, 2, 4]])
cen = A.mean(0)
K = A - cen
e1 = K[0] / np.linalg.norm(K[0])
e2 = K[1] - (K[1] @ e1) * e1; e2 /= np.linalg.norm(e2)
k2d = np.stack([K @ e1, K @ e2], 1)            # three planar wave vectors
assert np.allclose(np.linalg.norm(k2d, axis=1), 2 / np.sqrt(3))
zeta = (np.sqrt(13) + 3j * np.sqrt(3)) / np.sqrt(40)
assert abs(abs(zeta) - 1) < 1e-12
c = np.array([1, zeta, np.conj(zeta)])

W, H = L.W, L.H
scale = 0.0080                                  # lattice units per pixel
OX, OY = W * 0.62, H * 0.50
y, x = np.mgrid[0:H, 0:W].astype(np.float64)
X = (x - OX) * scale
Y = (y - OY) * scale
E = [c[j] * np.exp(1j * (k2d[j, 0] * X + k2d[j, 1] * Y)) for j in range(3)]
f = E[0] + E[1] + E[2]
I = np.abs(f) ** 2 / 9.0
ph = np.angle(f)
# analytic phase gradient (radians per pixel): Im(conj f grad f)/|f|^2
gx = sum(1j * k2d[j, 0] * E[j] for j in range(3))
gy = sum(1j * k2d[j, 1] * E[j] for j in range(3))
den = np.maximum(np.abs(f) ** 2, 1e-9)
gph = np.hypot((np.conj(f) * gx).imag / den, (np.conj(f) * gy).imag / den) * scale

# cyclic palette through the series colours
stops = [L.PAL['gold'], L.PAL['coral'], L.PAL['violet'], L.PAL['teal'], L.PAL['gold']]
t = (ph + np.pi) / (2 * np.pi) * 4
i0 = np.floor(t).astype(int) % 4
fr = (t - np.floor(t))[..., None]
S = np.array(stops)
hue = S[i0] * (1 - fr) + S[i0 + 1] * fr

img = L.backdrop(center=(0.62, 0.5), strength=0.8, seed=3)
fade = np.clip((x - W * 0.31) / (W * 0.20), 0, 1) ** 1.6
glow = (I ** 2.2 * 1.5)[..., None] * hue
# crisp isophase filaments every pi/3, constant width in pixels
wrapped = np.angle(np.exp(3j * ph))
dist = np.abs(wrapped) / np.maximum(3 * gph, 1e-9)
lines = np.exp(-(dist / 0.85) ** 2) * np.clip(np.sqrt(I) * 2.2, 0, 1)
glow += (0.26 * lines)[..., None] * L.PAL['ice'][None, None]
# crisp intensity contours |f|^2/9 = 0.1, 0.2, ..., 0.9, coloured by phase
gI = np.hypot(*np.gradient(I))                   # per pixel
lev = I * 10
dI = np.abs(lev - np.round(lev)) / 10 / np.maximum(gI, 1e-9)
cont = np.exp(-(dI / 0.9) ** 2) * (np.round(lev) >= 1) * (np.round(lev) <= 9)
glow += (0.85 * cont)[..., None] * hue
img += glow * fade[..., None]

# vortices: 1 + zeta e^{i q2.x} + conj(zeta) e^{i q3.x} = 0
q = np.stack([k2d[1] - k2d[0], k2d[2] - k2d[0]])
th = np.angle(zeta)
Qi = np.linalg.inv(q)
vort = []
for sgn, (p2, p3) in ((1, (2 * np.pi / 3, 4 * np.pi / 3)), (-1, (4 * np.pi / 3, 2 * np.pi / 3))):
    for m in range(-40, 41):
        for n in range(-40, 41):
            v = Qi @ np.array([p2 - th + 2 * np.pi * m, p3 + th + 2 * np.pi * n])
            px_, py_ = OX + v[0] / scale, OY + v[1] / scale
            if -20 < px_ < W + 20 and -20 < py_ < H + 20:
                vort.append((px_, py_, sgn))
for px_, py_, sgn in vort:
    fd = float(np.clip((px_ - W * 0.31) / (W * 0.20), 0, 1) ** 1.6)
    if fd > 0.02:
        L.ring(img, px_, py_, 7.5 if sgn > 0 else 4.5, L.PAL['ice'], width=1.6, intensity=0.9 * fd)
chk = [abs(1 + zeta * np.exp(1j * (q[0] @ ((np.array([a, b]) - [OX, OY]) * scale)))
           + np.conj(zeta) * np.exp(1j * (q[1] @ ((np.array([a, b]) - [OX, OY]) * scale))))
       for a, b, _ in vort[:20]]
assert max(chk) < 1e-9, max(chk)

# the phasor diagram: unit circle and the three coefficients
cx, cy, Rr = W * 0.165, H * 0.50, 250
L.ring(img, cx, cy, Rr, L.PAL['ice'], width=1.6, intensity=0.35)
for s in range(24):
    th = 2 * np.pi * s / 24
    r0 = Rr - (14 if s % 6 == 0 else 7)
    L.segments(img, [[cx + r0 * np.cos(th), cy - r0 * np.sin(th)]],
               [[cx + Rr * np.cos(th), cy - Rr * np.sin(th)]], L.PAL['ice'] * 0.5, 1.0, 2.0)
# axes
L.segments(img, [[cx - Rr - 40, cy], [cx, cy + Rr + 40]], [[cx + Rr + 40, cy], [cx, cy - Rr - 40]],
           L.PAL['ice'] * 0.18, 1.0, 2.0)
# right triangle: sqrt13 along the real axis, 3 sqrt3 up, hypotenuse sqrt40 (scaled to 1)
zx, zy = cx + Rr * zeta.real, cy - Rr * zeta.imag
dash = np.linspace(0, 1, 30)
for s in range(0, 30, 2):
    L.segments(img, [[zx, cy + (zy - cy) * dash[s]]], [[zx, cy + (zy - cy) * dash[s + 1]]],
               L.PAL['ice'] * 0.6, 1.0, 2.0)
for colr, z, wdt in ((L.PAL['gold'], 1 + 0j, 1.0), (L.PAL['coral'], zeta, 1.0),
                     (L.PAL['teal'], np.conj(zeta), 1.0)):
    ex, ey = cx + Rr * z.real, cy - Rr * z.imag
    for off in (-1.2, 0, 1.2):
        n = np.array([-(ey - cy), ex - cx]); n /= np.linalg.norm(n)
        L.segments(img, [[cx + off * n[0], cy + off * n[1]]], [[ex + off * n[0], ey + off * n[1]]],
                   colr * 1.6, 1.0, 2.0)
    L.disc(img, ex, ey, 9, colr * 3.0, halo=0.35, halo_r=3.5)
L.disc(img, cx, cy, 4, L.PAL['ice'] * 1.5)

img = L.bloom(img, threshold=0.55, strength=0.85)
out = L.finish(img, exposure=1.1, seed=3, grain=0.010)
lay, d = L.overlay()
MI = L.MI
L.mtext(d, (cx + Rr + 30, cy + 34), [('1', 'n')], 46, fill=(255, 214, 150), anchor='lm')
L.mtext(d, (zx + 22, zy - 24), [(MI['zeta'], 'n')], 52, fill=(255, 170, 195), anchor='lm')
L.mtext(d, (zx + 22, 2 * cy - zy + 30), [(MI['zeta'], 'bar')], 52, fill=(160, 245, 238), anchor='lm')
L.mtext(d, ((cx + zx) / 2, cy + 40), [('13', 'sqrt')], 36, alpha=220)
L.mtext(d, (zx + 18, (cy + zy) / 2 + 30), [('3', 'n'), ('3', 'sqrt')], 36, anchor='lm', alpha=220)
L.mtext(d, ((cx + zx) / 2 - 34, (cy + zy) / 2 - 26), [('40', 'sqrt')], 36, anchor='rm', alpha=220)
L.mtext(d, (cx, cy + Rr + 110), [('13 + 27 = 40', 'n')], 46, alpha=230)
L.save(out, 'r3_seed_field', lay)
print('vortices drawn', len(vort))
