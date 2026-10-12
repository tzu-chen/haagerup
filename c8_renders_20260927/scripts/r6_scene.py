"""Render 6 (Blender): the landscape of the exact four-point function

    G0(x) = <u^dag(inf) u(1) u^dag(x) u(0)> = (3 - 4x + 4x^2) / (3 x^4 (1-x)^4)

(correlators.tex, eq. physics-u-neutral) over the complex cross-ratio plane.
Height = log10|G0| (clipped), colour = arg G0, thin contours every 1/4 decade.
Order-four poles at x = 0, 1 (glowing calderas), simple zeros at
x = 1/2 +- i/sqrt2 (sinkholes); crossing symmetry x -> 1 - x is the mirror.
"""
import math
import os
import sys
sys.path.insert(0, os.path.dirname(__file__))
import bpy
import numpy as np
import bl_common as B

RE = (-2.0, 3.0)
IM = (-2.1, 2.1)
SX = 3.2          # Blender units per unit of x
SZ = 0.72         # Blender units per decade
HI, LO = 3.0, -2.2


def G0(z):
    return (3 - 4 * z + 4 * z * z) / (3 * z ** 4 * (1 - z) ** 4)


def logG(z):
    with np.errstate(divide='ignore', invalid='ignore'):
        v = np.log10(np.abs(G0(z)))
    return np.nan_to_num(v, nan=HI, posinf=HI, neginf=LO)


sc = B.reset(samples=320, noise=0.008, denoise=False)   # OIDN exceeds the 6 GiB cap here
B.world(color=(0.010, 0.014, 0.045), strength=0.6)

# --- colour texture -------------------------------------------------------
TW = 3600
TH = int(TW * (IM[1] - IM[0]) / (RE[1] - RE[0]))
xs = np.linspace(RE[0], RE[1], TW)
ys = np.linspace(IM[0], IM[1], TH)
Z = (xs[None, :] + 1j * ys[:, None]).astype(np.complex64)   # row 0 = bottom (Blender image order)
lg = logG(Z)
ph = np.angle(G0(Z))
stops = np.array([B.COL['gold'], B.COL['coral'], B.COL['violet'], B.COL['teal'], B.COL['gold']], np.float32)
ICE = np.array(B.COL['ice'], np.float32)
t = (ph + np.pi) / (2 * np.pi) * 4
i0 = np.floor(t).astype(int) % 4
fr = (t - np.floor(t)).astype(np.float32)[..., None]
hue = stops[i0] * (1 - fr) + stops[i0 + 1] * fr
lvl = np.clip((lg - LO) / (HI - LO), 0, 1).astype(np.float32)[..., None]
col = hue * (0.012 + 0.988 * lvl ** 1.7)
# contour lines: every quarter decade, stronger every decade
px_per_dec = np.hypot(*np.gradient(lg))            # decades per texel
def contour(step, width):
    f = lg / step
    dist = np.abs(f - np.round(f)) * step / np.maximum(px_per_dec, 1e-6)
    return np.exp(-(dist / width) ** 2)
lines = 0.35 * contour(0.25, 0.9) + 0.9 * contour(1.0, 1.3)
inside = (lg > LO + 0.02) & (lg < HI - 0.02)
col = col + (0.9 * lines * inside).astype(np.float32)[..., None] * ICE[None, None]
# calderas (poles) and sinkholes (zeros)
col[lg >= HI - 0.02] = np.array(B.COL['gold'], np.float32) * 4.0
col[(lg <= LO + 0.02) & (np.abs(G0(Z)) < 1e-2) & (np.abs(Z - 0.5) < 1.0)] = np.array(B.COL['teal'], np.float32) * 3.0
img = bpy.data.images.new('landscape', TW, TH, float_buffer=True, alpha=True)
# fade to transparent towards the edge of the domain (elliptical window)
er = np.hypot((Z.real - 0.5) / (0.5 * (RE[1] - RE[0])), Z.imag / (0.5 * (IM[1] - IM[0])))
alpha = np.clip((1.0 - er) / 0.28, 0, 1).astype(np.float32) ** 1.5
rgba = np.concatenate([col, alpha[..., None]], 2).astype(np.float32)
img.pixels.foreach_set(rgba.ravel())
del Z, lg, ph, hue, col, rgba, lines, inside, px_per_dec, t, i0, fr, lvl, er, alpha
import gc; gc.collect()

# --- mesh -------------------------------------------------------------------
bpy.ops.mesh.primitive_grid_add(x_subdivisions=1200, y_subdivisions=1000, size=1.0, calc_uvs=True)
obj = bpy.context.active_object
me = obj.data
n = len(me.vertices)
co = np.empty(n * 3, np.float32)
me.vertices.foreach_get('co', co)
co = co.reshape(-1, 3)
u = co[:, 0] + 0.5; v = co[:, 1] + 0.5
zr = RE[0] + u * (RE[1] - RE[0]); zi = IM[0] + v * (IM[1] - IM[0])
h = np.clip(logG(zr + 1j * zi), LO, HI)
co[:, 0] = (zr - 0.5) * SX
co[:, 1] = zi * SX
co[:, 2] = h * SZ
me.vertices.foreach_set('co', co.ravel())
me.update()
bpy.ops.object.shade_smooth()

m = bpy.data.materials.new('terrain')
m.use_nodes = True
nt = m.node_tree
bsdf = nt.nodes['Principled BSDF']
tex = nt.nodes.new('ShaderNodeTexImage'); tex.image = img; tex.interpolation = 'Cubic'
nt.links.new(tex.outputs['Color'], bsdf.inputs['Base Color'])
nt.links.new(tex.outputs['Color'], bsdf.inputs['Emission Color'])
nt.links.new(tex.outputs['Alpha'], bsdf.inputs['Alpha'])
bsdf.inputs['Emission Strength'].default_value = 0.8
bsdf.inputs['Roughness'].default_value = 0.42
bsdf.inputs['Coat Weight'].default_value = 0.25
B.assign(obj, m)

B.area_light((-7, 6, 9), (0, 0, 0), 9, 900, color=(0.85, 0.9, 1.0), name='key')
B.area_light((8, 8, 4), (0, 0, 0.5), 6, 500, color=(1.0, 0.8, 0.6), name='rim', glossy=False)
cam = B.camera((0.0, -11.6, 7.3), (0.0, 0.45, 0.10), lens=37,
               dof_target=(0.0, 0.0, 1.2), fstop=9.0)

anch = {}
for key, z in (('p0', 0 + 0j), ('p1', 1 + 0j), ('zf', 0.5 - 1j / math.sqrt(2)),
               ('zb', 0.5 + 1j / math.sqrt(2))):
    hz = float(np.clip(logG(np.array([z]))[0], LO, HI)) * SZ
    anch[key] = B.project([((z.real - 0.5) * SX, z.imag * SX, hz)])[0]
B.render('r6_landscape', anch)
