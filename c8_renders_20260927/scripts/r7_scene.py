"""Render 7 (Blender): two full theories at c = 8 as two cities of states.

Each bar stands at (h, hbar) with height proportional to log10 of the exact
number of Virasoro-primary components there (c8_physics_20260927/data).
Left: diagonal U theory (12 sectors; colour = gold for integer-weight
sectors 0,b,a,c0, violet for c1,c2, coral for d1..d6).  Right: the E8
extension.  Bars on the diagonal h = hbar < 1 are the relevant scalars
(glowing caps); the floor marks Delta = h + hbar = 2.
"""
import csv
import math
import os
import sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(__file__))
import bpy
import numpy as np
import bl_common as B

DATA = B.ROOT.parent / 'c8_physics_20260927' / 'data'
HMAX = 3
S = 2.6            # Blender units per unit of conformal weight
SZ = 0.40          # Blender units per decade of multiplicity
FOOT = 0.14

diag = {}
for r in csv.DictReader(open(DATA / 'diagonal_sector_spectrum.tsv'), delimiter='\t'):
    h, hb = F(r['h_left']), F(r['h_right'])
    if h <= HMAX and hb <= HMAX:
        key = (h, hb)
        cls = 'gold' if r['sector'] in ('0', 'b', 'a', 'c0') else (
            'violet' if r['sector'] in ('c1', 'c2') else 'coral')
        n, c = diag.get(key, (0, cls))
        diag[key] = (n + int(r['Virasoro_primaries']), cls)
e8 = {}
for r in csv.DictReader(open(DATA / 'e8_spectrum.tsv'), delimiter='\t'):
    D, s = F(r['Delta']), F(r['spin'])
    h, hb = (D + s) / 2, (D - s) / 2
    if h <= HMAX and hb <= HMAX and int(r['Virasoro_primaries']) > 0:
        e8[(h, hb)] = (int(r['Virasoro_primaries']), 'gold')
rel = sorted((k, v[0]) for k, v in diag.items() if k[0] == k[1] and 0 < k[0] < 1)
assert [n for _, n in rel] == [9, 25, 49, 169, 196, 729, 1764], rel
assert not any(k[0] == k[1] and 0 < k[0] < 1 for k in e8)

sc = B.reset(width=1200, height=1350, samples=160, noise=0.015)
B.world(color=(0.010, 0.014, 0.045), strength=0.7)

# floor texture: weight grid, the scalar diagonal and the line Delta = 2
lo, hi = -0.45, HMAX + 0.45
TWp = 2400
g = np.linspace(lo, hi, TWp)
X, Y = np.meshgrid(g, g)                 # row 0 = bottom
ppu = TWp / (hi - lo)
def line_dist(v):                         # distance in texels to nearest integer
    return np.abs(v - np.round(v)) * ppu
base = np.array(B.COL['ink']) * 1.6
col = np.broadcast_to(base, X.shape + (3,)).copy()
relevant = (X + Y < 2) & (X >= -0.02) & (Y >= -0.02)
col[relevant] = col[relevant] * 0.4 + np.array(B.COL['navy']) * 0.9
inside = (X > -0.05) & (Y > -0.05) & (X < HMAX + 0.05) & (Y < HMAX + 0.05)
grid = (np.exp(-(line_dist(X) / 1.3) ** 2) + np.exp(-(line_dist(Y) / 1.3) ** 2)) * inside
col += grid[..., None] * np.array(B.COL['ice']) * 0.35
diag_d = np.abs(X - Y) / math.sqrt(2) * ppu
col += (np.exp(-(diag_d / 1.6) ** 2) * inside)[..., None] * np.array(B.COL['gold']) * 0.9
mar_d = np.abs(X + Y - 2) / math.sqrt(2) * ppu
col += (np.exp(-(mar_d / 1.8) ** 2) * inside)[..., None] * np.array(B.COL['coral']) * 1.2
img = bpy.data.images.new('floor', TWp, TWp, float_buffer=True, alpha=True)
img.pixels.foreach_set(np.concatenate([col, np.ones(X.shape + (1,))], 2).astype(np.float32).ravel())
del col, grid, diag_d, mar_d, X, Y, relevant, inside
bpy.ops.mesh.primitive_plane_add(size=(hi - lo) * S, location=((lo + hi) / 2 * S, (lo + hi) / 2 * S, 0))
fl = bpy.context.active_object
fm = bpy.data.materials.new('floor'); fm.use_nodes = True
fb = fm.node_tree.nodes['Principled BSDF']
tx = fm.node_tree.nodes.new('ShaderNodeTexImage'); tx.image = img
fm.node_tree.links.new(tx.outputs['Color'], fb.inputs['Base Color'])
fm.node_tree.links.new(tx.outputs['Color'], fb.inputs['Emission Color'])
fb.inputs['Emission Strength'].default_value = 1.0
fb.inputs['Roughness'].default_value = 0.35
fb.inputs['Coat Weight'].default_value = 0.3
B.assign(fl, fm)

mats = {k: B.mat_principled(k, base=tuple(min(1, 0.85 * c) for c in B.COL[k]), rough=0.35,
                            emission=B.COL[k], emit_strength=0.55, coat=0.3)
        for k in ('gold', 'violet', 'coral')}
cap = B.mat_emission('cap', B.COL['ice'], 18.0)
coll = {}
for name, data in (('diag', diag), ('e8', e8)):
    cl = bpy.data.collections.new(name); sc.collection.children.link(cl); coll[name] = cl
    for (h, hb), (n, cls) in data.items():
        z = max(0.03, SZ * math.log10(1 + n))
        bpy.ops.mesh.primitive_cube_add(size=1, location=(float(h) * S, float(hb) * S, z / 2))
        o = bpy.context.active_object
        o.scale = (FOOT, FOOT, z)
        for c in o.users_collection:
            c.objects.unlink(o)
        cl.objects.link(o)
        B.assign(o, mats[cls])
        if h == hb and 0 < h < 1:
            bpy.ops.mesh.primitive_cube_add(size=1, location=(float(h) * S, float(hb) * S, z + 0.02))
            c2 = bpy.context.active_object
            c2.scale = (FOOT * 1.02, FOOT * 1.02, 0.04)
            for c in c2.users_collection:
                c.objects.unlink(c2)
            cl.objects.link(c2)
            B.assign(c2, cap)

B.area_light((-3, -6, 10), (4, 4, 0), 10, 1400, color=(0.9, 0.93, 1.0), name='key')
B.area_light((12, 2, 5), (4, 4, 1), 6, 500, color=(1.0, 0.8, 0.6), name='rim', glossy=False)
th = math.radians(246)          # swung off the h = hbar diagonal so the scalar towers separate
cx0 = 1.45 * S
cam = B.camera((cx0 + 10.5 * math.cos(th), cx0 + 10.5 * math.sin(th), 8.8), (cx0, cx0 + 0.3, 0.3),
               lens=35, dof_target=(1.2, 1.2, 0.3), fstop=11.0)

anch = dict(origin=B.project([(0, 0, 0)])[0], two=B.project([(2 * S, 0, 0), (0, 2 * S, 0)]))
for name in ('diag', 'e8'):
    for other in coll:
        coll[other].hide_render = (other != name)
    B.render(f'r7_city_{name}', anch)
