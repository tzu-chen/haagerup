"""Render 1 (Blender): the fusion graph of rho in the Haagerup category H3.

Vertices are the six simple objects; an edge joins x and y when y occurs in
rho (x) x.  Sphere radii are the Perron-Frobenius eigenvector of that graph,
i.e. the quantum dimensions 1 (gold: 1, alpha, alpha^2) and
d = (3 + sqrt 13)/2 (teal glass: rho, alpha rho, alpha^2 rho).
"""
import math
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
import bpy
from mathutils import Vector
import bl_common as B

d = (3 + math.sqrt(13)) / 2
RT = 0.95
RG = RT / d
RC = 2.75
Z0 = 1.35

sc = B.reset(samples=224, noise=0.014)
B.world(color=(0.010, 0.014, 0.045), strength=0.8)

teal_glass = B.mat_principled('glass', base=(0.72, 0.98, 0.95), rough=0.02, transmission=1.0,
                              ior=1.47, coat=0.0)
teal_core = B.mat_emission('tealcore', B.COL['teal'], 14.0)
teal_line = B.mat_emission('tealline', B.COL['teal'], 7.0)
loop_line = B.mat_emission('loopline', tuple(0.55 * a + 0.45 * b for a, b in zip(B.COL['teal'], B.COL['ice'])), 6.0)
gold_ball = B.mat_emission('gold', B.COL['gold'], 8.0)
gold_line = B.mat_emission('goldline', B.COL['gold'], 5.0)

# floor: dark lacquer that fades out radially
floor = B.mat_principled('floor', base=(0.006, 0.009, 0.025), rough=0.30, coat=0.0)
nt = floor.node_tree
tc = nt.nodes.new('ShaderNodeTexCoord')
ln = nt.nodes.new('ShaderNodeVectorMath'); ln.operation = 'LENGTH'
mr = nt.nodes.new('ShaderNodeMapRange')
mr.inputs['From Min'].default_value = 5.5
mr.inputs['From Max'].default_value = 13.0
mr.inputs['To Min'].default_value = 1.0
mr.inputs['To Max'].default_value = 0.0
nt.links.new(tc.outputs['Object'], ln.inputs[0])
nt.links.new(ln.outputs['Value'], mr.inputs['Value'])
nt.links.new(mr.outputs['Result'], nt.nodes['Principled BSDF'].inputs['Alpha'])
B.plane(40, 0.0, floor)

names_t = ['rho', 'alpha rho', 'alpha^2 rho']
names_g = ['1', 'alpha^2', 'alpha']       # 1-rho, alpha^2-(alpha rho), alpha-(alpha^2 rho)
T, Gp = [], []
for k in range(3):
    th = math.radians(90 + 120 * k)
    c = Vector((RC * math.cos(th), RC * math.sin(th), Z0))
    T.append(c)
    B.sphere(c, RT, teal_glass, name=f'T{k}')
    B.sphere(c, 0.36 * RT, teal_core, name=f'Tcore{k}')
    # satellite: an invertible object, radius 1/d of rho's
    g = c + Vector((math.cos(th), math.sin(th), 0)) * 2.05
    g.z = Z0 - 0.15
    Gp.append(g)
    B.sphere(g, RG, gold_ball, name=f'G{k}')
    a = c + (g - c).normalized() * (RT + 0.02)
    b = g - (g - c).normalized() * (RG + 0.01)
    B.tube([tuple(a), tuple(b)], 0.028, gold_line, name=f'gl{k}')
    # self-loop: rho occurs in rho (x) rho -- a tilted ring round the sphere
    ring = []
    tilt = math.radians(62)
    u = Vector((math.cos(th), math.sin(th), 0))      # radial
    v = Vector((-math.sin(th), math.cos(th), 0))     # tangential
    w = Vector((0, 0, 1))
    for s in range(200):
        phi = 2 * math.pi * s / 200
        p = (u * math.cos(phi) + (w * math.cos(tilt) + v * math.sin(tilt)) * math.sin(phi)) * 1.42
        ring.append(tuple(c + p))
    B.tube(ring, 0.022, loop_line, name=f'loop{k}', closed=True)

# the triangle of rho-type edges: gentle arcs between sphere surfaces
for i in range(3):
    for j in range(i + 1, 3):
        a, b = T[i], T[j]
        mid = (a + b) / 2 + Vector((0, 0, 0.55))
        pts = []
        for s in range(81):
            t = s / 80
            p = (1 - t) ** 2 * a + 2 * (1 - t) * t * mid + t ** 2 * b
            pts.append(p)
        pts = [p for p in pts if (p - a).length > RT + 0.02 and (p - b).length > RT + 0.02]
        B.tube([tuple(p) for p in pts], 0.04, teal_line, name=f'e{i}{j}')

B.area_light((-6, -5, 9), (0, 0, 1), 7, 900, color=(1.0, 0.93, 0.85), name='key')
B.area_light((5, 7, 4), (0, 0, 1.2), 5, 500, color=(0.55, 0.9, 1.0), name='rim', glossy=False)
B.area_light((0, -9, 1.5), (0, 0, 1.2), 8, 120, color=(0.75, 0.75, 1.0), name='fill', glossy=False)

cam = B.camera((0.0, -11.6, 12.6), (0.0, 0.95, 0.30), lens=40, dof_target=(0, -0.6, 1.3), fstop=7.0)

anchors = dict(teal=[list(p) for p in B.project([tuple(p) for p in T])],
               gold=[list(p) for p in B.project([tuple(p) for p in Gp])],
               names_t=names_t, names_g=names_g, RT=RT, RG=RG, d=d)
B.render('r1_fusion', anchors)
