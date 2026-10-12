"""Render 4 (Blender): the order-thirteen gluing of the Fib x SO(3)_13 core.

The pointed charges (j,k) in (Z/13)^2 of the lattice-Potts core and the
level-13 parafermions carry the quadratic form -(j^2+k^2)/13.  Because
5^2 = -1 (mod 13) its isotropic lines are exactly k = -5j and k = 5j.  On
the torus (Z/13)^2 inside (R/Z)^2 these are (1,-5) and (1,5) torus knots.
The certified field witness has charge (5,1), which lies on k = -5j: in the
manuscript's orientation convention that is the realized line (coral).  The
other line k = 5j (violet) cannot also occur.  They meet only at the vacuum
(0,0) (gold).
"""
import math
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
import bpy
from mathutils import Vector
import bl_common as B

N = 13
RMAJ, RMIN = 3.25, 1.30

sc = B.reset(samples=192, noise=0.014)
B.world(color=(0.010, 0.014, 0.045), strength=0.7)


def P(theta, phi, lift=0.0):
    t = theta - math.pi / 2          # theta = 0 faces the camera (-y)
    r = RMIN + lift
    return Vector(((RMAJ + r * math.cos(phi)) * math.cos(t),
                   (RMAJ + r * math.cos(phi)) * math.sin(t),
                   r * math.sin(phi)))


body = B.mat_principled('body', base=(0.006, 0.010, 0.030), rough=0.5, coat=0.18)
bpy.ops.mesh.primitive_torus_add(major_radius=RMAJ, minor_radius=RMIN, major_segments=192,
                                 minor_segments=96, location=(0, 0, 0))
tor = bpy.context.active_object
bpy.ops.object.shade_smooth()
B.assign(tor, body)

grid = B.mat_emission('grid', B.COL['ice'], 0.22)
for a in range(N):
    th = 2 * math.pi * a / N
    B.tube([tuple(P(th, 2 * math.pi * s / 160, 0.004)) for s in range(160)], 0.007, grid,
           name=f'mer{a}', closed=True)
    ph = 2 * math.pi * a / N
    B.tube([tuple(P(2 * math.pi * s / 320, ph, 0.004)) for s in range(320)], 0.007, grid,
           name=f'lon{a}', closed=True)

dot = B.mat_emission('dot', B.COL['ice'], 1.3)
coral = B.mat_emission('coral', B.COL['coral'], 9.0)
coral_bead = B.mat_emission('coralbead', B.COL['coral'], 22.0)
violet = B.mat_emission('violet', B.COL['violet'], 2.4)
gold = B.mat_emission('gold', B.COL['gold'], 26.0)

iso_p = {(j, (-5 * j) % N) for j in range(N)}   # realized (coral)
iso_m = {(j, (5 * j) % N) for j in range(N)}    # excluded (violet)
assert (5, 1) in iso_p
for j in range(N):
    for k in range(N):
        assert ((j * j + k * k) % N == 0) == ((j, k) in iso_p | iso_m)
        th, ph = 2 * math.pi * j / N, 2 * math.pi * k / N
        if (j, k) == (0, 0):
            B.sphere(P(th, ph, 0.02), 0.17, gold, seg=48, rings=24, name='vac')
        elif (j, k) in iso_p:
            B.sphere(P(th, ph, 0.02), 0.115, coral_bead, seg=40, rings=20, name=f'p{j}{k}')
        elif (j, k) in iso_m:
            B.sphere(P(th, ph, 0.02), 0.075, violet, seg=32, rings=16, name=f'm{j}{k}')
        else:
            B.sphere(P(th, ph, 0.01), 0.045, dot, seg=24, rings=12, name=f'd{j}{k}')

# the two isotropic lines as continuous torus knots through their lattice points
M = 1300
knot_p = [tuple(P(2 * math.pi * s / M, -5 * 2 * math.pi * s / M, 0.035)) for s in range(M)]
knot_m = [tuple(P(2 * math.pi * s / M, 5 * 2 * math.pi * s / M, 0.03)) for s in range(M)]
B.tube(knot_p, 0.030, coral, name='kp', closed=True)
B.tube(knot_m, 0.014, violet, name='km', closed=True)

B.area_light((-5, -6, 9), (0, 0, 0), 8, 380, color=(1.0, 0.95, 0.9), name='key')
B.area_light((4, 8, 3), (0, 0, 0), 6, 420, color=(0.6, 0.75, 1.0), name='rim', glossy=True)
cam = B.camera((0.0, -13.8, 9.0), (0.0, 0.0, -0.55), lens=37, dof_target=tuple(P(0, 0)), fstop=9.0)

# label anchors: vacuum, and a front point on each knot
a_vac = P(0, 0, 0.2)
a_p = P(-2 * math.pi * 1.5 / N, 5 * 2 * math.pi * 1.5 / N, 0.2)   # on k = -5j
a_m = P(2 * math.pi * 1.5 / N, 5 * 2 * math.pi * 1.5 / N, 0.2)    # on k = 5j
pr = B.project([tuple(a_vac), tuple(a_p), tuple(a_m)])
B.render('r4_torus', dict(vac=pr[0], plus=pr[1], minus=pr[2]))
