"""Blender-side helpers (run inside `blender -b --python`).

Scenes render with a transparent film to linear EXR; the float pixels are
dumped to .npy so that the shared post pipeline (look.py) composites them
over the series backdrop, blooms, tone-maps and labels them.
"""
import json
import math
from pathlib import Path

import bpy
import numpy as np
from bpy_extras.object_utils import world_to_camera_view
from mathutils import Vector

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'work'


def srgb_to_lin(hexstr):
    h = hexstr.lstrip('#')
    c = [int(h[i:i + 2], 16) / 255 for i in (0, 2, 4)]
    return tuple(x / 12.92 if x <= 0.04045 else ((x + 0.055) / 1.055) ** 2.4 for x in c)


HEX = dict(ink='#070b1d', navy='#131c46', gold='#ffb347', teal='#27e1d1',
           coral='#ff4d7e', violet='#8e7bff', ice='#dbe6ff')
COL = {k: srgb_to_lin(v) for k, v in HEX.items()}


def reset(width=2400, height=1350, samples=192, noise=0.015, bounces=10, denoise=True):
    import os
    scale = float(os.environ.get('R_SCALE', '1'))
    samples = int(os.environ.get('R_SAMPLES', samples))
    width, height = int(width * scale), int(height * scale)
    bpy.ops.wm.read_factory_settings(use_empty=True)
    sc = bpy.context.scene
    sc.render.engine = 'CYCLES'
    sc.cycles.device = 'CPU'
    sc.render.threads_mode = 'FIXED'
    sc.render.threads = 2
    sc.cycles.samples = samples
    sc.cycles.use_adaptive_sampling = True
    sc.cycles.adaptive_threshold = noise
    sc.cycles.max_bounces = bounces
    sc.cycles.transmission_bounces = bounces
    sc.cycles.glossy_bounces = 6
    sc.cycles.transparent_max_bounces = 16
    try:
        sc.cycles.use_denoising = denoise
        sc.cycles.denoiser = 'OPENIMAGEDENOISE'
        sc.cycles.denoising_prefilter = 'FAST'
        sc.cycles.denoising_quality = 'BALANCED'
    except Exception as e:  # pragma: no cover
        print('denoiser unavailable:', e)
    sc.render.resolution_x = width
    sc.render.resolution_y = height
    sc.render.resolution_percentage = 100
    sc.render.film_transparent = True
    sc.render.image_settings.file_format = 'OPEN_EXR'
    sc.render.image_settings.color_depth = '32'
    sc.render.image_settings.color_mode = 'RGBA'
    sc.view_settings.view_transform = 'Standard' if 'Standard' in [
        i.identifier for i in sc.view_settings.bl_rna.properties['view_transform'].enum_items] else sc.view_settings.view_transform
    return sc


def world(color=(0.004, 0.006, 0.02), strength=1.0):
    sc = bpy.context.scene
    w = bpy.data.worlds.new('world')
    sc.world = w
    w.use_nodes = True
    bg = w.node_tree.nodes['Background']
    bg.inputs[0].default_value = (*color, 1)
    bg.inputs[1].default_value = strength
    return w


def mat_principled(name, base=(0.8, 0.8, 0.8), rough=0.4, metal=0.0, transmission=0.0,
                   ior=1.45, emission=None, emit_strength=0.0, coat=0.0, alpha=1.0):
    m = bpy.data.materials.new(name)
    m.use_nodes = True
    b = m.node_tree.nodes['Principled BSDF']
    b.inputs['Base Color'].default_value = (*base, 1)
    b.inputs['Roughness'].default_value = rough
    b.inputs['Metallic'].default_value = metal
    b.inputs['IOR'].default_value = ior
    b.inputs['Transmission Weight'].default_value = transmission
    b.inputs['Coat Weight'].default_value = coat
    b.inputs['Alpha'].default_value = alpha
    if emission is not None:
        b.inputs['Emission Color'].default_value = (*emission, 1)
        b.inputs['Emission Strength'].default_value = emit_strength
    return m


def mat_emission(name, color, strength):
    m = bpy.data.materials.new(name)
    m.use_nodes = True
    nt = m.node_tree
    for n in list(nt.nodes):
        nt.nodes.remove(n)
    e = nt.nodes.new('ShaderNodeEmission')
    e.inputs[0].default_value = (*color, 1)
    e.inputs[1].default_value = strength
    o = nt.nodes.new('ShaderNodeOutputMaterial')
    nt.links.new(e.outputs[0], o.inputs[0])
    return m


def assign(obj, mat):
    obj.data.materials.clear()
    obj.data.materials.append(mat)
    return obj


def sphere(loc, r, mat, seg=96, rings=48, name='sphere'):
    bpy.ops.mesh.primitive_uv_sphere_add(segments=seg, ring_count=rings, radius=r, location=loc)
    o = bpy.context.active_object
    o.name = name
    bpy.ops.object.shade_smooth()
    return assign(o, mat)


def tube(points, radius, mat, name='tube', resolution=24, closed=False):
    cu = bpy.data.curves.new(name, 'CURVE')
    cu.dimensions = '3D'
    cu.bevel_depth = radius
    cu.bevel_resolution = 8
    cu.use_fill_caps = True
    sp = cu.splines.new('POLY')
    sp.points.add(len(points) - 1)
    for p, q in zip(sp.points, points):
        p.co = (*q, 1)
    sp.use_cyclic_u = closed
    o = bpy.data.objects.new(name, cu)
    bpy.context.scene.collection.objects.link(o)
    o.data.materials.append(mat)
    return o


def plane(size, z, mat, name='floor'):
    bpy.ops.mesh.primitive_plane_add(size=size, location=(0, 0, z))
    o = bpy.context.active_object
    o.name = name
    return assign(o, mat)


def area_light(loc, target, size, energy, color=(1, 1, 1), name='light', glossy=True):
    l = bpy.data.lights.new(name, 'AREA')
    l.size = size
    l.energy = energy
    l.color = color
    o = bpy.data.objects.new(name, l)
    bpy.context.scene.collection.objects.link(o)
    o.location = loc
    look_at(o, target)
    o.visible_camera = False
    o.visible_glossy = glossy
    return o


def look_at(obj, target):
    d = Vector(target) - obj.location
    obj.rotation_euler = d.to_track_quat('-Z', 'Y').to_euler()


def camera(loc, target, lens=50, dof_target=None, fstop=4.0, name='cam'):
    sc = bpy.context.scene
    c = bpy.data.cameras.new(name)
    c.lens = lens
    o = bpy.data.objects.new(name, c)
    sc.collection.objects.link(o)
    o.location = loc
    look_at(o, target)
    sc.camera = o
    if dof_target is not None:
        c.dof.use_dof = True
        c.dof.focus_distance = (Vector(dof_target) - Vector(loc)).length
        c.dof.aperture_fstop = fstop
    return o


def project(points):
    """Pixel coordinates (x right, y down) of world points in the active camera."""
    sc = bpy.context.scene
    bpy.context.view_layer.update()
    W, H = sc.render.resolution_x, sc.render.resolution_y
    out = []
    for p in points:
        v = world_to_camera_view(sc, sc.camera, Vector(p))
        out.append((v.x * W, (1 - v.y) * H, v.z))
    return out


def render(name, anchors=None):
    WORK.mkdir(exist_ok=True)
    sc = bpy.context.scene
    exr = WORK / f'{name}.exr'
    sc.render.filepath = str(exr)
    bpy.ops.render.render(write_still=True)
    img = bpy.data.images.load(str(exr))
    W, H = img.size
    px = np.empty(W * H * 4, np.float32)
    img.pixels.foreach_get(px)
    px = px.reshape(H, W, 4)[::-1].copy()
    np.save(WORK / f'{name}.npy', px)
    if anchors is not None:
        (WORK / f'{name}_anchors.json').write_text(json.dumps(anchors, indent=1))
    print('saved', name, px.shape, float(px[..., :3].max()))
