import bpy
bpy.ops.wm.read_factory_settings(use_empty=True)
sc = bpy.context.scene
sc.render.engine = 'CYCLES'
sc.cycles.device = 'CPU'
sc.cycles.samples = 16
sc.render.threads_mode = 'FIXED'; sc.render.threads = 2
sc.render.resolution_x = 320; sc.render.resolution_y = 200
bpy.ops.mesh.primitive_uv_sphere_add(radius=1)
cam = bpy.data.objects.new('cam', bpy.data.cameras.new('cam')); sc.collection.objects.link(cam)
cam.location = (0, -5, 0); cam.rotation_euler = (1.5708, 0, 0); sc.camera = cam
w = bpy.data.worlds.new('w'); sc.world = w; w.use_nodes = True
w.node_tree.nodes['Background'].inputs[0].default_value = (0.2, 0.3, 0.5, 1)
sc.render.filepath = '/home/tzuchen/Codes/haagerup/c8_renders_20260927/work/pilot.png'
bpy.ops.render.render(write_still=True)
print('DENOISERS', [d for d in dir(sc.cycles) if 'denois' in d][:8])
