"""Shared visual language for the c=8 Haagerup renders.

Everything is accumulated as linear HDR light (float32, H x W x 3), then
bloomed, tone-mapped (ACES fit), graded, grained and saved.  Labels are
drawn afterwards with PIL so they stay crisp.
"""
from pathlib import Path
import numpy as np
from scipy import ndimage
from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'out'
WORK = ROOT / 'work'
W, H = 2400, 1350


def lin(hexstr):
    h = hexstr.lstrip('#')
    c = np.array([int(h[i:i + 2], 16) / 255 for i in (0, 2, 4)], np.float32)
    return np.where(c <= 0.04045, c / 12.92, ((c + 0.055) / 1.055) ** 2.4).astype(np.float32)


# One palette for the whole series.
# Series grade.  One set of knobs, applied identically to every render.
GRADE = dict(
    sat=0.58,            # saturation kept (1 = as rendered)
    bloom=0.35,          # glow strength multiplier
    bloom_threshold=1.6, # glow starts later
    exposure=0.86,       # keeps emissive cores from burning to white
    grain=1.35,          # film grain multiplier
    label_sat=0.55,      # saturation kept in label colours
)

HEX = dict(
    ink='#0b0f1c',      # deep night (less blue than before)
    navy='#1b2338',     # backdrop glow, muted slate
    gold='#ffb347',     # vacuum / invertible / E6+A2
    teal='#27e1d1',     # Haagerup rho, non-invertible
    coral='#ff4d7e',    # thirteen
    violet='#8e7bff',   # secondary
    ice='#dbe6ff',      # neutral light
)
PAL = {k: lin(v) for k, v in HEX.items()}

FONT = dict(
    sans='/usr/share/fonts/lato-fonts/Lato-Regular.ttf',
    sansb='/usr/share/fonts/lato-fonts/Lato-Bold.ttf',
    sansbl='/usr/share/fonts/lato-fonts/Lato-Black.ttf',
    sansl='/usr/share/fonts/lato-fonts/Lato-Light.ttf',
    math='/usr/share/fonts/lm-math/latinmodern-math.otf',
    it='/usr/share/fonts/lm/lmroman10-italic.otf',
    rm='/usr/share/fonts/lm/lmroman10-regular.otf',
)


def canvas(w=W, h=H):
    return np.zeros((h, w, 3), np.float32)


def backdrop(w=W, h=H, center=(0.5, 0.5), inner='navy', outer='ink',
             strength=1.0, seed=0, nebula=0.35):
    """Radial night gradient with faint large-scale nebulosity."""
    y, x = np.mgrid[0:h, 0:w].astype(np.float32)
    cx, cy = center[0] * w, center[1] * h
    r = np.sqrt(((x - cx) / w) ** 2 + ((y - cy) / w) ** 2)
    t = np.clip(1 - r / 0.75, 0, 1) ** 1.6 * strength
    rng = np.random.default_rng(seed)
    n = rng.normal(size=(h // 40 + 2, w // 40 + 2)).astype(np.float32)
    n = ndimage.gaussian_filter(n, 2.0)
    n = ndimage.zoom(n, (h / n.shape[0], w / n.shape[1]), order=3)[:h, :w]
    n = (n - n.min()) / (np.ptp(n) + 1e-9)
    t = np.clip(t * (1 - nebula + nebula * 2 * n), 0, 1.5)
    return (PAL[outer][None, None] * (1 - t[..., None]) +
            PAL[inner][None, None] * t[..., None]).astype(np.float32)


def splat(buf, x, y, rgb, weight=1.0):
    """Bilinear additive splat of points (x, y) with colour rgb (3,) or (N,3)."""
    h, w = buf.shape[:2]
    x = np.asarray(x, np.float64); y = np.asarray(y, np.float64)
    wt = np.broadcast_to(np.asarray(weight, np.float64), x.shape)
    rgb = np.asarray(rgb, np.float32)
    x0 = np.floor(x).astype(np.int64); y0 = np.floor(y).astype(np.int64)
    fx = x - x0; fy = y - y0
    flat = buf.reshape(-1, 3)
    idxs, vals = [], []
    for dx, dy, f in ((0, 0, (1 - fx) * (1 - fy)), (1, 0, fx * (1 - fy)),
                      (0, 1, (1 - fx) * fy), (1, 1, fx * fy)):
        xi = x0 + dx; yi = y0 + dy
        ok = (xi >= 0) & (xi < w) & (yi >= 0) & (yi < h)
        idxs.append(yi[ok] * w + xi[ok])
        vals.append((f * wt)[ok][:, None] * (rgb if rgb.ndim == 1 else rgb[ok]))
    idx = np.concatenate(idxs); val = np.concatenate(vals)
    for c in range(3):
        flat[:, c] += np.bincount(idx, weights=val[:, c], minlength=h * w).astype(np.float32)


def segments(buf, p0, p1, rgb, intensity=1.0, density=1.5, chunk=400_000):
    """Additively draw straight segments as light (intensity per pixel length)."""
    p0 = np.asarray(p0, np.float64); p1 = np.asarray(p1, np.float64)
    L = np.linalg.norm(p1 - p0, axis=1)
    n = np.maximum(2, np.ceil(L * density)).astype(np.int64)
    rgb = np.asarray(rgb, np.float32)
    per_rgb = rgb.ndim == 2
    seg_id = np.repeat(np.arange(len(p0)), n)
    starts = np.concatenate([[0], np.cumsum(n)[:-1]])
    t = (np.arange(n.sum()) - np.repeat(starts, n) + 0.5) / np.repeat(n, n)
    for s in range(0, len(t), chunk):
        sid = seg_id[s:s + chunk]; tt = t[s:s + chunk]
        pts = p0[sid] * (1 - tt[:, None]) + p1[sid] * tt[:, None]
        wt = intensity / density * np.ones(len(sid))
        splat(buf, pts[:, 0], pts[:, 1], rgb[sid] if per_rgb else rgb, wt)


def polyline(buf, pts, rgb, intensity=1.0, density=1.5, closed=False):
    pts = np.asarray(pts, np.float64)
    if closed:
        pts = np.vstack([pts, pts[:1]])
    segments(buf, pts[:-1], pts[1:], rgb, intensity, density)


def disc(buf, cx, cy, r, rgb, soft=1.2, core=1.0, halo=0.0, halo_r=3.0):
    """Anti-aliased filled disc plus optional exponential halo, added as light."""
    h, w = buf.shape[:2]
    R = r + (7 * r * halo_r * 0.35 if halo > 0 else 0) + 4 * soft + 2
    x0, x1 = int(max(0, cx - R)), int(min(w, cx + R + 1))
    y0, y1 = int(max(0, cy - R)), int(min(h, cy + R + 1))
    if x0 >= x1 or y0 >= y1:
        return
    yy, xx = np.mgrid[y0:y1, x0:x1].astype(np.float32)
    d = np.sqrt((xx - cx) ** 2 + (yy - cy) ** 2)
    a = np.clip((r - d) / soft + 0.5, 0, 1) * core
    if halo > 0:
        a = a + halo * np.exp(-np.maximum(d - r, 0) / (r * halo_r * 0.35 + 1e-6)) * (d > r * 0.6)
    buf[y0:y1, x0:x1] += a[..., None] * np.asarray(rgb, np.float32)[None, None]


def ring(buf, cx, cy, r, rgb, width=1.5, intensity=1.0):
    h, w = buf.shape[:2]
    R = r + 4 * width + 2
    x0, x1 = int(max(0, cx - R)), int(min(w, cx + R + 1))
    y0, y1 = int(max(0, cy - R)), int(min(h, cy + R + 1))
    yy, xx = np.mgrid[y0:y1, x0:x1].astype(np.float32)
    d = np.abs(np.sqrt((xx - cx) ** 2 + (yy - cy) ** 2) - r)
    a = np.clip((width / 2 - d) + 0.5, 0, 1) * intensity
    buf[y0:y1, x0:x1] += a[..., None] * np.asarray(rgb, np.float32)[None, None]


def blur(img, sigma):
    """Gaussian blur; large radii go through a downsampled pyramid."""
    if sigma < 6:
        return ndimage.gaussian_filter(img, (sigma, sigma, 0))
    f = int(2 ** np.floor(np.log2(sigma / 3)))
    h, w = img.shape[:2]
    hh, ww = h // f * f, w // f * f
    small = img[:hh, :ww].reshape(hh // f, f, ww // f, f, 3).mean((1, 3))
    small = ndimage.gaussian_filter(small, (sigma / f, sigma / f, 0))
    big = ndimage.zoom(small, (h / small.shape[0], w / small.shape[1], 1), order=1)
    return big[:h, :w]


def bloom(img, threshold=0.6, levels=((3, 0.35), (10, 0.25), (28, 0.18), (70, 0.12), (160, 0.08)),
          strength=1.0):
    strength = strength * GRADE['bloom']
    threshold = threshold * GRADE['bloom_threshold']
    lum = img.max(axis=2, keepdims=True)
    hi = img * np.clip((lum - threshold) / (lum + 1e-6), 0, None)
    out = img.copy()
    for s, wgt in levels:
        out += strength * wgt * blur(hi, s)
    return out


def aces(x):
    a, b, c, d, e = 2.51, 0.03, 2.43, 0.59, 0.14
    return np.clip((x * (a * x + b)) / (x * (c * x + d) + e), 0, 1)


def to_srgb(x):
    x = np.clip(x, 0, 1)
    return np.where(x <= 0.0031308, 12.92 * x, 1.055 * np.power(x, 1 / 2.4) - 0.055)


def finish(img, exposure=1.0, grain=0.010, vignette=0.28, seed=0, lift=0.0):
    h, w = img.shape[:2]
    y, x = np.mgrid[0:h, 0:w].astype(np.float32)
    r = np.sqrt(((x - w / 2) / (w / 2)) ** 2 * 0.8 + ((y - h / 2) / (h / 2)) ** 2 * 0.8)
    v = 1 - vignette * np.clip(r - 0.35, 0, None) ** 1.5
    lum = (img @ np.array([0.2126, 0.7152, 0.0722], np.float32))[..., None]
    img = lum + GRADE['sat'] * (img - lum)
    grain = grain * GRADE['grain']
    out = aces(np.clip(img, 0, None) * exposure * GRADE['exposure'] * v[..., None])
    out = to_srgb(out + lift)
    rng = np.random.default_rng(seed)
    g = rng.normal(size=(h, w, 1)).astype(np.float32) * grain
    out = np.clip(out + g, 0, 1)
    return (out * 255 + 0.5).astype(np.uint8)


def font(key, size):
    return ImageFont.truetype(FONT[key], size)


def label(draw, xy, text, key='sans', size=34, fill=(219, 230, 255), anchor='mm', alpha=255,
          spacing=0):
    f = font(key, size)
    if spacing:
        x, y = xy
        total = sum(draw.textlength(ch, font=f) for ch in text) + spacing * (len(text) - 1)
        if anchor[0] == 'm':
            x -= total / 2
        elif anchor[0] == 'r':
            x -= total
        for ch in text:
            draw.text((x, y), ch, font=f, fill=fill + (alpha,), anchor='l' + anchor[1])
            x += draw.textlength(ch, font=f) + spacing
        return
    draw.text(xy, text, font=f, fill=fill + (alpha,), anchor=anchor)


def overlay():
    """Return a transparent RGBA layer and its drawer for crisp labels."""
    lay = Image.new('RGBA', (W, H), (0, 0, 0, 0))
    return lay, ImageDraw.Draw(lay)


def save(img8, name, layer=None):
    OUT.mkdir(exist_ok=True)
    im = Image.fromarray(img8, 'RGB')
    if layer is not None:
        # soft dark halo under the labels so they read on busy ground
        from PIL import ImageFilter
        la = np.asarray(layer, np.float32)
        l = la[..., :3] @ np.array([0.2126, 0.7152, 0.0722], np.float32)
        la[..., :3] = l[..., None] + GRADE['label_sat'] * (la[..., :3] - l[..., None])
        layer = Image.fromarray(np.clip(la, 0, 255).astype(np.uint8), 'RGBA')
        r = max(3, int(round(img8.shape[1] / 400)))
        halo = np.asarray(layer.getchannel('A').filter(ImageFilter.MaxFilter(3))
                          .filter(ImageFilter.GaussianBlur(r)), np.float32) / 255
        base = np.asarray(im, np.float32) * (1 - 0.6 * np.clip(halo * 1.6, 0, 1))[..., None]
        im = Image.fromarray(base.astype(np.uint8), 'RGB')
        im = Image.alpha_composite(im.convert('RGBA'), layer).convert('RGB')
    im.save(OUT / f'{name}.png', optimize=True)
    web = OUT / 'web'; web.mkdir(exist_ok=True)
    im.save(web / f'{name}.jpg', quality=90, optimize=True, progressive=True)
    return OUT / f'{name}.png'


def load_render(name):
    """Linear premultiplied RGBA float render dumped by bl_common.render."""
    import json
    px = np.load(WORK / f'{name}.npy')
    anchors = None
    a = WORK / f'{name}_anchors.json'
    if a.exists():
        anchors = json.loads(a.read_text())
    return px, anchors


def composite(px, **backdrop_kw):
    h, w = px.shape[:2]
    bg = backdrop(w, h, **backdrop_kw)
    rgb = np.clip(px[..., :3], 0, None)
    a = np.clip(px[..., 3:4], 0, 1)
    return rgb + (1 - a) * bg


def overlay_like(img8):
    h, w = img8.shape[:2]
    lay = Image.new('RGBA', (w, h), (0, 0, 0, 0))
    return lay, ImageDraw.Draw(lay)


def mtext(draw, xy, parts, size, fill=(219, 230, 255), alpha=255, anchor='mm', key='math',
          measure=False):
    """Tiny math typesetter.  parts: list of (text, kind), kind in
    'n' (normal), 'sup', 'sub', 'bar' (overline), 'sqrt' (radical with vinculum)."""
    big = font(key, size); small = font(key, int(size * 0.64))
    col = fill + (alpha,)
    def width(t, k):
        f = small if k in ('sup', 'sub') else big
        w = draw.textlength(t, font=f)
        if k == 'sqrt':
            w += 0.56 * size
        return w
    total = sum(width(t, k) for t, k in parts)
    if measure:
        return total
    x, y = xy
    base = y + 0.33 * size
    if anchor[0] == 'm':
        x -= total / 2
    elif anchor[0] == 'r':
        x -= total
    lw = max(2, int(round(0.055 * size)))
    for t, k in parts:
        w = width(t, k)
        if k == 'sup':
            draw.text((x, base - 0.40 * size), t, font=small, fill=col, anchor='ls')
        elif k == 'sub':
            draw.text((x, base + 0.20 * size), t, font=small, fill=col, anchor='ls')
        elif k == 'sqrt':
            x0 = x + 0.52 * size
            draw.text((x0, base), t, font=big, fill=col, anchor='ls')
            top = base - 0.80 * size
            pts = [(x + 0.02 * size, base - 0.30 * size), (x + 0.13 * size, base - 0.37 * size),
                   (x + 0.27 * size, base + 0.03 * size), (x + 0.47 * size, top),
                   (x + w + 0.02 * size, top)]
            draw.line(pts, fill=col, width=lw, joint='curve')
        else:
            draw.text((x, base), t, font=big, fill=col, anchor='ls')
            if k == 'bar':
                bb = draw.textbbox((x, base), t, font=big, anchor='ls')
                yb = bb[1] - 0.10 * size
                draw.line([(bb[0] + 0.05 * size, yb), (bb[2] + 0.02 * size, yb)], fill=col, width=lw)
        x += w
    return total


# mathematical italic letters for labels
MI = dict(a='\U0001D44E', b='\U0001D44F', c='\U0001D450', d='\U0001D451', h='\u210E',
          i='\U0001D456', j='\U0001D457', k='\U0001D458', q='\U0001D45E', x='\U0001D465',
          G='\U0001D43A', E='\U0001D438', alpha='\U0001D6FC', rho='\U0001D70C', zeta='\U0001D701')
