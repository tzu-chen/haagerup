"""Build gallery/index.html (the published page) and STORIES.md from stories.py."""
import html
import re
import shutil
from pathlib import Path

import stories as S

ROOT = Path(__file__).resolve().parents[1]
GAL = ROOT / 'gallery'
IMG = GAL / 'img'

ACC = {'teal': 'var(--teal)', 'gold': 'var(--gold)', 'coral': 'var(--coral)', 'violet': 'var(--violet)'}

CSS = r"""
:root{
  --paper:#f5f6fa; --paper-2:#eceff7; --ink:#10152e; --muted:#586080; --rule:#d9deea;
  --gold:#94672a; --teal:#2f7a70; --coral:#a84a60; --violet:#5f55a8;
  --plate:#0b0f1c; --note:#e9ecf6;
  --display:"Schibsted Grotesk","Helvetica Neue",Arial,sans-serif;
  --serif:"Source Serif 4","Source Serif Pro",Georgia,"Times New Roman",serif;
  --mono:"IBM Plex Mono",ui-monospace,SFMono-Regular,Menlo,monospace;
}
@media (prefers-color-scheme: dark){
  :root:not([data-theme="light"]){
    color-scheme:dark;
    --paper:#0b0f1c; --paper-2:#121829; --ink:#e6e8ef; --muted:#9ea4b8; --rule:#20283d;
    --gold:#d9b27a; --teal:#7cc3b8; --coral:#df8ea0; --violet:#a9a2dc; --note:#121829;
  }
}
:root[data-theme="dark"]{
  color-scheme:dark;
  --paper:#0b0f1c; --paper-2:#121829; --ink:#e6e8ef; --muted:#9ea4b8; --rule:#20283d;
  --gold:#d9b27a; --teal:#7cc3b8; --coral:#df8ea0; --violet:#a9a2dc; --note:#121829;
}
*{box-sizing:border-box}
body{background:var(--paper);color:var(--ink);font-family:var(--serif);font-size:18px;
  line-height:1.62;margin:0;padding-inline:clamp(16px,4vw,48px);padding-block:0 64px;
  -webkit-font-smoothing:antialiased;text-rendering:optimizeLegibility}
.wrap{max-width:1240px;margin-inline:auto}
.masthead{padding-block:clamp(40px,7vw,88px) 28px;display:grid;gap:18px}
.kicker{font-family:var(--display);font-weight:700;font-size:13px;letter-spacing:.14em;
  text-transform:uppercase;color:var(--teal);margin:0}
h1{font-family:var(--display);font-weight:800;font-size:clamp(40px,7.2vw,88px);line-height:.98;
  letter-spacing:-.02em;margin:0;text-wrap:balance}
h1 .thirteen{color:var(--coral)}
.lede{font-size:clamp(19px,2.1vw,23px);line-height:1.5;max-width:40em;margin:0;color:var(--ink)}
.status{font-family:var(--display);font-size:14px;line-height:1.55;color:var(--muted);max-width:52em;margin:0;
  border-left:2px solid var(--rule);padding-left:14px}
nav.contents{margin-block:26px 8px;border-top:1px solid var(--rule);padding-top:22px}
nav.contents ol{list-style:none;margin:0;padding:0;display:grid;gap:14px;
  grid-template-columns:repeat(7,minmax(0,1fr))}
nav.contents a{display:grid;gap:8px;text-decoration:none;color:var(--ink);border-radius:4px}
nav.contents a:focus-visible{outline:2px solid var(--teal);outline-offset:4px}
nav.contents img{display:block;width:100%;aspect-ratio:16/9;object-fit:cover;border-radius:3px;
  background:var(--plate);transition:transform .25s ease}
nav.contents a:hover img{transform:translateY(-2px)}
nav.contents .n{font-family:var(--display);font-weight:700;font-size:12px;letter-spacing:.12em;
  text-transform:uppercase;color:var(--muted)}
nav.contents .t{font-family:var(--display);font-weight:600;font-size:15px;line-height:1.25}
@media (max-width:900px){
  nav.contents ol{grid-template-columns:1fr}
  nav.contents a{grid-template-columns:112px 1fr;align-items:center;gap:14px}
  nav.contents .n{grid-column:2;grid-row:1;align-self:end}
  nav.contents .t{grid-column:2;grid-row:2;align-self:start}
  nav.contents img{grid-row:1 / span 2}
}
section.view{padding-block:clamp(48px,8vw,96px) 0;scroll-margin-top:16px}
section.view + section.view{border-top:1px solid var(--rule);margin-top:clamp(40px,6vw,72px)}
figure{margin:0}
figure img{display:block;width:100%;max-width:100%;height:auto;aspect-ratio:16/9;border-radius:4px;
  background:var(--plate)}
figcaption{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:18px;margin-top:14px;
  font-family:var(--display);font-size:13.5px;line-height:1.5;color:var(--muted)}
figcaption p{margin:0;border-top:1px solid var(--rule);padding-top:8px}
@media (max-width:760px){figcaption{grid-template-columns:1fr;gap:6px}}
.story{max-width:680px;margin-inline:auto;margin-top:clamp(28px,4vw,44px)}
.eyebrow{font-family:var(--display);font-weight:700;font-size:13px;letter-spacing:.14em;
  text-transform:uppercase;margin:0 0 12px;color:var(--acc)}
.eyebrow .num{font-variant-numeric:tabular-nums;margin-right:10px}
h2{font-family:var(--display);font-weight:800;font-size:clamp(30px,4.2vw,46px);line-height:1.05;
  letter-spacing:-.015em;margin:0 0 16px;text-wrap:balance}
.dek{font-style:italic;font-size:clamp(19px,2vw,22px);line-height:1.48;color:var(--muted);margin:0 0 26px}
.story p.body{margin:0 0 1.1em;hyphens:auto}
.work{margin-top:26px;background:var(--note);border-radius:4px;padding:14px 18px;
  font-family:var(--display);font-size:14.5px;line-height:1.55}
.work b{font-weight:700;letter-spacing:.1em;text-transform:uppercase;font-size:12px;color:var(--acc);
  margin-right:8px}
.mono{font-family:var(--mono);font-size:.92em}
.ov{text-decoration:overline;text-decoration-thickness:1px}
sub,sup{line-height:0;font-size:.72em}
i{font-style:italic}
footer{max-width:680px;margin-inline:auto;margin-top:clamp(64px,9vw,110px);border-top:1px solid var(--rule);
  padding-top:22px;font-family:var(--display);font-size:14px;line-height:1.6;color:var(--muted)}
footer h3{font-family:var(--display);font-size:13px;letter-spacing:.14em;text-transform:uppercase;
  color:var(--ink);margin:0 0 8px}
footer p{margin:0 0 10px}
@media (prefers-reduced-motion:reduce){nav.contents img{transition:none}}
"""


def page():
    out = []
    add = out.append
    add('<title>Seven Views of Haagerup</title>')
    add('<link rel="preconnect" href="https://fonts.googleapis.com">')
    add('<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>')
    add('<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono&'
        'family=Schibsted+Grotesk:wght@500;600;700;800&'
        'family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;1,8..60,400&display=swap">')
    add(f'<style>{CSS}</style>')
    add('<div class="wrap">')
    I = S.INTRO
    add('<header class="masthead">')
    add(f'<p class="kicker">{I["kicker"]}</p>')
    add('<h1>Seven Views of Haagerup</h1>')
    add(f'<p class="lede">{I["dek"]}</p>')
    add(f'<p class="status">{I["status"]}</p>')
    add('<nav class="contents" aria-label="The seven views"><ol>')
    for k, v in enumerate(S.VIEWS, 1):
        add(f'<li><a href="#{v["slug"]}"><img src="img/{v["img"]}.jpg" alt="" loading="lazy">'
            f'<span class="n">{k} · {v["kicker"]}</span><span class="t">{v["title"]}</span></a></li>')
    add('</ol></nav></header><main>')
    for k, v in enumerate(S.VIEWS, 1):
        acc = ACC[v['accent']]
        add(f'<section class="view" id="{v["slug"]}" style="--acc:{acc}">')
        eager = 'eager' if k == 1 else 'lazy'
        add(f'<figure><img src="img/{v["img"]}.jpg" width="2400" height="1350" loading="{eager}" '
            f'alt="{html.escape(v["alt"])}">')
        add('<figcaption>' + ''.join(f'<p>{s}</p>' for s in v['see']) + '</figcaption></figure>')
        add('<div class="story">')
        add(f'<p class="eyebrow"><span class="num">{k:02d}</span>{v["kicker"]}</p>')
        add(f'<h2>{v["title"]}</h2>')
        add(f'<p class="dek">{v["dek"]}</p>')
        for p in v['body']:
            add(f'<p class="body">{p}</p>')
        add(f'<div class="work"><b>In the work</b>{v["work"]}</div>')
        add('</div></section>')
    add('</main><footer>')
    add('<h3>How these were made</h3>')
    add('<p>Views 1, 4, 6 and 7 are Blender Cycles renders. Views 2, 3 and 5 are drawn as additive '
        'light in NumPy. All seven share one finishing pass: bloom, ACES tone mapping and film grain. '
        'Every mark is placed from exact data: the manuscript\'s Gram matrix and defining field, its '
        'modular data, the exported character and spectrum tables, and the exact four-point '
        'function.</p>')
    add('<p>Scripts and full-resolution images live in <span class="mono">c8_renders_20260927/</span> '
        'next to the manuscript <span class="mono">hi_cft_c8_proof.tex</span>. Each ran under the '
        'repository\'s bounded launcher, one job at a time on two threads.</p>')
    add('</footer></div>')
    return '\n'.join(out)


SUB = str.maketrans('0123456789+−=()', '₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎')
SUP = str.maketrans('0123456789+−=()', '⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾')


def md(s):
    s = re.sub(r'<span class="ov">(.*?)</span>', lambda m: m.group(1) + '̅', s)
    s = re.sub(r'<span class="mono">(.*?)</span>', r'`\1`', s)
    for _ in range(3):
        s = re.sub(r'<sub>([^<>]*)</sub>',
                   lambda m: m.group(1).translate(SUB) if set(m.group(1)) <= set('0123456789+−=()')
                   else '_' + m.group(1), s)
        s = re.sub(r'<sup>([^<>]*)</sup>',
                   lambda m: m.group(1).translate(SUP) if set(m.group(1)) <= set('0123456789+−=()')
                   else '^(' + m.group(1) + ')', s)
        s = re.sub(r'<i>([^<>]*)</i>', r'*\1*', s)
    s = re.sub(r'<[^>]+>', '', s)
    return html.unescape(s)


def stories_md():
    I = S.INTRO
    L = [f'# {md(I["title"])}', '', f'*{md(I["kicker"])}*', '', md(I['dek']), '', f'> {md(I["status"])}', '']
    for k, v in enumerate(S.VIEWS, 1):
        L += [f'## {k}. {md(v["title"])}', '', f'![{md(v["alt"])}](out/{v["img"]}.png)', '',
              f'*{md(v["dek"])}*', '']
        L += [md(p) + '\n' for p in v['body']]
        L += ['**What you see.**', ''] + [f'- {md(s)}' for s in v['see']] + ['']
        L += [f'**In the work.** {md(v["work"])}', '']
    return '\n'.join(L)


if __name__ == '__main__':
    IMG.mkdir(parents=True, exist_ok=True)
    for v in S.VIEWS:
        shutil.copy(ROOT / 'out' / 'web' / f'{v["img"]}.jpg', IMG / f'{v["img"]}.jpg')
    (GAL / 'index.html').write_text(page())
    (ROOT / 'STORIES.md').write_text(stories_md())
    print('wrote', GAL / 'index.html', ROOT / 'STORIES.md')
