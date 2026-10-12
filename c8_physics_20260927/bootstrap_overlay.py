#!/usr/bin/env python3
"""Original vector AHKZ panels with exact (8,2) comparison points.

Uses only Python stdlib, pdftotext, and pdflatex. Run under hi_cft_safe_run.py.
Estimated <150MiB; reviewed AS1GiB. Child tools inherit the resource guard.
No rasterization, curve digitization, curve fitting, or extra installation.
The original article is CC-BY4.0; the output includes full attribution.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET

PANELS = [
    {'figure': 2, 'page_number': 4, 'crop': [333, 190, 543, 333],
     'title': '(a) Haagerup-invariant scalar gap', 'target_x': 20},
    {'figure': 3, 'page_number': 5, 'crop': [70, 45, 282, 190],
     'title': '(b) Charged tube-sector scalar gap', 'target_x': 390},
]

def center(word):
    return ((word[0]+word[2])/2, (word[1]+word[3])/2)

def contains(rect, box):
    return rect[0] <= box[0] <= box[2] <= rect[2] and rect[1] <= box[1] <= box[3] <= rect[3]

def ticks(all_words, crop):
    words = [w for w in all_words if contains(crop, w[:4])]
    x_ticks = {}
    for number in (0, 2, 4, 6, 8):
        found = [w for w in words if w[4] == str(number) and center(w)[1] > crop[3]-25]
        if len(found) != 1:
            raise ValueError(('x tick not uniquely identified', number, found, words))
        x_ticks[number] = found[0]
    x0 = center(x_ticks[0])[0]
    sx = (center(x_ticks[8])[0]-x0)/8
    if not 15 < sx < 30:
        raise ValueError(('unexpected central-charge axis scale', sx))
    x_residuals = {str(t): center(w)[0]-(x0+t*sx) for t,w in x_ticks.items()}
    if max(abs(x) for x in x_residuals.values()) > .7:
        raise ValueError(('x tick calibration inconsistent', x_residuals))
    y_ticks = {}
    for number in (0, .5, 1, 1.5, 2, 2.5):
        target = f'{number:.1f}'
        found = [w for w in words if w[4] == target and w[2] < x0-.2]
        if len(found) != 1:
            raise ValueError(('y tick not uniquely identified', target, found, words))
        y_ticks[number] = found[0]
    y0 = center(y_ticks[0])[1]
    sy = (center(y_ticks[2])[1]-y0)/2
    if not -60 < sy < -25:
        raise ValueError(('unexpected dimension axis scale', sy))
    y_residuals = {str(t): center(w)[1]-(y0+t*sy) for t,w in y_ticks.items()}
    if max(abs(y) for y in y_residuals.values()) > .7:
        raise ValueError(('y tick calibration inconsistent', y_residuals))
    point = (x0+8*sx, y0+2*sy)
    if not contains(crop, [point[0],point[1],point[0],point[1]]):
        raise ValueError('point fell outside source crop')
    return {'x_tick_words': {str(t): w[:5] for t,w in x_ticks.items()},
            'y_tick_words': {str(t): w[:5] for t,w in y_ticks.items()},
            'x_residual_points': x_residuals, 'y_residual_points': y_residuals,
            'source_point_coordinates': point, 'source_axis_origin': [x0,y0],
            'source_axis_scale_per_unit': [sx,sy]}

def source_geometry(source):
    run = subprocess.run(['pdftotext', '-f', '4', '-l', '5', '-bbox', str(source), '-'],
                         capture_output=True, text=True, check=True, timeout=20)
    if len(run.stdout) > 5*1024*1024:
        raise ValueError('unexpectedly large two-page geometry')
    # Some PDF font maps emit XML-forbidden control characters in body
    # text, although the axis labels are ordinary ASCII. Remove only XML
    # 1.0-invalid characters/references and record every such removal.
    def xml_allowed(code):
        return code in (9,10,13) or 0x20 <= code <= 0xD7FF or 0xE000 <= code <= 0xFFFD or 0x10000 <= code <= 0x10FFFF
    removed = {}
    safe = []
    for char in run.stdout:
        if xml_allowed(ord(char)):
            safe.append(char)
        else:
            key = f'U+{ord(char):04X}'
            removed[key] = removed.get(key,0)+1
    invalid_references = {}
    def clean_reference(match):
        token = match.group(1)
        code = int(token[1:],16) if token.lower().startswith('x') else int(token)
        if xml_allowed(code):
            return match.group(0)
        invalid_references[token] = invalid_references.get(token,0)+1
        return ''
    xml = re.sub(r'&#(x[0-9A-Fa-f]+|[0-9]+);', clean_reference, ''.join(safe))
    root = ET.fromstring(xml)
    pages = [e for e in root.iter() if e.tag.rsplit('}',1)[-1] == 'page']
    if len(pages) != 2:
        raise ValueError('expected geometry for exactly pages4 and5')
    result = {'_xml_sanitization': {'removed_invalid_codepoints': removed,
                                  'removed_invalid_numeric_references': invalid_references,
                                  'retained_controls': ['TAB','LF','CR']}}
    for page_number, page in zip((4,5), pages):
        width, height = float(page.attrib['width']), float(page.attrib['height'])
        if abs(width-612) > 1 or abs(height-792) > 1:
            raise ValueError(('unexpected source page dimensions', width,height))
        words = []
        for e in page.iter():
            if e.tag.rsplit('}',1)[-1] == 'word':
                words.append([float(e.attrib[a]) for a in ('xMin','yMin','xMax','yMax')] + [''.join(e.itertext())])
        result[page_number] = {'width':width,'height':height,'words':words}
    return result

def put_text(x, y_from_top, text, size=9, color='black'):
    return ('\\put(%.6f,%.6f){\\makebox(0,0)[l]{\\sffamily'
            '\\fontsize{%s}{%s}\\selectfont\\color{%s}%s}}' %
            (x,309-y_from_top,size,size+2,color,text))

def main(source_path, output_dir, build=True):
    source_path = source_path.resolve()
    output_dir = output_dir.resolve()
    if source_path.stat().st_size > 10*1024*1024:
        raise ValueError('unexpectedly large source PDF')
    source = source_geometry(source_path)
    output_dir.mkdir(parents=True, exist_ok=True)
    metadata = {'source_url':'https://arxiv.org/pdf/2512.08225v2',
                'source_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
                'published_doi':'10.1103/6tzz-tvp7',
                'license_url':'https://creativecommons.org/licenses/by/4.0/',
                'license_verified_at':'https://journals.aps.org/prl/abstract/10.1103/6tzz-tvp7',
                'modifications':'Clipped original vector panels; added red exact-model points and labels.',
                'model_point':{'c_left':8,'c_right':8,'Delta_scalar':2},
                'comparison':'Visually below both published curves; no curve value extracted.',
                'geometry_tool':'pdftotext -bbox; all coordinates in PDF big points (bp)',
                'source_text_sanitization':source['_xml_sanitization'],
                'panels':[]}
    lines = [r'\documentclass{article}',
             r'\usepackage[paperwidth=740bp,paperheight=309bp,margin=0bp]{geometry}',
             r'\usepackage{graphicx,xcolor}',r'\pagestyle{empty}',
             r'\definecolor{modelred}{rgb}{0.78,0.10,0.10}',
             r'\setlength{\parindent}{0pt}\setlength{\parskip}{0pt}\setlength{\topskip}{0pt}',
             r'\setlength{\unitlength}{1bp}',r'\begin{document}',
             r'\noindent\begin{picture}(740,309)']
    for panel in PANELS:
        page = source[panel['page_number']]
        crop = panel['crop']
        calibration = ticks(page['words'],crop)
        factor = 320/(crop[2]-crop[0])
        target = [panel['target_x'],28,panel['target_x']+320,28+factor*(crop[3]-crop[1])]
        trim = [crop[0],page['height']-crop[3],page['width']-crop[2],crop[1]]
        command = ('\\put(%.6f,%.6f){\\includegraphics[page=%d,width=320bp,'
                   'trim={%.6fbp %.6fbp %.6fbp %.6fbp},clip]{\\detokenize{%s}}}' %
                   (target[0],309-target[3],panel['page_number'],*trim,source_path.as_posix()))
        lines.append(command)
        xx,yy = calibration['source_point_coordinates']
        point = [target[0]+(xx-crop[0])*factor,target[1]+(yy-crop[1])*factor]
        lines.append('\\put(%.6f,%.6f){\\color{white}\\circle*{7}}' % (point[0],309-point[1]))
        lines.append('\\put(%.6f,%.6f){\\color{modelred}\\circle*{5.8}}' % (point[0],309-point[1]))
        lines.append(put_text(point[0]-36,point[1]+15,'$(8,2)$',10,'modelred'))
        lines.append(put_text(panel['target_x']+4,15,panel['title'],11))
        calibration.update(panel)
        calibration['target_rectangle'] = target
        calibration['target_point_coordinates'] = point
        calibration['graphicx_trim_bp'] = trim
        metadata['panels'].append(calibration)
    lines += [put_text(20,263,r'Red circles: the selected left Haagerup symmetry of the full $E_8$ theory; $c_L=c_R=8$.'),
              put_text(20,278,r"Original panels: J.~Albert, Y.~Honda, J.~Kaidi, Y.~Zheng, `Haagerup Symmetry in $(E_8)_1$?',",8),
              put_text(20,290,r'Phys.~Rev.~Lett.~136, 091603 (2026), DOI: 10.1103/6tzz-tvp7. CC BY 4.0. Red points and labels added.',8),
              r'\end{picture}',r'\end{document}']
    stem = 'haagerup_bootstrap_comparison'
    tex = output_dir/f'{stem}.tex'
    tex.write_text('\n'.join(lines)+'\n')
    (output_dir/f'{stem}_metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    if build:
        run = subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                              '-output-directory',str(output_dir),str(tex)],
                             capture_output=True,text=True,timeout=45)
        (output_dir/f'{stem}_build.log').write_text(run.stdout+run.stderr)
        if run.returncode:
            raise RuntimeError(f'pdflatex failed: see {stem}_build.log')
        destination = output_dir/f'{stem}.pdf'
        if not destination.is_file() or destination.stat().st_size < 1000:
            raise RuntimeError('overlay PDF missing or empty')
        info = subprocess.run(['pdfinfo',str(destination)],capture_output=True,text=True,check=True,timeout=10)
        if not any(line.split()==['Pages:','1'] for line in info.stdout.splitlines()):
            raise RuntimeError(('expected a single-page overlay',info.stdout))
    print(json.dumps({'status':'PASS' if build else 'PREPARED','output':str(output_dir/(stem+('.pdf' if build else '.tex'))),
                      'model_points':[[8,2],[8,2]],'curve_values_extracted':False}),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    directory=Path(__file__).resolve().parent
    parser.add_argument('--source',type=Path,default=directory/'ahkz_2512.08225v2.pdf')
    parser.add_argument('--output-dir',type=Path,default=directory/'figures')
    parser.add_argument('--no-build',action='store_true')
    args=parser.parse_args()
    main(args.source,args.output_dir,not args.no_build)
