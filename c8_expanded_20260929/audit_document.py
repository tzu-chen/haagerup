#!/usr/bin/env python3
"""Audit typesetting dependencies, saved-input hashes and document scope.

This is an editorial integrity check, not a replay of any CFT computation.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
MAIN=HERE/'haagerup_c8_expanded.tex'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    visited={};missing=[]
    def visit(p):
        if p in visited:return
        if not p.is_file():missing.append(str(p));return
        text=p.read_text()
        visited[p]=text
        for rel in re.findall(r'\\input\{([^}]+)\}',text):visit(HERE/rel)
    visit(MAIN)
    text='\n'.join(re.sub(r'(?m)^\s*%.*$','',s) for s in visited.values())
    labels=Counter(re.findall(r'\\label\{([^}]+)\}',text))
    refs=set(re.findall(r'\\(?:ref|eqref|pageref|nameref|msref|mspageref|msnameref)\{([^}]+)\}',text))
    refs={x for x in refs if '#' not in x}
    cites={c for item in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',text) for c in item.split(',')}
    bib=set(re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',text))
    assets=set(re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}',text))
    missing.extend(str(HERE/a) for a in assets if not (HERE/a).is_file())
    controls={str(p.relative_to(HERE)):sorted({ord(c) for c in s if ord(c)<32 and c not in '\n\t'}) for p,s in visited.items()}
    controls={k:v for k,v in controls.items() if v}
    log=(HERE/'haagerup_c8_expanded.log').read_text(encoding='latin-1')
    warnings={
        'overfull_boxes':log.count('Overfull '),
        'underfull_boxes':log.count('Underfull '),
        'undefined_references_or_citations':len(re.findall(r'LaTeX Warning: (?:Reference|Citation).*undefined',log)),
        'multiply_defined_labels':len(re.findall('multiply defined',log)),
        'missing_glyphs':len(re.findall('Missing character:',log)),
        'rerun_required':bool(re.search(r'Rerun to get|Rerun LaTeX|Label\(s\) may have changed|Table widths have changed',log)),
    }
    recorded={}
    for path in ['assembly_inputs.json','top_transcription_inputs.json']:
        for source,entry in json.loads((HERE/path).read_text())['files'].items():recorded[source]=entry['sha256']
    recorded.update(json.loads((HERE/'physics_tables/transcription_manifest.json').read_text())['source_sha256'])
    changed=[s for s,h in recorded.items() if not (ROOT/s).is_file() or sha(ROOT/s)!=h]
    base={str(p.relative_to(HERE/'base')):sha(p) for p in (HERE/'base').rglob('*.tex')}
    changed_base=[s for s,h in base.items() if not (ROOT/s).is_file() or sha(ROOT/s)!=h]
    info=subprocess.check_output(['pdfinfo',str(HERE/'haagerup_c8_expanded.pdf')],text=True)
    pdf_mtime=(HERE/'haagerup_c8_expanded.pdf').stat().st_mtime_ns
    newer_sources=[str(p.relative_to(HERE)) for p in visited if p.stat().st_mtime_ns>pdf_mtime]
    pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
    pdftxt=subprocess.check_output(['pdftotext','-layout',str(HERE/'haagerup_c8_expanded.pdf'),'-'],text=True)
    (HERE/'haagerup_c8_expanded.txt').write_text(pdftxt)
    errorlist=[]
    for name,value in [('missing_dependencies',missing),('duplicate_labels',[k for k,v in labels.items() if v>1]),('unresolved_labels',sorted(refs-set(labels))),('unresolved_citations',sorted(cites-bib)),('control_characters',controls),('changed_recorded_inputs',changed),('changed_original_base_sources',changed_base),('TeX_sources_newer_than_PDF',newer_sources)]:
        if value:errorlist.append({name:value})
    for name,v in warnings.items():
        if v and name!='underfull_boxes':errorlist.append({name:v})
    report={
        'status':'PASS' if not errorlist else 'FAIL',
        'scope':'Document/reference/source integrity only. Existing numerical certificates were not replayed.',
        'pages':pages,'PDF_bytes':(HERE/'haagerup_c8_expanded.pdf').stat().st_size,
        'PDF_sha256':sha(HERE/'haagerup_c8_expanded.pdf'),
        'active_TeX_files':len(visited),'labels':len(labels),'references':len(refs),'bibliography_entries':len(bib),
        'included_figures':sorted(assets),'warnings':warnings,
        'recorded_original_input_hashes_checked':len(recorded),'original_base_TeX_files_unchanged':len(base),
        'physics_transcription_coverage':json.loads((HERE/'physics_tables/transcription_manifest.json').read_text())['coverage'],
        'spectral_scope':{'U_modules':12,'E8_vacuum_modules':1,'grades_each':25,'scalar_rows':121,'signed_spin_rows':2907,'thermal_observable_intervals':60},
        'coordinate_scope':{'small_stress_field_terms':337,'additional_weight_three_terms':434,'spectral_eigenvector_terms':126,'eighty_current_cyclic_recipes':80,'mixed_top_cyclic_recipes':324},
        'errors':errorlist,
        'typesetting_files':{str(p.relative_to(HERE)):sha(p) for p in sorted(visited)},
        'original_source_hashes':recorded,
    }
    (HERE/'document_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['typesetting_files','original_source_hashes']},indent=2))
    if errorlist:raise SystemExit(1)

if __name__=='__main__':main()
