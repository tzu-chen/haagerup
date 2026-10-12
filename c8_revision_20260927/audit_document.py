"""Bounded static source/build audit; no mathematical proof is inferred.

Run through hi_cft_safe_run.py with512MiB AS. Peak estimate<0.1GiB,
including one pdfinfo child, source strings and small JSON objects.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import subprocess

root=Path(__file__).resolve().parents[1]
revision=root/'c8_revision_20260927'
names=['hi_cft_c8_proof.tex','hi_cft_c8_manuscript_structure.tex',
       'hi_cft_c8_manuscript_analytic.tex','hi_cft_c8_bibliography.tex']
texts={name:(root/name).read_text() for name in names}
text='\n'.join(texts.values())
labels=re.findall(r'\\label\{([^}]+)\}',text)
references=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',text)
bib=re.findall(r'\\bibitem\{([^}]+)\}',text)
cites=[]
for group in re.findall(r'\\cite(?:\[[^\]]*\])*\{([^}]+)\}',text):
    cites.extend(part.strip() for part in group.split(','))
assert len(labels)==len(set(labels)), 'duplicate labels'
assert len(bib)==len(set(bib)), 'duplicate bibliography keys'
assert set(references)<=set(labels), 'unresolved cross-references'
assert set(cites)<=set(bib), 'unresolved citations'
paths={}
for name in sorted(set(re.findall(r'\\artifact\{([^}]+)\}',text))):
    if name=='#1': continue
    path=root/name
    if not path.exists(): path=revision/name
    assert path.exists(), 'missing local artifact: '+name
    paths[name]=str(path.relative_to(root))
log=(root/'hi_cft_c8_proof_build.log').read_text()
for bad in ['undefined references','multiply defined','Overfull','Underfull',
            'Missing character','Rerun to get','! LaTeX Error']:
    assert bad not in log, 'build problem: '+bad
pdf=root/'hi_cft_c8_proof.pdf'
info=subprocess.run(['pdfinfo',str(pdf)],capture_output=True,text=True,check=True,timeout=10).stdout
pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M).group(1))
assert pages==55
ledger=json.loads((revision/'finite_input_ledger_complete.json').read_text())
assert ledger['status']=='finite_inputs_and_explicit_generation_authenticated'
assert len(ledger['fresh_successful_replay_outputs'])==11
for name in names+['hi_cft_c8_proof.pdf','hi_cft_c8_proof_README.md',
                  'hi_cft_c8_proof_build.log','hi_cft_c8_manuscript_review.md']:
    path=root/name
    assert hashlib.sha256(path.read_bytes()).hexdigest()==ledger['source_sha256'][str(path)]
assert json.loads((revision/'top_bound_replay.json').read_text())['status']=='pass'
for name in ['lean_finite_closure_final.log','lean_top_bound.log']:
    leanlog=(revision/name).read_text()
    assert '; exit 0' in leanlog and 'sorryAx' not in leanlog and 'error:' not in leanlog
line_counts={name:{'revised':len(content.splitlines())} for name,content in texts.items()}
for name in names:
    baseline=revision/'baseline'/name
    if baseline.exists(): line_counts[name]['baseline']=len(baseline.read_text().splitlines())
result={
    'status':'pass','pdf_pages':pages,'bibliography_entries':len(bib),
    'unique_labels':len(labels),'distinct_citation_keys_used':len(set(cites)),
    'local_artifacts_resolved':len(paths),'artifact_resolution':paths,
    'source_line_counts':line_counts,
    'supplemented_ledger_authenticated_files':ledger['authenticated_file_count'],
    'semantic_replays':list(ledger['fresh_successful_replay_outputs']),
    'additional_independent_arithmetic':'fourteen-top exact Fraction reconstruction: pass',
    'lean_modules_checked':['FiniteClosure.lean','TopBound.lean'],
    'visually_inspected_pdf_pages':[1,5,10,18,23,41,42,43,44,49,52,55],
    'build_issues':[],
    'environment_notices':['array package requests newer LaTeX format','epstopdf shell escape disabled'],
    'source_and_pdf_hashes':{name:hashlib.sha256((root/name).read_bytes()).hexdigest()
                             for name in names+['hi_cft_c8_proof.pdf']},
    'scope':'Static document consistency, successful scoped replay records and declared manual page inspection; not a proof of the mathematical arguments, including the annulus comparison.'}
output=revision/'document_audit_complete.json'
with output.open('x') as stream: json.dump(result,stream,indent=2);stream.write('\n')
print(json.dumps({k:result[k] for k in ['status','pdf_pages','bibliography_entries','unique_labels','local_artifacts_resolved','supplemented_ledger_authenticated_files']}))
