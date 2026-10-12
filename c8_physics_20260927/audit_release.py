"""Bounded document, dependency and arithmetic-record audit; no producer rerun.

Run under512MiB resource guard. Hash in64KiB chunks; JSON files<10MiB.
This verifies current hashes and declared checks, not the CFT theorem.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
from check_manuscript_refs import check as check_manuscript_refs

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(65536),b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    assert path.stat().st_size < 10*1024**2
    return json.loads(path.read_text())


def check_hashes(values, base):
    for name,expected in values.items():
        path=Path(name)
        if not path.is_absolute():
            path=base/path
        assert path.is_file() and sha(path)==expected, ('hash mismatch',str(path))
    return len(values)


def main():
    checks={}
    spectrum=read(HERE/'data/run_summary.json')
    assert spectrum['status']=='PASS' and all(spectrum['checks'].values())
    checks['spectrum_source_hashes']=check_hashes(spectrum['source_sha256'],ROOT)
    checks['spectrum_output_hashes']=check_hashes(spectrum['output_sha256'],HERE/'data')
    for directory in (HERE,HERE/'full_weight_two'):
        record=read(directory/'low_weight_couplings.json')
        assert record['status']=='pass'
        check_hashes(record['source_sha256'],ROOT)
        assert sha(directory/'low_weight_basis.json')==record['basis_sha256']
        assert sha(directory/'low_weight_products.jsonl')==record['products_sha256']
        complete=read(directory/'complete_primary_couplings.json')
        assert complete['status']=='PASS'
        check_hashes(complete['source_sha256'],ROOT)
        assert sha(directory/'complete_primary_couplings.tsv')==complete['output_sha256']
    checks['seed_and_completed_coupling_hashes']=True
    corr=read(HERE/'correlators.json')
    checks['correlator_source_hashes']=check_hashes(corr['source_sha256'],ROOT)
    defect=read(HERE/'defect_data.json')
    assert all(defect['checks'].values()) and sha(HERE/'defects.py')==defect['generator_sha256']
    checks['defect_generator_hash_and_checks']=True
    cross=read(HERE/'crosslink_checks.json')
    assert cross['status']=='PASS'
    checks['crosslink_source_hashes']=check_hashes(cross['source_sha256'],HERE)
    thermal_input=read(HERE/'thermal_input_check.json')
    assert thermal_input['status']=='PASS'
    checks['thermal_constant_source_hashes']=check_hashes(thermal_input['source_sha256'],HERE)
    replay=read(HERE/'release_replay.json')
    assert replay['status']=='PASS'
    checks['fresh_tree_replay']=replay
    for document in ('hi_cft_c8_proof','hi_cft_c8_lean_assessment','hi_cft_c8_verification_guide'):
        log=(ROOT/(document+'.log')).read_text()
        forbidden=[r'Undefined control sequence',r'undefined references',r'undefined on input',
                   r'multiply defined',r'Overfull',r'Underfull',r'destination with the same identifier',
                   r'Missing character',r'^!']
        for pattern in forbidden:
            assert not re.search(pattern,log,re.M), (document,pattern)
        pdf=ROOT/(document+'.pdf')
        result=subprocess.run(['pdfinfo',str(pdf)],capture_output=True,text=True,check=True,timeout=15)
        pages=int(re.search(r'^Pages:\s+(\d+)',result.stdout,re.M)[1])
        checks[document]={'pages':pages,'sha256':sha(pdf),'bytes':pdf.stat().st_size,'clean_TeX_checks':True}
    visited=set()
    pending=[ROOT/'hi_cft_c8_proof.tex',ROOT/'hi_cft_c8_lean_assessment.tex',
             ROOT/'hi_cft_c8_verification_guide.tex']
    assets=set()
    while pending:
        path=pending.pop()
        if path in visited:
            continue
        visited.add(path)
        for kind,name in re.findall(r'\\(input|includegraphics)(?:\[[^\]]*\])?\{([^}]+)\}',path.read_text()):
            target=ROOT/name
            assert target.is_file(),('missing TeX dependency',str(target))
            assets.add(str(target.relative_to(ROOT)))
            if kind=='input':
                pending.append(target)
    checks['TeX_dependency_files']=sorted(assets)
    checks['current_manuscript_references']=check_manuscript_refs(ROOT)
    assert checks['current_manuscript_references']['status']=='PASS', checks['current_manuscript_references']['errors']
    leanlog=(HERE/'physics_lean.log').read_text()
    assert 'exit 0' in leanlog and leanlog.count('depends on axioms:')==2
    assert not re.search(r'\berror:',leanlog)
    checks['two_Lean_thermal_lemmas']={'passed':True,'source_sha256':sha(ROOT/'lean/HaagerupIzumi/CFT/PhysicsBounds.lean'),
                                     'scope':'Algebraic implications with explicit analytic premises.'}
    result={'status':'PASS','checks':checks,'scope':'Document/dependency/source audit and successful saved arithmetic replay; not a formal proof of the full manuscript.'}
    (HERE/'release_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','manuscript_pages':checks['hi_cft_c8_proof']['pages'],
                      'assessment_pages':checks['hi_cft_c8_lean_assessment']['pages'],
                      'verification_guide_pages':checks['hi_cft_c8_verification_guide']['pages'],
                      'dependency_files':len(assets),'replay_files':replay['byte_identical_payload_files']}))


if __name__=='__main__':
    main()
