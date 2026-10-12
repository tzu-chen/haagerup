"""Verify the actual ZIP, then compile all three documents from its fresh extraction.

Use permanent guard with1536MiB AS, timeout120s. Expected<150MiB RSS,
one TeX child at a time; no numerical producer is rerun here.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import zipfile
from check_manuscript_refs import check as check_manuscript_refs

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def main():
    bundle=ROOT/'hi_cft_c8_physics_bundle.zip'
    directory=Path(tempfile.mkdtemp(prefix='c8-physics-bundle-verified-'))
    with zipfile.ZipFile(bundle) as archive:
        manifest=json.loads(archive.read('c8_physics_20260927/release_manifest.json'))
        assert archive.testzip() is None
        assert len(archive.namelist())==len(manifest['files'])+1
        for name in archive.namelist():
            path=Path(name)
            assert not path.is_absolute() and '..' not in path.parts
        for row in manifest['files']:
            value=archive.read(row['path'])
            assert len(value)==row['bytes'] and hashlib.sha256(value).hexdigest()==row['sha256']
        archive.extractall(directory)
    documents={}
    for name in ('hi_cft_c8_proof','hi_cft_c8_lean_assessment','hi_cft_c8_verification_guide'):
        # Compare with the reviewed PDF actually shipped, without freezing
        # page counts in this checker when a companion's layout changes.
        shipped_info=subprocess.check_output(['pdfinfo',str(directory/(name+'.pdf'))],text=True,timeout=15)
        expected=int(re.search(r'^Pages:\s+(\d+)',shipped_info,re.M)[1])
        for iteration in range(3):
            with (directory/f'{name}_verify{iteration}.txt').open('w') as stream:
                result=subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                                       '-halt-on-error',name+'.tex'],cwd=directory,
                                      stdout=stream,stderr=subprocess.STDOUT,timeout=30)
            assert result.returncode==0,('extracted TeX failed',name,iteration,str(directory))
        log=(directory/(name+'.log')).read_text()
        assert not re.search(r'undefined references|undefined on input|Overfull|Underfull|multiply defined|Missing character|destination with the same identifier|^!',log,re.M),name
        info=subprocess.check_output(['pdfinfo',str(directory/(name+'.pdf'))],text=True,timeout=15)
        pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
        assert pages==expected,(name,pages,expected)
        documents[name]={'passes':3,'pages':pages,'clean_compile':True}
    references=check_manuscript_refs(directory)
    assert references['status']=='PASS',references['errors']
    result={'status':'PASS','bundle':bundle.name,'bundle_sha256':hashlib.sha256(bundle.read_bytes()).hexdigest(),
            'verified_members':len(manifest['files'])+1,'fresh_extraction':str(directory),
            'documents':documents,'manuscript_references':references,
            'scope':'Actual ZIP integrity, every member hash, clean independent compilation of all three documents, and current manuscript link targets. Physics arithmetic replay is separately recorded in release_replay.json.'}
    (HERE/'bundle_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
