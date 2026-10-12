"""Check final research artifacts, source hashes, and report links."""
import hashlib,json,re,resource
from pathlib import Path

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=128*1024**2
    names=['lattice_control','ope_control','fields_precise','closure_precise','trace_certificate',
           'exact_unitary_certificate','minimal_generators','grade3_span','grade3_modular',
           'grade3_exact_v2','grade3_action']
    records=[]
    for name in names:
        path=Path('hi_cft_20260923_c8_'+name+'.json');data=json.loads(path.read_text());count=0;archived=[]
        for filename,expected in data.get('source_sha256',{}).items():
            p=Path(filename);actual=hashlib.sha256(p.read_bytes()).hexdigest()
            if actual!=expected and p.name=='hi_cft_20260923_c8_exact_grade3.py':
                p=Path('hi_cft_20260923_c8_exact_grade3_v1.py');actual=hashlib.sha256(p.read_bytes()).hexdigest();archived.append(str(p))
            assert actual==expected,(path,p,actual,expected)
            count+=1
        records.append({'artifact':str(path),'verified_source_hashes':count,'historical_producer_archives':archived})
    report=Path('hi_cft_20260923_c8_construction_report.md');links=[]
    for target in re.findall(r'\]\(([^)]+)\)',report.read_text()):
        if target.startswith(('https://','http://','#')):continue
        p=report.parent/target.split('#')[0];assert p.exists(),p;links.append(str(p))
    out={'final_artifacts':records,'verified_local_report_links':links,
         'scope':'Integrity and linkage audit; mathematical scope is stated in each certificate.',
         'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()}
    path=Path('hi_cft_20260923_c8_artifact_audit.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'artifacts':len(records),'local_links':len(links),'all_passed':True}))

if __name__=='__main__':main()
