"""Integrity and dependency audit for the two-hour proof attempt."""
import hashlib,json,re,resource
from pathlib import Path


def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=256*1024**2
    prefix='hi_cft_20260923_proof_'
    names=['current_module_v2','potts','potts_exact','rational_core','ambient_coset',
           'pf13_exact','pf13_membership','pf13_ope','pf13_nonlinear','pf13_truncation',
           'pf13_dly','pf13_simple_pole_algebra','pf13_upper_poles','remaining_coset','remaining_axes','grade4_tol5']
    records=[]
    for name in names:
        p=Path(prefix+name+'.json');data=json.loads(p.read_text());count=0
        for key in ('source_sha256','sha256'):
            for filename,expected in data.get(key,{}).items():
                source=Path(filename);actual=hashlib.sha256(source.read_bytes()).hexdigest()
                assert actual==expected,(str(p),filename,actual,expected)
                count+=1
        records.append({'artifact':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                        'verified_embedded_hashes':count})
    for filename,key in [('pf13_nonlinear','exact_Linshaw_5_7_simple_pole'),
                         ('pf13_truncation','exact_W6_truncation'),
                         ('pf13_dly','matches_DLY_Appendix_B_exactly'),
                         ('pf13_simple_pole_algebra','exact_A2_simple_pole_from_Jacobi_and_skew'),
                         ('pf13_upper_poles','all_checked_upper_poles_match'),
                         ('remaining_coset','PF13_stress_PCT_and_ambient_quasiprimary_exact'),
                         ('remaining_coset','PF13_translation_on_generator_exact')]:
        data=json.loads(Path(prefix+filename+'.json').read_text());assert data[key] is True
    docs=[Path(prefix+'report.md'),Path(prefix+'pf13_identification.md')];links=[]
    for doc in docs:
        for target in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
            if target.startswith(('https://','http://','#')):continue
            p=doc.parent/target.split('#')[0];assert p.exists(),p;links.append(str(p))
    manifest={str(p):hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(Path('.').glob(prefix+'*'))
              if p.is_file() and p.suffix in ('.py','.md','.json') and 'artifact_audit.json' not in p.name}
    out={'all_integrity_checks_passed':True,'finite_OPE_identification_gates_passed':True,
         'full_Haagerup_identification_proved':False,
         'mathematical_derivation':prefix+'pf13_identification.md',
         'records':records,'local_links':links,'manifest_sha256':manifest,
         'scope':'File integrity and finite calculation gates. The reconstruction and C2 arguments are mathematical proofs in the linked note; this script does not formally verify those theorems.'}
    p=Path(prefix+'artifact_audit.json');assert not p.exists()
    p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'all_passed':True,'artifacts':len(records),'local_links':len(links),'manifest_files':len(manifest)}))


if __name__=='__main__':main()
