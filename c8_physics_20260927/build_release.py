"""Build a reproducible physics bundle, or replay its producers in a fresh tree.

Root runs through hi_cft_safe_run.py. Bundle expected<100MiB RSS, replay
<300MiB; AS1GiB for replay, one child at a time, no workers. The replay
inherits the guard rather than acquiring a second nested lock.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from time import monotonic
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(65536),b''):
            h.update(block)
    return h.hexdigest()


def release_files():
    root_names = ['hi_cft_c8_proof.pdf','hi_cft_c8_proof.tex','hi_cft_c8_proof.aux','hi_cft_c8_proof_README.md',
        'hi_cft_c8_manuscript_structure.tex','hi_cft_c8_manuscript_analytic.tex',
        'hi_cft_c8_bibliography.tex','hi_cft_c8_lean_assessment.pdf','hi_cft_c8_lean_assessment.tex',
        'hi_cft_c8_companions_README.md','hi_cft_c8_verification_guide.pdf',
        'hi_cft_c8_verification_guide.tex','c8_reviewability_20260927/structural_inputs.tex',
        'hi_cft_c8_reviewability_bundle.zip','hi_cft_safe_run.py',
        'hi_cft_20260923_c8_exact.py','hi_cft_20260923_c8_exact_fields.json',
        'hi_cft_20260923_proof_pf13_ope.json','hi_cft_20260923_proof_pf13_upper_poles.py',
        'hi_cft_20260923_proof_pf13_upper_poles.json',
        'hi_cft_third_flavoured_trace_check.py','hi_cft_third_rank3_current_series.py',
        'hi_cft_20260923_next_structure_conditional_characters.md',
        'c8_reviewability_20260927/check_readable_inputs.py',
        'c8_reviewability_20260927/lean_assessment.tex',
        'lean/HaagerupIzumi/CFT/PhysicsBounds.lean',
        'lean/HaagerupIzumi/CFT/FiniteClosure.lean','lean/HaagerupIzumi/CFT/TopBound.lean',
        'lean/safe_lean.py','lean/tools/lean_stack_limit.c','lean/lean-toolchain',
        'lean/lakefile.toml','lean/lake-manifest.json']
    paths = [ROOT/name for name in root_names]
    for path in HERE.rglob('*'):
        if not path.is_file():
            continue
        rel = path.relative_to(HERE)
        if any(p.endswith('_initial') or p == '__pycache__' for p in rel.parts):
            continue
        if path.name in ('ahkz_2512.08225v2.pdf','release_manifest.json',
                         'bundle_build_final.log','bundle_verification.json','bundle_verification_final.log'):
            continue
        if path.suffix not in ('.py','.md','.tex','.json','.tsv','.jsonl','.pdf','.svg','.log'):
            continue
        # Generated TeX build intermediates and obsolete failed attempts are
        # not release data. Keep final audit logs and the frozen baseline.
        if path.suffix == '.log' and not any(s in path.name for s in ('final','physics_lean','release_replay')):
            continue
        if path.name.endswith('_bbox.html'):
            continue
        paths.append(path)
    assert all(p.is_file() for p in paths)
    paths = sorted(set(paths))
    assert sum(p.stat().st_size for p in paths) < 150*1024**2
    return paths


def package():
    files = release_files()
    manifest = {'schema':'haagerup-c8-physics-release-v1',
        'scope':'Current physics-first manuscript, exact data/producers, both current companion guides with manuscript references, and frozen earlier input-review bundle. Mathematical construction hypotheses remain as documented.',
        'files':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files],
        'excluded':'Full third-party AHKZ paper; transient build products; initial duplicate runs; Lean toolchain/Mathlib binary cache.',
        'manifest_note':'The manifest authenticates all other bundle members; it does not hash itself.'}
    destination = ROOT/'hi_cft_c8_physics_bundle.zip'
    manifest_path = HERE/'release_manifest.json'
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n')
    with zipfile.ZipFile(destination,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as archive:
        for path in files+[manifest_path]:
            archive.write(path,str(path.relative_to(ROOT)))
    with zipfile.ZipFile(destination) as archive:
        assert archive.testzip() is None
        assert len(archive.namelist()) == len(files)+1
        for row in manifest['files']:
            assert hashlib.sha256(archive.read(row['path'])).hexdigest() == row['sha256']
    print(json.dumps({'status':'PASS','bundle':str(destination),'members':len(files)+1,
                      'bytes':destination.stat().st_size,'sha256':sha(destination)}))


def replay():
    start = monotonic()
    directory = Path(tempfile.mkdtemp(prefix='c8-physics-release-replay-'))
    for path in release_files():
        target = directory/path.relative_to(ROOT)
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(path,target)
    work = directory/'replayed'
    work.mkdir()
    producer = directory/'c8_physics_20260927'
    commands = [
        ('spectrum',[str(producer/'spectrum.py'),'--order','24','--delta-cut','24','--outdir',str(work/'spectrum')],300),
        ('primary_seeds',[str(producer/'full_weight_two.py'),'--output-dir',str(work/'primaries')],920),
        ('primary_tensor',[str(producer/'complete_weight_two.py'),'--data-dir',str(work/'primaries')],300),
        ('correlators',[str(producer/'correlators.py'),'--output',str(work/'correlators.json')],130),
        ('defects',[str(producer/'defects.py'),'--output-dir',str(work/'defects')],300),
        ('crosslinks',[str(producer/'check_physics_crosslinks.py')],30)]
    completed = []
    for name,args,limit in commands:
        with (work/f'{name}.log').open('w') as stream:
            result = subprocess.run([sys.executable,*args],cwd=directory,stdout=stream,
                                    stderr=subprocess.STDOUT,timeout=limit)
        if result.returncode:
            raise RuntimeError(f'{name} failed: {work/name}.log')
        completed.append(name)
        print(json.dumps({'replayed':name}),flush=True)
    comparisons = []
    for path in (work/'spectrum').glob('*'):
        if path.name != 'run_summary.json':
            comparisons.append((path,producer/'data'/path.name))
    for path in (work/'primaries').glob('*'):
        if path.name not in ('low_weight_couplings.json','complete_primary_couplings.json'):
            comparisons.append((path,producer/'full_weight_two'/path.name))
    for suffix in ('.terms.tsv','.global_blocks.tsv','.samples.tsv'):
        comparisons.append((work/('correlators'+suffix),producer/('correlators'+suffix)))
    for path in (work/'defects').glob('*.tsv'):
        comparisons.append((path,producer/path.name))
    for new,old in comparisons:
        assert sha(new) == sha(old), ('replay differs',str(new),str(old))
    # Compare structured values after removing explicitly variable run metadata.
    structured = [(work/'correlators.json',producer/'correlators.json',('seconds','peak_rss_KiB')),
        (work/'defects/defect_data.json',producer/'defect_data.json',('seconds',)),
        (work/'primaries/low_weight_couplings.json',producer/'full_weight_two/low_weight_couplings.json',('seconds','peak_rss_KiB')),
        (work/'primaries/complete_primary_couplings.json',producer/'full_weight_two/complete_primary_couplings.json',('elapsed_seconds','peak_RSS_KiB','source_sha256'))]
    for new,old,ignored in structured:
        a,b=json.loads(new.read_text()),json.loads(old.read_text())
        for key in ignored:
            a.pop(key,None);b.pop(key,None)
        assert a == b, ('structured replay differs',new)
    result = {'status':'PASS','fresh_tree':str(directory),'producers':completed,
              'byte_identical_payload_files':len(comparisons),'structured_payload_comparisons':len(structured),
              'ignored_run_metadata':'elapsed time, measured RSS and absolute fresh-output locations only',
              'elapsed_seconds':monotonic()-start,
              'scope':'Fresh-tree arithmetic replay from the same files selected for the release. Does not replay the entire historical CFT construction or bootstrap SDP.'}
    (HERE/'release_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay',action='store_true')
    args=parser.parse_args()
    replay() if args.replay else package()
