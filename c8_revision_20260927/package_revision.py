"""Package the finished manuscript and a bounded subset of its check records.

Run through hi_cft_safe_run.py with 512 MiB AS. Estimated peak <64 MiB:
one streaming ZIP member, a 1 MiB hash buffer, small path/hash manifests.
The checks archive does not contain the full historical certificate graph.
"""
from pathlib import Path
import hashlib
import json
import os
import resource
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REV = ROOT / 'c8_revision_20260927'
MIB = 1024**2


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(MIB), b''):
            result.update(block)
    return result.hexdigest()


def pack(name, files):
    files = sorted(set(files))
    assert all(path.is_file() and not path.is_symlink() for path in files)
    assert all(path.stat().st_size <= 8*MIB for path in files)
    assert sum(path.stat().st_size for path in files) <= 32*MIB
    before = {str(path.relative_to(ROOT)): digest(path) for path in files}
    output = ROOT / name
    temp = output.with_suffix('.zip.tmp')
    with zipfile.ZipFile(temp, 'x', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=6) as archive:
        for path in files:
            archive.write(path, str(path.relative_to(ROOT)))
    with zipfile.ZipFile(temp) as archive:
        assert archive.testzip() is None
        assert set(archive.namelist()) == set(before)
        for member, expected in before.items():
            result = hashlib.sha256()
            with archive.open(member) as stream:
                for block in iter(lambda: stream.read(MIB), b''):
                    result.update(block)
            assert result.hexdigest() == expected
    assert {str(path.relative_to(ROOT)): digest(path) for path in files} == before
    os.replace(temp, output)
    return {'path': name, 'files': len(files), 'bytes': output.stat().st_size,
            'sha256': digest(output), 'member_sha256': before}


def main():
    soft, _ = resource.getrlimit(resource.RLIMIT_AS)
    assert 0 < soft <= 512*MIB
    assert len(os.sched_getaffinity(0)) <= 2
    assert (REV/'baseline/hi_cft_c8_proof_sources.zip').is_file()
    assert json.loads((REV/'document_audit_complete.json').read_text())['status'] == 'pass'
    sources = [ROOT/name for name in [
        'hi_cft_c8_proof.tex', 'hi_cft_c8_manuscript_structure.tex',
        'hi_cft_c8_manuscript_analytic.tex', 'hi_cft_c8_bibliography.tex',
        'hi_cft_c8_proof_README.md', 'hi_cft_c8_manuscript_review.md',
        'hi_cft_c8_proof_build.log']]
    checks = list((ROOT/'lean/HaagerupIzumi/CFT').glob('*.lean'))
    checks += [ROOT/'lean/HaagerupIzumi/CFT/README.md']
    checks += list(ROOT.glob('hi_cft_c8_revision_20260927_*.md'))
    checks += list(REV.glob('*_replay.json'))
    checks += [REV/name for name in [
        'finite_input_ledger_complete.json', 'finite_input_ledger_complete.log',
        'document_audit_complete.json', 'document_audit_complete.log',
        'authenticate_inputs.py', 'complete_ledger_command.sh', 'audit_document.py',
        'check_top_bound.py', 'replay_structural_input.py', 'package_revision.py',
        'replay_commands.md', 'revision_summary.md', 'resource_review.md',
        'structural_replay_review.md', 'checks_archive_README.md',
        'lean_finite_closure_final.log', 'lean_top_bound.log',
        'charged_span_replay.log', 'core_extension_replay.log',
        'gate4_replay.log', 'gate5_replay_corrected.log', 'grade3_replay.log',
        'minimal_generators_replay.log', 'pf13_membership_replay.log',
        'potts_replay.log', 'top81_replay.log', 'top_bound_replay.log',
        'unitary_replay.log']]
    checks += [ROOT/name for name in [
        'hi_cft_safe_run.py', 'lean/safe_lean.py', 'lean/tools/lean_stack_limit.c',
        'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
    result = {'status': 'pass', 'scope': 'Source archive and selected check records; '
              'the checks archive is not the full historical certificate input graph.',
              'archives': [pack('hi_cft_c8_proof_sources.zip', sources),
                           pack('hi_cft_c8_revision_checks.zip', checks)]}
    with (REV/'package_manifest.json').open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': result['status'], 'archives': [
        {key: archive[key] for key in ['path', 'files', 'bytes', 'sha256']}
        for archive in result['archives']]}))


if __name__ == '__main__':
    main()
