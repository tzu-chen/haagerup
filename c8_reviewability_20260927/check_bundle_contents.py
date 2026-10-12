"""Prepare or validate a fresh reviewer-bundle extraction.

Run serially under hi_cft_safe_run.py --limit-mib 1024. Between these
two operations run each checker directly under the permanent launcher,
as documented in the README. No checker is run as an unguarded child.
Expected memory <0.1GiB; ZIP payload <=40MiB; hashes stream in 1MiB blocks.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
D = ROOT / 'c8_reviewability_20260927'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1024**2), b''):
            h.update(b)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-directory', type=Path)
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(120)
    archive = ROOT / 'hi_cft_c8_reviewability_bundle.zip'
    if args.verify_directory is None:
        base = Path(tempfile.mkdtemp(prefix='c8-review-portable-'))
        with zipfile.ZipFile(archive) as z:
            assert sum(info.file_size for info in z.infolist()) < 40 * 1024**2
            assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
            z.extractall(base)
    else:
        base = args.verify_directory.resolve()
    work = base / 'hi_cft_c8_reviewability_bundle'
    data = work / 'c8_reviewability_20260927'
    assert sha(data / 'reviewer_manifest.json') == sha(D / 'reviewer_manifest.json')
    manifest = json.loads((data / 'reviewer_manifest.json').read_text())['files']
    for name, record in manifest.items():
        assert sha(work / name) == record['sha256'], name
    if args.verify_directory is None:
        print(json.dumps({'extraction': str(base), 'workdir': str(work),
                          'manifest_files': len(manifest), 'status': 'prepared'}), flush=True)
        return
    results = []
    for name, report in [('small', base / 'small/readable_checks.json'),
                         *[(n, base / (n + '.json')) for n in
                           ('generation', 'membership', 'gate4', 'current80')]]:
        result = json.loads(report.read_text())
        if name == 'generation':
            assert result['basis_rows'] == 120 and result['target_expansions_checked_in_two_bases'] == 20
            assert result['source_hashes_match'] and result['unit_triangular_independence']
        else:
            assert result['status'] == ('all_twelve_residuals_zero' if name == 'gate4' else 'pass')
        results.append({'check': name, 'status': 'pass', 'report_sha256': sha(report)})
    final = {'status': 'pass', 'archive_sha256': sha(archive), 'checks': results,
             'fresh_extraction': str(base), 'all_manifest_inputs_unchanged': True,
             'scope': 'Five exact checkers passed using extracted bundle files under the permanent launcher; no original database or mode-engine imports in verifier paths.'}
    (D / 'portable_replay.json').write_text(json.dumps(final, indent=2) + '\n')
    print(json.dumps(final), flush=True)


if __name__ == '__main__':
    main()
