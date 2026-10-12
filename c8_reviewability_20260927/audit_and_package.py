"""Bounded document/transcription audit and reviewer archive (no mode arithmetic).

Run from the repository through hi_cft_safe_run.py --limit-mib 1024.
Streams hashes/ZIP members; payload <=40MiB; expected peak <0.25GiB.
This is packaging/provenance validation, not a mathematical proof checker.
"""
import csv
import hashlib
import json
from pathlib import Path
import re
import resource
import signal
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
D = ROOT / 'c8_reviewability_20260927'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1024**2), b''):
            h.update(b)
    return h.hexdigest()


def read(name):
    p = ROOT / name
    assert p.stat().st_size < 30 * 1024**2
    return json.loads(p.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def join(a):
    return ','.join(map(str, a))


def check_tsv(name, expected):
    with (D / name).open(newline='') as f:
        rows = list(csv.reader(f, delimiter='\t'))
    expected = [[str(c) for c in row] for row in expected]
    assert rows[1:] == expected, name
    return len(expected)


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(120)
    potts = read('hi_cft_20260923_proof_potts_exact.json')
    pf = read('hi_cft_20260923_proof_pf13_exact.json')
    expected = []
    for name, fields in [('p', potts['potts_stress']),
                         ('w_P', potts['weight_three_primary']),
                         ('z', pf['stress']), ('w', pf['primary'])]:
        expected.extend([name, join(v['momentum']), join(v['oscillators']),
                         *v['coefficient']] for v in fields)
    counts = {'structural_fields.tsv': check_tsv('structural_fields.tsv', expected)}
    expected = []
    core = read('hi_cft_20260923_next_structure_core_extension.json')
    for b in core['blocks']:
        for e in b['joint_eigenspaces']:
            if e['PF13_weight'] == '12/13':
                for v in e['vectors']:
                    expected.extend([join(b['Cartan_weight']), join(r['momentum']),
                                     join(r['oscillators']), *r['coefficient']]
                                    for r in v['vector'])
    counts['core_spectral_witnesses.tsv'] = check_tsv('core_spectral_witnesses.tsv', expected)
    expected, pivots = [], []
    tops = read('hi_cft_20260923_next_81top_all.json')
    for sec in tops['sectors']:
        for i, row in enumerate(sec['rows']):
            rec = sec['recipes'][i]
            pivots.append([sec['glue_sign'], sec['sector_sign'], i, row[0][0],
                           join(rec['weight']), json.dumps(rec['input'], sort_keys=True),
                           json.dumps(rec['reductions']), json.dumps(rec['scale'])])
            if i < 2:
                expected.extend([sec['glue_sign'], sec['sector_sign'], i, j,
                                 join(sec['roots'][j]), *c,
                                 json.dumps(rec, sort_keys=True)] for j, c in row)
    counts['top81_pivots.tsv'] = check_tsv('top81_pivots.tsv', pivots)
    counts['top81_seeds_and_first_steps.tsv'] = check_tsv('top81_seeds_and_first_steps.tsv', expected)

    reports = {name: read(str((D / name).relative_to(ROOT))) for name in (
        'readable_checks.json', 'finite_witnesses.json', 'gate4_packet_checked.json',
        'membership_coordinate_check.json', 'current80_matrix_checks.json',
        'minimal_generation_checked.json')}
    assert reports['readable_checks.json']['status'] == 'pass'
    assert reports['finite_witnesses.json']['status'] == 'all_requested_saved_data_checks_passed'
    assert reports['gate4_packet_checked.json']['status'] == 'all_twelve_residuals_zero'
    for name in ('membership_coordinate_check.json', 'current80_matrix_checks.json'):
        assert reports[name]['status'] == 'pass'
    m = reports['minimal_generation_checked.json']
    assert m['basis_rows'] == 120 and m['target_expansions_checked_in_two_bases'] == 20
    assert m['unit_triangular_independence'] and not m['mode_products_recomputed']
    for path, digest in reports['readable_checks.json']['source_sha256'].items():
        assert sha(ROOT / path) == digest
    bindings = [
        ('gate4_packet_checked.json', 'packet_sha256', 'gate4_vectors.jsonl.gz'),
        ('gate4_packet_checked.json', 'relations_sha256', 'finite_witnesses.json'),
        ('gate4_packet_checked.json', 'checker_sha256', 'check_gate4_packet.py'),
        ('membership_coordinate_check.json', 'certificate_sha256', 'membership_witnesses.json'),
        ('membership_coordinate_check.json', 'checker_sha256', 'check_membership_coordinates.py'),
        ('current80_matrix_checks.json', 'certificate_sha256', 'current80_witness.json'),
        ('current80_matrix_checks.json', 'checker_sha256', 'check_current80_matrices.py'),
        ('minimal_generation_checked.json', 'witness_sha256', 'minimal_generation_witness.json'),
        ('minimal_generation_checked.json', 'verifier_sha256', 'export_minimal_generation.py'),
        ('minimal_generation_checked.json', 'arithmetic_helper_sha256', 'check_readable_inputs.py')]
    for report, key, path in bindings:
        assert reports[report][key] == sha(D / path), (report, key)

    docs = {}
    for stem, fragments in (
        ('hi_cft_c8_verification_guide', ['finite_inputs.tex', 'structural_inputs.tex']),
        ('hi_cft_c8_lean_assessment', ['lean_assessment.tex'])):
        body = (ROOT / (stem + '.tex')).read_text()
        body += ''.join((D / f).read_text() for f in fragments)
        labels = re.findall(r'\\label\{([^}]+)\}', body)
        refs = re.findall(r'\\(?:eqref|ref|pageref)\{([^}]+)\}', body)
        assert len(labels) == len(set(labels)), stem
        assert set(refs) <= set(labels), (stem, set(refs) - set(labels))
        log = (D / (stem.removeprefix('hi_cft_c8_') + '_final.log')).read_text()
        assert not re.search(r'^!|Overfull|Underfull|undefined|Rerun to get|may have changed', log, re.M)
        info = subprocess.check_output(['pdfinfo', str(ROOT / (stem + '.pdf'))], text=True, timeout=10)
        docs[stem] = {'pages': int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1)),
                      'labels': len(labels), 'references': len(refs), 'clean_build': True}
    old = read('c8_revision_20260927/package_manifest.json')
    unchanged = 0
    for archive in old['archives']:
        if archive['path'] == 'hi_cft_c8_proof_sources.zip':
            for path, digest in archive['member_sha256'].items():
                assert sha(ROOT / path) == digest, 'old source changed: ' + path
                unchanged += 1
    audit = {'status': 'pass', 'transcription_rows': counts, 'documents': docs,
             'checked_report_bindings': len(bindings), 'old_manuscript_source_files_unchanged': unchanged,
             'scope': 'Transcription, report bindings, local TeX references and packaging only; no new mathematical theorem.'}
    write(D / 'companion_audit.json', audit)

    names = '''hi_cft_c8_companions_README.md
hi_cft_c8_verification_guide.tex
hi_cft_c8_verification_guide.pdf
hi_cft_c8_lean_assessment.tex
hi_cft_c8_lean_assessment.pdf
hi_cft_c8_proof.pdf
hi_cft_c8_proof.tex
hi_cft_c8_manuscript_structure.tex
hi_cft_c8_manuscript_analytic.tex
hi_cft_c8_bibliography.tex
hi_cft_safe_run.py
hi_cft_20260923_c8_exact.py
hi_cft_20260923_c8_minimal_generators.py
hi_cft_20260923_c8_minimal_generators.json
hi_cft_20260923_c8_exact_fields.json
hi_cft_20260923_proof_potts_exact.json
hi_cft_20260923_proof_pf13_exact.json
hi_cft_20260923_next_structure_core_extension.json
hi_cft_20260923_next_81top_all.json
lean/HaagerupIzumi/CFT/FiniteClosure.lean
lean/HaagerupIzumi/CFT/TopBound.lean
lean/lean-toolchain
lean/lakefile.toml
c8_revision_20260927/lean_finite_closure_final.log
c8_revision_20260927/lean_top_bound.log
c8_revision_20260927/check_top_bound.py
c8_revision_20260927/package_manifest.json'''.splitlines()
    paths = [ROOT / n for n in names]
    for p in sorted(D.iterdir()):
        if p.suffix in ('.py', '.tex', '.tsv', '.md', '.json') and p.name not in (
                'reviewer_manifest.json', 'bundle_validation.json', 'portable_replay.json'):
            paths.append(p)
        elif p.name.endswith('_final.log') or p.name in (
                'gate4_vectors.jsonl.gz', 'readable_checks.log', 'finite_witnesses.log',
                'minimal_generation_checked.log', 'membership_coordinate_check.log',
                'current80_matrix_checks.log', 'gate4_packet_checked.log'):
            paths.append(p)
    paths = sorted(set(paths))
    assert all(p.is_file() for p in paths)
    total = sum(p.stat().st_size for p in paths)
    assert total < 40 * 1024**2
    records = {str(p.relative_to(ROOT)): {'bytes': p.stat().st_size, 'sha256': sha(p)} for p in paths}
    manifest = D / 'reviewer_manifest.json'
    write(manifest, {'format': 'c8-reviewability-manifest-v1', 'files': records,
                     'scope': 'Selected portable checks and reading material; not the full historical input graph.'})
    paths.append(manifest)
    output = ROOT / 'hi_cft_c8_reviewability_bundle.zip'
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
        for p in paths:
            z.write(p, 'hi_cft_c8_reviewability_bundle/' + str(p.relative_to(ROOT)))
    with zipfile.ZipFile(output) as z:
        assert z.testzip() is None
        for p in paths:
            digest = hashlib.sha256()
            with z.open('hi_cft_c8_reviewability_bundle/' + str(p.relative_to(ROOT))) as f:
                for b in iter(lambda: f.read(1024**2), b''):
                    digest.update(b)
            assert digest.hexdigest() == sha(p)
    result = {'status': 'pass', 'archive': output.name, 'members': len(paths),
              'uncompressed_bytes': total + manifest.stat().st_size,
              'archive_bytes': output.stat().st_size, 'sha256': sha(output),
              'all_zip_members_equal_manifest_sources': True}
    write(D / 'bundle_validation.json', result)
    print(json.dumps({'audit': audit, 'archive': result}), flush=True)


if __name__ == '__main__':
    main()
