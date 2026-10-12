"""Authenticate the completed c=8 certificate chain and freeze its proof ledger.

This checks certificate provenance and completion. The mathematical lemmas
and cited external theorems are human-readable proof inputs, not formalized
theorems checked by this program.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

ROOT = Path(__file__).resolve().parent
PREFIX = 'hi_cft_20260923_'
MIB = 1024**2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default=str(ROOT/(PREFIX+'c8two_proof_bundle.json')))
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024*MIB
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(180)
    started = monotonic()
    output = Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix('.json.tmp').exists()
    hashes = {}

    def bind(path, expected=None):
        path = Path(path).resolve()
        name = str(path)
        if name not in hashes:
            digest = hashlib.sha256()
            with path.open('rb') as stream:
                for block in iter(lambda: stream.read(MIB), b''):
                    digest.update(block)
            hashes[name] = digest.hexdigest()
        if expected is not None:
            assert hashes[name] == expected, name
        return hashes[name]

    def graphs(value):
        if isinstance(value, dict):
            for key, item in value.items():
                if key.endswith('source_sha256') or key == 'ancestor_files_sha256':
                    assert isinstance(item, dict)
                    for path, digest in item.items():
                        bind(path, digest)
                elif isinstance(item, (dict, list)):
                    graphs(item)
        elif isinstance(value, list):
            for item in value:
                graphs(item)

    def read(suffix):
        path = ROOT/(PREFIX+suffix+'.json')
        assert path.stat().st_size < 32*MIB
        value = json.loads(path.read_text())
        graphs(value)
        bind(path)
        return value

    lower = read('next_structure_lower_closure')
    assert lower['status'] == 'complete' and lower['cursor'] == lower['total_tasks'] == 3970
    p4 = read('next_structure_p4_controls')
    assert p4['status'] == 'exact_P4_triplet_and_lower_controls_passed'
    assert p4['current_zero_mode_controls'] == 18 and p4['positive_Virasoro_controls'] == 6
    bind(ROOT/p4['vectors_file'], p4['vectors_sha256'])
    charged = read('c8two_charged_span_verified')
    assert charged['status'] == 'charged_pair_current_span_is_exact_P3_quotient'
    assert charged['exact_quotient_dimension'] == charged['combined_rank'] == 322
    assert charged['sl2_and_cross_commutators_verified']
    gate4 = read('c8two_gate4_verified')
    assert gate4['status'] == 'all_Gate4_identities_proved_by_exact_seeds_and_raising'
    assert gate4['implied_A0P3_identity_count'] == 2898
    assert gate4['old_exact_seed_count'] == 2145
    assert gate4['additional_direct_exact_count'] == 118
    assert gate4['additional_singlet_exact_count'] == 12
    assert gate4['independent_projected_integer_residuals_zero'] == 12
    gate5 = read('c8two_gate5_verified')
    assert gate5['status'] == 'all_Gate5_families_proved_by_Jacobi'
    assert all(gate5[key] for key in ('all_eight_charged_pair_data_passed',
        'all_eight_charged_families_derived', 'Gate4_certificate_authenticated',
        'charged_pair_span_certificate_authenticated', 'neutral_family_derived',
        'all24_independent_Gate5_channels'))
    # Older producers used three different provenance encodings. Preserve
    # their scopes and verify the actual encoding rather than treating an
    # old partial certificate as a standalone identification theorem.
    legacy_names = [
        'proof_current_module_v2', 'next_81top_all', 'proof_potts',
        'proof_potts_exact', 'proof_rational_core', 'proof_pf13_exact',
        'proof_pf13_membership', 'proof_pf13_ope', 'proof_pf13_nonlinear',
        'proof_pf13_truncation', 'proof_pf13_dly', 'proof_pf13_simple_pole_algebra',
        'proof_pf13_upper_poles', 'proof_remaining_coset',
        'next_structure_core_extension', 'next_structure_order13_top_check',
        'next_m3_harmonic_theta_v2', 'next_m3_reverse_theta_check',
    ]
    legacy = {}
    for suffix in legacy_names:
        path = ROOT/(PREFIX+suffix+'.json')
        assert path.stat().st_size < 32*MIB
        value = json.loads(path.read_text())
        graph_value = dict(value)
        if isinstance(value.get('source_sha256'), str):
            bind(ROOT/(PREFIX+suffix+'.py'), graph_value.pop('source_sha256'))
        graphs(graph_value)
        for key in ('sources', 'sha256'):
            if key in value:
                assert isinstance(value[key], dict)
                for filename, digest in value[key].items():
                    bind(ROOT/filename, digest)
        bind(path)
        legacy[suffix] = value
    assert legacy['proof_current_module_v2']['zero_mode_algebra_on_complement_is_irreducible']
    assert legacy['next_81top_all']['status'] == 'complete'
    assert legacy['proof_potts_exact']['exact_membership_in_generated_S3']
    assert legacy['proof_pf13_membership']['exact_membership_in_generated_S3']
    assert legacy['proof_pf13_nonlinear']['exact_Linshaw_5_7_simple_pole']
    assert legacy['proof_pf13_truncation']['exact_W6_truncation']
    assert legacy['proof_pf13_dly']['matches_DLY_Appendix_B_exactly']
    assert legacy['proof_pf13_upper_poles']['all_checked_upper_poles_match']
    assert legacy['next_structure_core_extension']['all_six_order13_target_weights_present']
    assert legacy['next_structure_order13_top_check']['exact_table_verified']
    assert legacy['next_structure_order13_top_check']['exact_dual_verified']
    notes = [
        'c8_construction_report', 'c8two_final_theorem', 'c8two_report',
        'c8two_jacobi_proof', 'c8two_certificate_audit',
        'c8two_structure_final_audit', 'c8two_structure_properness_dependency',
        'c8two_h4_singlet_independent_audit',
        'next_structure_h4_certificate', 'next_structure_recursive_strong_certificate',
        'next_structure_rationality', 'next_structure_vacuum_projective',
        'next_structure_order13_top_bound', 'next_structure_rank46',
        'next_m3_universal_data', 'next_m3_universal_independent_audit',
        'next_structure_m6_balanced_exclusion', 'next_structure_m6_universal_projection',
        'next_m6_independent_audit', 'next_structure_rank6_indicators',
        'next_rank6_root_audit', 'next_structure_rank6_center',
        'next_structure_conditional_characters', 'next_structure_final_dependency_audit',
        'proof_report', 'proof_pf13_identification', 'next_c8_proof_audit',
        'next_structure_order13_core', 'next_structure_independent_audit',
        'next_structure_c2_energy_bound', 'next_c2_energy_independent_audit',
        'next_structure_m3_character_obstruction', 'next_m3_reverse_theta_derivation',
        'next_structure_m6_character_obstruction', 'next_m3_unitarity_scope',
    ]
    for suffix in notes:
        bind(ROOT/(PREFIX+suffix+'.md'))
    bind(__file__)
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 256*1024
    result = {
        'format': 'c8-completed-proof-provenance-ledger-v1',
        'status': 'all_finite_certificate_premises_authenticated',
        'lower_exact_identities': 3970,
        'P4_current_controls': 18, 'P4_Virasoro_controls': 6,
        'Gate4_identities': 2898, 'Gate5_independent_channels': 24,
        'charged_quotient_dimension': 322,
        'source_sha256': hashes,
        'human_proof_notes': [PREFIX+name+'.md' for name in notes],
        'earlier_exact_inputs': [PREFIX+name+'.json' for name in legacy_names],
        'mathematical_conclusion_by_linked_lemmas':
            'U is proper in V(E6+A2), dim U1=6; the linked identification theorem applies.',
        'scope': 'Hashes and completed certificate premises are checked here. '
            'This is a computer-assisted proof ledger, not proof-assistant verification '
            'of the mathematical lemmas or external classification/analytic theorems.',
        'seconds': monotonic()-started,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    data = json.dumps(result, indent=2).encode()
    assert len(data) < 8*MIB
    temporary = output.with_suffix('.json.tmp')
    temporary.write_bytes(data)
    temporary.replace(output)
    signal.alarm(0)
    print({'status': result['status'], 'authenticated_files': len(hashes),
           'seconds': result['seconds'], 'peak_rss_KiB': result['peak_rss_KiB']}, flush=True)


if __name__ == '__main__':
    main()
