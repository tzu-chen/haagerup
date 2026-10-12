"""Small exact cross-checks joining independently generated physics datasets.

Pure stdlib, streamed TSV, estimated<30MiB; run under512MiB guard.
This intentionally imports neither the mode engine nor either generator.
"""
import csv
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    tensor = HERE/'full_weight_two/complete_primary_couplings.tsv'
    correlators = json.loads((HERE/'correlators.json').read_text())
    basispath = HERE/'full_weight_two/low_weight_basis.json'
    basis = json.loads(basispath.read_text())['fields']
    assert len(basis) == 113
    assert basis[68]['name'] == 'v7_0_0' and basis[68]['Cartan_weight'] == [1,13]
    assert basis[95]['name'] == 'v7_1_13' and basis[95]['Cartan_weight'] == [-1,-13]
    assert [r['multiplet'] for r in basis[110:]] == [10,11,12]
    total = [F(0)]*4
    singlet = [F(0)]*4
    pair = []
    with tensor.open() as stream:
        for row in csv.DictReader(stream,delimiter='\t'):
            if (int(row['i']),int(row['j'])) != (68,95):
                continue
            square = list(map(F,json.loads(row['abs_C_squared_K4'])))
            total = [a+b for a,b in zip(total,square)]
            if int(row['k']) >= 110:
                singlet = [a+b for a,b in zip(singlet,square)]
            pair.append({'k':int(row['k']),'name':row['name_k'],'abs_C_squared':list(map(str,square))})
    assert total == [F(11,3),0,0,0], total
    stresses = [(F(1),F(1,4)),(F(117,41),F(195,164)),
                (F(2400,1271),F(180,1271)),(F(70,31),F(13,31))]
    stress_projection = sum(2*h*h/c for c,h in stresses)
    assert singlet == [stress_projection-1,0,0,0], singlet
    assert total[0]+1 == F(14,3)
    uu = correlators['u_four_point']
    global2 = F(uu['channels']['mpmp']['global_blocks']['global_primary_squared_coupling_sums'][2])
    assert total[0]+1 == global2 == F(uu['global_weight2']['total'])
    assert total[0] == F(uu['global_weight2']['other_Virasoro_primary_total'])
    assert stress_projection == F(uu['global_weight2']['four_orthogonal_stress_total'])
    # Exact hand derivation of the three-stress-normalization examples.
    cl,cr = F(1),F(117,41)
    assert 8*(cr-cl)**2/(cl*cr*(cl+cr)) == F(23104,9243)
    spectrum = json.loads((HERE/'data/characters.json').read_text())
    vacuum = spectrum['modules'][0]
    assert vacuum['state_multiplicities'][2] == 120
    assert vacuum['virasoro_primary_multiplicities_including_identity'][2] == 113
    sectors = json.loads((HERE/'defect_data.json').read_text())
    assert [r['module'] for r in spectrum['modules']] == sectors['labels']
    assert [r['h'] for r in spectrum['modules']] == sectors['lowest_weights']
    assert [r['state_multiplicities'][0] for r in spectrum['modules']] == sectors['top_dimensions']
    report = {'status':'PASS','u_conjugate_pair_indices':[68,95],
              'u_pair_primary_projection_sum':list(map(str,total)),
              'u_pair_total_stress_projection':'1','u_neutral_global_weight2':'14/3',
              'three_stress_primary_projection':list(map(str,singlet)),
              'four_stress_projection':str(stress_projection),'u_pair_nonzero_targets':pair,
              'complete_weight_two_primary_count':113,
              'spectrum_defect_labels_weights_tops_agree':True,
              'scope':'Independent exact arithmetic linking the113-primary tensor to the separate Gaussian four-point derivation, stress Ward identities, character count and defect sector conventions.',
              'source_sha256':{str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in [Path(__file__),tensor,basispath,HERE/'correlators.json',HERE/'data/characters.json',HERE/'defect_data.json']}}
    (HERE/'crosslink_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','u_pair_nonzero_targets':len(pair),'primary_projection':'11/3','basis_dimension':113}))


if __name__ == '__main__':
    main()
