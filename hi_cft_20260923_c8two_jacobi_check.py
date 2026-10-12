"""Root-only exact replay of the small Jacobi reduction of Gate5.

No new VOA mode or native solve is evaluated. Two closed H4 bottom
witnesses and eight exact S2-by-S2 quotient identities are authenticated.
Gate4 and charged-span certificates are optional explicit prerequisites;
without them the corresponding conclusion is labelled conditional.
"""
import argparse
from contextlib import closing
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic
import sqlite3
import zlib

import hi_cft_20260923_c8two_structure_saturation as auth
import hi_cft_20260923_next_structure_lower_closure as lower

F = auth.fast.FastField
ZERO, ONE = F(0), F(1)
MIB = 1024**2
MAX_BITS = 4096
PAIRS = ((0,3),(1,3),(2,3),(3,6),(4,6),(5,3),(6,3),(7,3))
WITNESSES = {3:'r3_000910',6:'r3_000899'}


def read_json(path,limit=8*MIB):
    path = Path(path).resolve()
    assert path.is_file() and path.stat().st_size <= limit
    return json.loads(path.read_text())


def unpack(blob,limit=8*MIB):
    decoder = zlib.decompressobj()
    raw = decoder.decompress(blob,limit+1)
    assert len(raw) <= limit and decoder.eof and not decoder.unconsumed_tail
    return json.loads(raw)


def field(value):
    out = F(value)
    assert max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in out) <= MAX_BITS
    return out


def add(out,key,value):
    value = out.get(key,ZERO)+value
    if value:
        field(value)
        out[key] = value
    else:
        out.pop(key,None)


def packed(vector):
    return [[key,[str(q) for q in value]] for key,value in sorted(vector.items())]


def closed(path,limit=512*MIB):
    path = Path(path).resolve()
    assert path.is_file() and path.stat().st_size <= limit
    assert not Path(str(path)+'-journal').exists() and not Path(str(path)+'-wal').exists()
    db = sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1',uri=True)
    db.execute('PRAGMA cache_size=-2048')
    db.execute('PRAGMA mmap_size=0')
    return db


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--lower-summary',default='hi_cft_20260923_next_structure_lower_closure.json')
    parser.add_argument('--h4-database',default='hi_cft_20260923_c8two_targeted_h4_trimmed_v2/block_p0_m2.sqlite')
    parser.add_argument('--saturation',default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--gate4')
    parser.add_argument('--charged-span')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_jacobi_checked.json')
    parser.add_argument('--seconds',type=int,default=180)
    args = parser.parse_args()
    assert 0 < args.seconds <= 300
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    output = Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix(output.suffix+'.tmp').exists()
    started = monotonic()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('Jacobi replay alarm')))
    signal.alarm(args.seconds)
    bindings = {}

    def boundary():
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss <= 512*1024,'512 MiB RSS review boundary'
        assert monotonic()-started <= args.seconds,'Jacobi replay time boundary'

    def bind(path):
        path = str(Path(path).resolve())
        digest = auth.sha(path)
        assert path not in bindings or bindings[path] == digest
        bindings[path] = digest
        return path

    try:
        for path in (__file__,auth.__file__,lower.__file__,auth.fast.__file__,auth.frozen.__file__):
            bind(path)
        manifest = Path(args.checkpoint).resolve()/'manifest.json'
        meta = read_json(manifest)
        assert meta['format'] == 'exact-cartan-span-v1' and meta['completed_grade3']
        assert meta['dimensions']['2'] == 120 and meta['dimensions']['3'] == 956
        assert any(h['stage'] == 'grade3 translation descendants' and h['dimensions']['3'] == 634 for h in meta['history'])
        order2,order3 = meta['order']['2'],meta['order']['3']
        assert len(order2) == len(set(order2)) == 120
        assert len(order3) == len(set(order3)) == 956
        normal3,quotient = set(order3[:634]),set(order3[634:])
        auth.verify_graph(meta['sources'],bindings)
        bind(manifest)

        sat = read_json(args.saturation,32*MIB)
        assert sat['status'] == 'complete' and sat['arithmetic'] == 'exact'
        assert sat['S3_dimension'] == 956 and sat['N3_dimension'] == 634
        assert sat['quotient_order'] == order3[634:]
        auth.verify_graph(sat['raising_source_sha256'],bindings)
        bind(args.saturation)
        weights3 = dict(zip(sat['quotient_order'],map(tuple,sat['quotient_weights'])))
        assert len(weights3) == 322

        lm = read_json(args.lower_summary)
        assert lm['format'] == lower.FORMAT and lm['status'] == 'complete'
        assert lm['cursor'] == lm['total_tasks'] == 3970
        auth.nested_graphs(lm,bindings)
        bind(args.lower_summary)
        lowerdb = Path(lm['sqlite_file']).resolve()
        bind(lowerdb)
        unitary_path = Path('hi_cft_20260923_c8_exact_unitary_certificate.json')
        unitary = read_json(unitary_path)
        assert unitary['exact_PCT_preservation']
        assert len(unitary['primary_checks']) == 8
        assert all(row['exact_primary_and_eigenvalue_checks'] for row in unitary['primary_checks'])
        auth.nested_graphs(unitary,bindings)
        bind(unitary_path)
        p4path = Path('hi_cft_20260923_next_structure_p4_controls.json')
        p4 = read_json(p4path)
        assert p4['status'] == 'exact_P4_triplet_and_lower_controls_passed'
        assert auth.sha(p4['vectors_file']) == p4['vectors_sha256']
        auth.nested_graphs(p4,bindings)
        bind(p4path);bind(p4['vectors_file'])

        # Only the small grade-two basis is loaded; no lattice mode is called.
        rows,blocks,total = {},{},0
        for filename in meta['block_files']:
            if not filename.startswith('grade2_'):
                continue
            path = manifest.parent/filename
            assert auth.sha(path) == meta['files_sha256'][filename]
            bind(path)
            for record in auth.frozen.row_stream(path):
                name,weight = record['id'],tuple(record['weight'])
                assert name in order2 and name not in rows and record['grade'] == 2
                vector = {(tuple(a),tuple(o)):field(c) for a,o,c in record['vector']}
                assert 0 < len(vector) == len(record['vector']) <= 20000 and all(vector.values())
                assert all(auth.x.grade(s) == 2 and auth.x.weight(s) == weight for s in vector)
                pivot = min(vector)
                assert vector[pivot] == ONE
                block = blocks.setdefault(weight,{})
                assert pivot not in block
                block[pivot] = name
                rows[name] = vector
                total += len(vector)
                assert total <= 50000
                boundary()
        assert set(rows) == set(order2)

        fields_path = Path('hi_cft_20260923_c8_exact_fields.json')
        data = read_json(fields_path)['fields']
        assert len(data) == 9
        assert str(fields_path.resolve()) in bindings and bindings[str(fields_path.resolve())] == auth.sha(fields_path)
        operators,opweights = [],[]
        for op,row in enumerate(data[:8]):
            vector = {}
            for item in row['coefficients']:
                parts = item['Qsqrt13_sqrtminus3']
                state = (tuple(item['momentum']),tuple(item['oscillators']))
                assert state not in vector
                value = field(parts[0]+parts[1])
                if value:
                    vector[state] = value
            ws = {auth.x.weight(s) for s in vector}
            assert len(ws) == 1 and all(auth.x.grade(s) == 2 for s in vector)
            weight = ws.pop()
            assert list(row['dimensions']) == unitary['primary_checks'][op]['dimensions']
            assert weight == tuple(v-1 for v in row['dimensions'])
            operators.append(vector);opweights.append(weight)
        assert opweights == [(0,4),(0,8),(0,8),(0,12),(1,1),(1,5),(1,7),(1,13)]

        decompositions = {}
        for op in (3,6):
            residual = dict(operators[op]);coordinates = {}
            for pivot,name in sorted(blocks[opweights[op]].items()):
                value = residual.get(pivot,ZERO)
                if value:
                    coordinates[name] = value
                    for state,c in rows[name].items():
                        add(residual,state,-value*c)
            assert not residual,'Primitive highest vector must decompose exactly in saved S2'
            decompositions[op] = coordinates

        work = lower.tasks(meta)
        ids = {tuple(task):i for i,task in enumerate(work)}
        assert len(ids) == 3970
        pairs = []
        with closing(closed(lowerdb,256*MIB)) as db:
            assert read_json(args.lower_summary) == json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            assert db.execute('SELECT COUNT(*) FROM identities').fetchone()[0] == 3970
            for a,b in PAIRS:
                answer = {}
                used = []
                for right,c in decompositions[b].items():
                    task = ('weight_two',a,right,0,3)
                    idx = ids[task]
                    recipe,targetsha,relation,residual = db.execute(
                        'SELECT recipe,target_sha256,relation,residual FROM identities WHERE id=?',(idx,)).fetchone()
                    assert json.loads(recipe) == list(task) and unpack(residual) == []
                    values = unpack(relation)
                    assert len(values) == len({name for name,_ in values}) <= 956
                    for name,value in values:
                        assert name in normal3 or name in quotient
                        add(answer,name,c*field(value))
                    record_hash = hashlib.sha256(recipe.encode()+b'\0'+targetsha.encode()+b'\0'+relation+b'\0'+residual).hexdigest()
                    used.append({'id':idx,'recipe':list(task),'record_sha256':record_hash})
                assert not (set(answer)&quotient),('Charged pair has nonzero exact S3/N3 component',a,b)
                pweight = weights3[WITNESSES[b]]
                beta_weight = tuple(s+t for s,t in zip(opweights[a],pweight))
                assert beta_weight not in ((0,-2),(0,0),(0,2))
                pairs.append({'a':a,'b':b,'right_bottom_input':WITNESSES[b],
                    'a_zero_p_weight':list(beta_weight),'beta_a_p_vanishes_by_weight':True,
                    'B_a_b_exact_quotient_zero':True,'normal3_coefficients':packed(answer),
                    'lower_records':used})
                boundary()

        witnesses = []
        h4path = Path(args.h4_database).resolve()
        with closing(closed(h4path)) as db:
            hm = json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            assert hm['format'] == 'exact-n4-selected-block-v1' and hm['failed_targets'] == 0
            assert hm['P4_columns']['-3'] == {'id':'P4_minus','weight':[0,-2]}
            auth.nested_graphs(hm,bindings)
            for b,name in WITNESSES.items():
                assert tuple(s+t for s,t in zip(opweights[b],weights3[name])) == (0,-2)
                key = 'A%d_zero_%s'%(b,name)
                blob,digest,passed = db.execute('SELECT record,digest,passed FROM relations WHERE name=?',(key,)).fetchone()
                assert passed == 1
                record = auth.unpack(blob,digest)
                assert record['word'] == {'operator':b,'mode':0,'exact_input':name}
                assert record['exact_residual_zero'] and record['residual'] == []
                assert record['negative_columns_are_exact_P4_fields']
                coefficients = record['normal_word_coefficients']
                assert len(coefficients) == len({i for i,_ in coefficients}) <= 300
                beta = ZERO
                for idx,value in coefficients:
                    assert idx in hm['extended_columns']
                    c = field(value)
                    if idx < 0:
                        assert idx == -3
                        beta = c
                assert beta,'A nonzero bottom coefficient is essential'
                witnesses.append({'operator':b,'input':name,'input_weight':list(weights3[name]),
                    'record_name':key,'record_sha256':digest,'P4_minus_coefficient':[str(q) for q in beta],
                    'exact_residual_zero':True})
        bind(h4path)

        gate4 = False
        if args.gate4:
            certificate = read_json(args.gate4,32*MIB)
            assert certificate['format'] == 'verified-H4-raising-certificate-v1'
            assert certificate['status'] == 'all_Gate4_identities_proved_by_exact_seeds_and_raising'
            assert certificate['implied_A0P3_identity_count'] == 2898
            auth.nested_graphs(certificate,bindings);bind(args.gate4)
            gate4 = True
        charged_span = False
        if args.charged_span:
            certificate = read_json(args.charged_span,32*MIB)
            assert certificate['format'] == 'charged-zero-product-quotient-span-v1'
            assert certificate['status'] == 'charged_zero_products_span_exact_quotient'
            assert certificate['combined_rank'] == certificate['quotient_dimension'] == 322
            assert certificate['quotient_order'] == order3[634:]
            auth.nested_graphs(certificate,bindings);bind(args.charged_span)
            charged_span = True
        boundary()
        assert str(output) not in bindings and str(output.with_suffix(output.suffix+'.tmp')) not in bindings
        result = {'format':'exact-Jacobi-Gate5-data-v1',
            'status':'all_Gate5_families_proved_by_Jacobi' if gate4 and charged_span else 'exact_Jacobi_data_passed_conditional_prerequisites',
            'source_sha256':bindings,'grade2_input_terms':total,
            'primitive_decompositions':{str(op):packed(c) for op,c in decompositions.items()},
            'bottom_witnesses':witnesses,'charged_pair_checks':pairs,
            'all_eight_charged_pair_data_passed':True,
            'all_eight_charged_families_derived':gate4,'Gate4_certificate_authenticated':gate4,
            'charged_pair_span_certificate_authenticated':charged_span,
            'neutral_family_derived':gate4 and charged_span,
            'all24_independent_Gate5_channels':gate4 and charged_span,
            'lemma_dependencies':['S2_0 N4 subset N5','N3_0 S3 subset N5',
                'bottom Jacobi identity followed by current raising',
                'charged-pair spanning gives neutral Jacobi identity',
                'second neutral field from ambient stress minus affine stresses'],
            'scope':'No unknown N4 upper bound or new grade5 mode. Charged conclusions use the audited Jacobi lemma and require Gate4. Neutral additionally requires charged-pair quotient spanning. Properness follows only with the separately audited finite strong-generation theorem.',
            'seconds':monotonic()-started,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        auth.atomic(output,result)
        print({key:result[key] for key in ('status','Gate4_certificate_authenticated',
            'charged_pair_span_certificate_authenticated','seconds','peak_rss_KiB')},flush=True)
    finally:
        signal.alarm(0)


if __name__ == '__main__':
    main()
