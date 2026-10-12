"""Independent exact linear-relation replay; no lattice mode generation.

Root launches only through hi_cft_safe_run.py. Reconstructs each recorded
target from frozen basis vectors and saved relation coefficients, using a
bit-mask field product independent of FastField's closed formulas. Target
recipes and digests are bound to the completed mode-producing certificate;
the lattice mode oracle is not independently recomputed by this consumer.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib

from gmpy2 import mpq

MIB = 1024**2
CAP = 8*MIB
ZERO = (mpq(0),)*4
ONE = (mpq(1),mpq(0),mpq(0),mpq(0))


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(path):
    out = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(MIB), b''):
            out.update(chunk)
    return out.hexdigest()


def scalar(value):
    assert isinstance(value, (list, tuple)) and len(value) == 4
    result = tuple(mpq(q) for q in value)
    assert all(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) <= 4096
               for q in result)
    return result


def product(a,b):
    # Independent basis multiplication: s^2=13,t^2=-3; shared bits reduce.
    out = [mpq(0) for _ in range(4)]
    for i, value in enumerate(a):
        if not value:
            continue
        for j, other in enumerate(b):
            if other:
                factor = (13 if i & j & 1 else 1)*(-3 if i & j & 2 else 1)
                out[i ^ j] += value*other*factor
    return tuple(out)


def add_scaled(out, factor, vector):
    for state, value in vector.items():
        added = product(factor, value)
        old = out.get(state, ZERO)
        result = tuple(a+b for a,b in zip(old,added))
        if any(result):
            out[state] = result
        else:
            out.pop(state, None)


def pack_vector(vector):
    return [[list(a),list(o),[str(q) for q in c]]
            for (a,o),c in sorted(vector.items())]


def parse_vector(records):
    assert len(records) <= 20000
    out = {(tuple(a),tuple(o)):scalar(c) for a,o,c in records}
    assert len(out) == len(records) and all(any(c) for c in out.values())
    return out


def decode(blob):
    decoder = zlib.decompressobj()
    data = decoder.decompress(blob, CAP+1)
    assert len(data) <= CAP and decoder.eof and not decoder.unconsumed_tail
    return json.loads(data)


def streamed_rows(path):
    # Independent bounded JSON-array reader; no mode-engine imports.
    decoder = json.JSONDecoder()
    with gzip.open(path,'rt',encoding='utf-8') as stream:
        buffer = ''
        while '"rows":[' not in buffer:
            piece = stream.read(65536)
            assert piece, 'missing row-array marker'
            buffer += piece
            assert len(buffer) <= 131072
        buffer = buffer.split('"rows":[',1)[1]
        while True:
            buffer = buffer.lstrip(' \r\n\t,')
            if buffer.startswith(']'):
                assert (buffer[1:]+stream.read(32)).strip() == '}'
                return
            try:
                row,end = decoder.raw_decode(buffer)
            except json.JSONDecodeError:
                assert len(buffer) < CAP
                piece = stream.read(min(65536,CAP-len(buffer)))
                assert piece, 'truncated row record'
                buffer += piece
                continue
            assert end <= CAP
            yield row
            buffer = buffer[end:]


def current_basis():
    # Rebuild the six current basis rows with scalar rational elimination,
    # directly from the documented Chevalley coordinates; no mode calls.
    z = (0,)*8
    a = (-1,-2,-3,-2,-1,-2,0,0)
    h = (5,8,9,8,5,0,2,2)
    simple = [tuple(int(i == j) for i in range(8)) for j in range(8)]
    raw = [({(z,(i,)):mpq(v) for i,v in enumerate(a) if v},(0,0)),
           ({(a,()):mpq(1)},(2,0)),
           ({(tuple(-v for v in a),()):mpq(-1)},(-2,0)),
           ({(z,(i,)):mpq(v) for i,v in enumerate(h) if v},(0,0)),
           ({(simple[i],()):mpq(1) for i,v in enumerate(h) if v},(0,2)),
           ({(tuple(-v for v in simple[i]),()):mpq(-c)
             for i,c in enumerate(h) if c},(0,-2))]
    answer,blocks = {},{}
    for i,(vector,w) in enumerate(raw):
        block = blocks.setdefault(w,{})
        for pivot,row in sorted(block.items()):
            factor = vector.get(pivot,mpq(0))
            if factor:
                for state,c in row.items():
                    value = vector.get(state,mpq(0))-factor*c
                    if value:
                        vector[state] = value
                    else:
                        vector.pop(state,None)
        assert vector
        pivot = min(vector)
        scale = vector[pivot]
        vector = {state:c/scale for state,c in vector.items()}
        block[pivot] = vector
        answer['current_basis_%d'%i] = {state:(c,mpq(0),mpq(0),mpq(0))
                                      for state,c in vector.items()}
    return answer


def expected_tasks(order2):
    out = [('quasiprimary',op,None,2,1) for op in range(10)]
    for op in (8,9,0,1,2,3,4,5,6,7):
        for mode in (0,1):
            out.extend(('weight_two',op,name,mode,3-mode) for name in order2)
    for cur in range(6):
        for mode in (0,1):
            out.extend(('current',cur,name,mode,2-mode) for name in order2)
    out.extend(('L1_S2',0,name,2,1) for name in order2)
    assert len(out) == 3970
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',default='hi_cft_20260923_next_structure_lower_closure.sqlite')
    parser.add_argument('--output',default='hi_cft_20260923_next_structure_lower_replay.json')
    parser.add_argument('--seconds',type=int,default=300)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('hard alarm')))
    signal.alarm(args.seconds+10)
    started = last_save = monotonic()
    source = Path(args.database).resolve()
    assert source.stat().st_size <= 256*MIB
    assert not Path(str(source)+'-journal').exists()
    connection = sqlite3.connect(source.as_uri()+'?mode=ro&immutable=1',uri=True)
    connection.execute('PRAGMA cache_size=-8192')
    connection.execute('PRAGMA mmap_size=0')
    output = Path(args.output)
    try:
        meta = json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert meta['format'] == 'exact-gmp-lower-closure-v1'
        assert meta['status'] == 'complete' and meta['cursor'] == meta['total_tasks'] == 3970
        assert connection.execute('SELECT count(*) FROM identities').fetchone()[0] == 3970
        hashes = dict(meta['source_sha256'])
        for path,digest in hashes.items():
            assert sha(path) == digest,path
        hashes[str(source)] = sha(source)
        hashes[str(Path(__file__).resolve())] = sha(__file__)
        candidates = [Path(path) for path in hashes if Path(path).name == 'manifest.json']
        assert len(candidates) == 1
        manifest_path = candidates[0]
        manifest = json.loads(manifest_path.read_text())
        rows,terms = current_basis(),0
        for name,vector in rows.items():
            assert pack_vector(vector) == meta['current_basis'][name]
        assert set(rows) == set(meta['current_basis'])
        for filename in manifest['block_files']:
            if not filename.startswith(('grade2_','grade3_')):
                continue
            path = manifest_path.parent/filename
            assert sha(path) == manifest['files_sha256'][filename]
            for row in streamed_rows(path):
                assert row['id'] not in rows
                rows[row['id']] = parse_vector(row['vector'])
                terms += len(rows[row['id']])
                assert terms <= 300000
        assert set(rows)-set(meta['current_basis']) == set(manifest['order']['2']+manifest['order']['3'])
        work = expected_tasks(manifest['order']['2'])
        if output.exists():
            status = json.loads(output.read_text())
            assert status['source_sha256'] == hashes and status['status'] == 'bounded_stop'
        else:
            status = {'format':'independent-lower-relation-replay-v1',
                      'source_sha256':hashes,'cursor':0,'seconds':0,'history':[],
                      'input_terms':terms,'arithmetic':'Independent GMP rational bit-mask multiplication',
                      'scope':'Full saved linear-relation replay against producer target digests. No independent lattice mode generation.'}

        def save(state,reason):
            nonlocal last_save
            now = monotonic()
            status['seconds'] += now-last_save
            last_save = now
            status.update(status=state,reason=reason,
                          peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
            status['history'].append({'cursor':status['cursor'],'seconds':status['seconds'],'reason':reason})
            temporary = output.with_suffix('.json.tmp')
            with temporary.open('w') as stream:
                json.dump(status,stream,indent=2)
                stream.write('\n')
                stream.flush()
                os.fsync(stream.fileno())
            temporary.replace(output)
            print({'status':state,'cursor':status['cursor'],'seconds':status['seconds'],'reason':reason},flush=True)

        save('bounded_stop','Authenticated source, current basis and frozen rows')
        while status['cursor'] < 3970:
            index = status['cursor']
            recipe,digest,relation_blob,residual_blob = connection.execute(
                'SELECT recipe,target_sha256,relation,residual FROM identities WHERE id=?',(index,)).fetchone()
            assert json.loads(recipe) == list(work[index])
            assert decode(residual_blob) == [],'Producer did not certify zero residual'
            relation = decode(relation_blob)
            assert len(relation) <= 956
            assert len({name for name,_ in relation}) == len(relation)
            reconstructed = {}
            for name,coefficient in relation:
                assert name in rows
                add_scaled(reconstructed,scalar(coefficient),rows[name])
                assert len(reconstructed) <= 20000
            assert hashlib.sha256(compact(pack_vector(reconstructed)).encode()).hexdigest() == digest,(
                'Exact linear relation failed target digest',index,work[index])
            status['cursor'] += 1
            if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 768*1024:
                save('bounded_stop','768 MiB RSS review boundary')
                return
            if monotonic()-started >= args.seconds:
                save('bounded_stop','requested time boundary')
                return
            if monotonic()-last_save >= 20:
                save('bounded_stop','periodic exact relation boundary')
        save('complete','All3970 exact relation reconstructions match the bound target digests')
    except (TimeoutError,MemoryError):
        print({'status':'interrupted','action':'Prior atomically saved replay cursor remains authoritative.'},flush=True)
    finally:
        signal.alarm(0)
        connection.close()


if __name__ == '__main__':
    main()
