"""Stream a closed direct-N5 prime artifact and select relation support.

Pure standard-library finite-field arithmetic. Root-only numerical work;
this may be used as a small standalone measurement before an exact solve.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib

PRIME = 1000003
MIB = 1024**2
FORMAT = 'direct-N5-prime-relation-support-v1'


def compact(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))


def sha(path):
    digest = hashlib.sha256()
    with open(path,'rb') as stream:
        for block in iter(lambda:stream.read(MIB),b''):
            digest.update(block)
    return digest.hexdigest()


def decode(blob,digest):
    decoder = zlib.decompressobj()
    data = decoder.decompress(blob,32*MIB+1)
    assert len(data) <= 32*MIB and decoder.eof and not decoder.unconsumed_tail
    assert hashlib.sha256(data).hexdigest() == digest
    record = json.loads(data)
    assert len(record) <= 40000
    vector = {int(i):int(c) for i,c in record}
    assert len(vector) == len(record) and all(0 < c < PRIME for c in vector.values())
    return vector


def solve(matrix,rhs):
    """Unique solution of square matrix times X = RHS, independently checked."""
    n = len(matrix)
    assert n <= 300 and len(rhs) == n and all(len(row) == n for row in matrix)
    if not n:
        return []
    width = len(rhs[0])
    assert 0 < width <= 3 and all(len(row) == width for row in rhs)
    a = [[int(c)%PRIME for c in row]+[int(c)%PRIME for c in right]
         for row,right in zip(matrix,rhs)]
    for k in range(n):
        pivot = next((i for i in range(k,n) if a[i][k]),None)
        assert pivot is not None,'Saved prime pivot minor is singular'
        a[k],a[pivot] = a[pivot],a[k]
        inv = pow(a[k][k],-1,PRIME)
        a[k][k:] = [c*inv%PRIME for c in a[k][k:]]
        for i in range(k+1,n):
            multiplier = a[i][k]
            if multiplier:
                a[i][k] = 0
                for j in range(k+1,n+width):
                    a[i][j] = (a[i][j]-multiplier*a[k][j])%PRIME
    answer = [[0]*width for _ in range(n)]
    for i in range(n-1,-1,-1):
        for j in range(width):
            answer[i][j] = (a[i][n+j]-sum(a[i][k]*answer[k][j] for k in range(i+1,n)))%PRIME
    assert all(sum(matrix[i][k]*answer[k][j] for k in range(n))%PRIME == rhs[i][j]%PRIME
               for i in range(n) for j in range(width))
    return answer


def independent_rows(matrix,columns):
    """Return original row indices giving an invertible restricted minor."""
    if not columns:
        return []
    basis,selected = {},[]
    for index,row in enumerate(matrix):
        vector = [row[j]%PRIME for j in columns]
        for pivot,previous in sorted(basis.items()):
            coefficient = vector[pivot]
            if coefficient:
                vector = [(a-coefficient*b)%PRIME for a,b in zip(vector,previous)]
        pivot = next((j for j,c in enumerate(vector) if c),None)
        if pivot is not None:
            inverse = pow(vector[pivot],-1,PRIME)
            basis[pivot] = [c*inverse%PRIME for c in vector]
            selected.append(index)
            if len(selected) == len(columns):
                break
    assert len(selected) == len(columns),'Selected prime columns lost independence'
    return selected


def controls():
    for n in (1,2,3,7):
        for reverse in (False,True):
            matrix = [[(1 if i == j else (i+2)*(j+3) if i > j else 0)
                       for j in range(n)] for i in range(n)]
            if reverse:
                matrix.reverse()
            expected = [[(i+1)*(j+2)%PRIME if (i+j)%3 else 0 for j in range(3)] for i in range(n)]
            rhs = [[sum(matrix[i][k]*expected[k][j] for k in range(n))%PRIME
                    for j in range(3)] for i in range(n)]
            assert solve(matrix,rhs) == expected
            columns = list(range(0,n,2))
            chosen = independent_rows(matrix,columns)
            minor = [[matrix[i][j] for j in columns] for i in chosen]
            assert solve(minor,[[sum(row)%PRIME] for row in minor]) == [[1] for _ in columns]
    try:
        solve([[1,1],[1,1]],[[1],[1]])
    except AssertionError:
        return {'known_solution_systems':8,'restricted_minor_systems':8,'singular_refusal':True}
    raise AssertionError('Singular matrix control failed')


def extract(database,source_summary):
    started = monotonic()
    database,summary_path = Path(database).resolve(),Path(source_summary).resolve()
    assert database.stat().st_size <= 512*MIB and summary_path.stat().st_size <= 8*MIB
    assert not Path(str(database)+'-journal').exists(),'Close the prime producer first'
    connection = sqlite3.connect(database.as_uri()+'?mode=ro&immutable=1',uri=True)
    connection.execute('PRAGMA cache_size=-4096')
    connection.execute('PRAGMA mmap_size=0')
    try:
        meta = json.loads(connection.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert meta['format'] == 'direct-normal-N5-highest-prime-v1'
        assert meta['prime'] == PRIME and meta['targets_ready'] and 0 < meta['target_count'] <= 3
        summary = json.loads(summary_path.read_text())
        for key in ('source_sha256','cursor','normal_rank','targets_ready','target_count','weight','factors'):
            assert summary[key] == meta[key]
        bindings = dict(meta['source_sha256'])
        for filename,digest in bindings.items():
            assert sha(filename) == digest,filename
        for filename in (database,summary_path,Path(__file__).resolve()):
            bindings[str(filename)] = sha(filename)
        oracle = controls()
        rows = list(connection.execute('SELECT id,pivot FROM rows ORDER BY id'))
        assert [i for i,_ in rows] == list(range(len(rows)))
        assert len(rows) == meta['normal_rank'] <= 300
        pivots = [pivot for _,pivot in rows]
        assert len(set(pivots)) == len(pivots)
        positions = {pivot:i for i,pivot in enumerate(pivots)}
        targets = []
        for idx,blob,digest in connection.execute('SELECT id,raw,digest FROM targets ORDER BY id'):
            assert idx == len(targets)
            targets.append(decode(blob,digest))
        assert len(targets) == meta['target_count']
        rank = len(rows)
        matrix = [[0]*rank for _ in rows]
        for column,(idx,_) in enumerate(rows):
            blob,digest = connection.execute('SELECT raw,digest FROM rows WHERE id=?',(idx,)).fetchone()
            vector = decode(blob,digest)
            for state,c in vector.items():
                if state in positions:
                    matrix[positions[state]][column] = c
        rhs = [[target.get(pivot,0) for target in targets] for pivot in pivots]
        coefficients = solve(matrix,rhs)
        selected = [j for j,row in enumerate(coefficients) if any(row)]
        residuals = [dict(target) for target in targets]
        for j in selected:
            blob,digest = connection.execute('SELECT raw,digest FROM rows WHERE id=?',(rows[j][0],)).fetchone()
            vector = decode(blob,digest)
            for residual,c in zip(residuals,coefficients[j]):
                if c:
                    for state,value in vector.items():
                        new = (residual.get(state,0)-c*value)%PRIME
                        if new:
                            residual[state] = new
                        else:
                            residual.pop(state,None)
                    assert len(residual) <= 120000
        assert not any(residuals),'Targets are not contained in the saved full prime span'
        selected_rows = independent_rows(matrix,selected)
        selected_minor = [[matrix[i][j] for j in selected] for i in selected_rows]
        selected_rhs = [[target.get(pivots[i],0) for target in targets] for i in selected_rows]
        assert solve(selected_minor,selected_rhs) == [coefficients[j] for j in selected]
        return {'format':FORMAT,'prime':PRIME,'source_sha256':bindings,'weight':meta['weight'],
            'source_normal_rank':rank,'selected_rank':len(selected),
            'selected_columns':[rows[j][0] for j in selected],
            'selected_pivot_state_ids':[pivots[i] for i in selected_rows],
            'target_count':len(targets),'gain':len(selected) < rank,
            'prime_relation_coefficients':[[rows[j][0],coefficients[j]] for j in selected],
            'all_full_sparse_prime_residuals_zero':True,'controls':oracle,
            'seconds':monotonic()-started,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'scope':'A candidate exact column subset only. Finite-prime zero coefficients are not asserted to vanish over the number field; a full exact residual is required.'}
    finally:
        connection.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',required=True)
    parser.add_argument('--source-summary',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=int,default=120)
    args = parser.parse_args()
    assert 0 < args.seconds <= 300 and 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('Prime support extractor alarm')))
    signal.alarm(args.seconds)
    result = extract(args.database,args.source_summary)
    output = Path(args.output)
    protected = {Path(filename).resolve() for filename in result['source_sha256']}
    assert output.resolve() not in protected and output.with_suffix('.json.tmp').resolve() not in protected
    temporary = output.with_suffix('.json.tmp')
    with temporary.open('w') as stream:
        json.dump(result,stream,indent=2)
        stream.write('\n');stream.flush();os.fsync(stream.fileno())
    temporary.replace(output)
    print({key:result[key] for key in ('format','source_normal_rank','selected_rank','gain','seconds')},flush=True)


if __name__ == '__main__':
    main()
