"""Root-only positive certificate that charged zero products span S3/N3.

Only a full rank in the independently exact 322-dimensional quotient is a
positive conclusion. Prime mode coordinates are reductions of actual current
images in the already known current-stable exact S3; no unknown upper bound
on a generated VOA or on N4 is asserted. No launch is authorized by this file.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib

import hi_cft_20260923_c8two_structure_saturation as auth

x,g3,frozen=auth.x,auth.g3,auth.frozen
MIB=1024**2
PRIME=1000003


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint',default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--output',default='hi_cft_20260923_c8two_structure_charged_span.json')
    parser.add_argument('--seconds',type=int,default=300)
    args=parser.parse_args()
    assert 0<args.seconds<=600 and 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=3*1024**3
    output=Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix(output.suffix+'.tmp').exists()
    started=monotonic()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('charged-span alarm')))
    signal.alarm(args.seconds)
    result={'format':'charged-zero-product-quotient-span-v1','status':'initializing',
            'prime':PRIME,'lowering_images':[],'independent_seeds':[]}

    def boundary():
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<=1024*1024,'1 GiB RSS boundary'
        if monotonic()-started>args.seconds:
            raise TimeoutError('charged-span deadline')

    def save(status):
        result.update(status=status,seconds=monotonic()-started,
                      peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        auth.atomic(output,result)
        print({'status':status,'rank':result.get('combined_rank'),
               'seconds':result['seconds']},flush=True)

    try:
        roots=g3.install_prime(PRIME)
        assert roots==[231543,1000]
        x.creation=lru_cache(maxsize=128)(g3.creation.__wrapped__)
        g3.creation=x.creation
        x.vertex=lru_cache(maxsize=256)(g3.vertex.__wrapped__)
        x.basis_mode=lru_cache(maxsize=512)(g3.basis_mode.__wrapped__)
        manifest=Path(args.checkpoint).resolve()/'manifest.json'
        meta=json.loads(manifest.read_text())
        assert meta['format']=='exact-cartan-span-v1' and meta['completed_grade3']
        assert meta['dimensions']['3']==956 and meta['dimensions']['2']==120
        assert any(h['stage']=='grade3 translation descendants' and h['dimensions']['3']==634 for h in meta['history'])
        order2,order3=meta['order']['2'],meta['order']['3']
        assert len(order2)==len(set(order2))==120 and len(order3)==len(set(order3))==956
        quotient=order3[634:]
        qi={name:i for i,name in enumerate(quotient)}
        bindings={str(manifest):auth.sha(manifest)}
        auth.verify_graph(meta['sources'],bindings)
        for p in (__file__,auth.__file__,x.__file__,g3.__file__,frozen.__file__):
            bindings[str(Path(p).resolve())]=auth.sha(p)
        saturation_path=Path('hi_cft_20260923_c8two_structure_saturation.json').resolve()
        saturation=json.loads(saturation_path.read_text())
        assert saturation['status']=='complete' and saturation['arithmetic']=='exact'
        assert saturation['S3_dimension']==956 and saturation['N3_dimension']==634
        assert saturation['quotient_order']==quotient and len(saturation['raising_images'])==644
        auth.verify_graph(saturation['raising_source_sha256'],bindings)
        bindings[str(saturation_path)]=auth.sha(saturation_path)

        lowerpath=Path('hi_cft_20260923_next_structure_lower_closure.json').resolve()
        lower=json.loads(lowerpath.read_text())
        assert lower['status']=='complete' and lower['cursor']==lower['total_tasks']==3970
        auth.verify_graph(lower['source_sha256'],bindings)
        bindings[str(lowerpath)]=auth.sha(lowerpath)
        database=Path(lower['sqlite_file']).resolve()
        assert database.stat().st_size<=256*MIB
        assert not Path(str(database)+'-journal').exists() and not Path(str(database)+'-wal').exists()
        bindings[str(database)]=auth.sha(database)

        rows,weights,blocks,terms={},{},{},0
        for filename in meta['block_files']:
            if not filename.startswith('grade3_'):
                continue
            path=manifest.parent/filename
            assert auth.sha(path)==meta['files_sha256'][filename]
            bindings[str(path)]=auth.sha(path)
            for rec in frozen.row_stream(path):
                name=rec['id'];weight=tuple(rec['weight'])
                assert name in order3 and name not in rows and rec['grade']==3
                vector={(tuple(a),tuple(o)):v for a,o,c in rec['vector'] if (v:=x.A(c))}
                assert vector and len(vector)<=20000
                assert all(x.grade(s)==3 and x.weight(s)==weight for s in vector)
                pivot=min(vector)
                assert vector[pivot]==x.ONE
                block=blocks.setdefault(weight,{})
                assert pivot not in block
                block[pivot]=name
                rows[name],weights[name]=vector,weight
                terms+=len(vector)
                assert terms<=300000
        assert set(rows)==set(order3)
        blocks={w:sorted(v.items()) for w,v in blocks.items()}
        assert max(Counter(weights[n] for n in quotient).values())<=64

        def subtract(out,c,row):
            if not c:return
            for s,v in row.items():
                y=out.get(s,x.ZERO_A)-c*v
                if y:out[s]=y
                else:out.pop(s,None)

        def coords(vector,weight):
            out=dict(vector);answer={}
            assert len(out)<=20000
            for pivot,name in blocks.get(weight,[]):
                c=out.get(pivot,x.ZERO_A)
                if c:
                    if name in qi:answer[qi[name]]=c
                    subtract(out,c,rows[name])
            assert not out,('Actual current image outside known exact S3 after specialization',weight)
            return answer

        echelon={}
        def insert(vector):
            out=dict(vector)
            for pivot,row in sorted(echelon.items()):
                subtract(out,out.get(pivot,x.ZERO_A),row)
            if not out:return False
            pivot=min(out);inv=out[pivot].inv()
            echelon[pivot]={s:c*inv for s,c in out.items()}
            assert len(echelon)<=322
            return True

        def packed(vector):return [[int(i),int(c)] for i,c in sorted(vector.items())]

        result.update(source_sha256=bindings,S3_dimension=956,N3_dimension=634,
                      quotient_dimension=322,quotient_order=quotient,
                      quotient_weights=[weights[n] for n in quotient],
                      input_sparse_terms=terms,split_roots=roots)
        for name in quotient:
            for axis,current,shift in (('LEFT',x.LEFT[2],(-2,0)),('RIGHT',x.RIGHT[2],(0,-2))):
                w=tuple(a+b for a,b in zip(weights[name],shift))
                image=x.mode(current,0,rows[name])
                assert all(x.grade(s)==3 and x.weight(s)==w for s in image)
                c=coords(image,w);independent=insert(c)
                result['lowering_images'].append({'axis':axis,'input':name,'weight':w,
                    'coordinates':packed(c),'independent':independent})
                boundary()
            if len(result['lowering_images'])%40==0:
                for fun in (x.creation,x.vertex,x.basis_mode):fun.cache_clear()
        result['lowering_image_rank']=len(echelon)
        assert len(result['lowering_images'])==644
        save('lowering_images_complete')

        B,K={},{}
        db=sqlite3.connect(database.as_uri()+'?mode=ro&immutable=1',uri=True)
        db.execute('PRAGMA cache_size=-2048');db.execute('PRAGMA mmap_size=0')
        try:
            saved=json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            assert saved==lower
            assert db.execute('SELECT count(*) FROM identities').fetchone()[0]==3970
            count=0
            for idx,recipe,targetsha,relation,residual in db.execute('SELECT * FROM identities ORDER BY id'):
                assert idx==count;count+=1
                task=json.loads(recipe)
                decoder=zlib.decompressobj()
                raw=decoder.decompress(residual,8*MIB+1)
                assert len(raw)<=8*MIB and decoder.eof and not decoder.unconsumed_tail
                assert raw==b'[]'
                kind,op,name,mode,grade=task
                selected=(kind=='weight_two' and op<8 and mode==0) or (kind=='current' and mode==0)
                if not selected:continue
                decoder=zlib.decompressobj()
                raw=decoder.decompress(relation,8*MIB+1)
                assert len(raw)<=8*MIB and decoder.eof and not decoder.unconsumed_tail
                rel=json.loads(raw)
                assert name in order2 and len(rel)==len({r[0] for r in rel})
                if kind=='weight_two':
                    assert grade==3 and 0<=op<8
                    assert all(n in order3 for n,c in rel)
                    value={qi[n]:a for n,c in rel if n in qi and (a:=x.A(c))}
                    assert (op,name) not in B
                    B[op,name]=value
                else:
                    assert grade==2 and 0<=op<6 and all(n in order2 for n,c in rel)
                    value={n:a for n,c in rel if (a:=x.A(c))}
                    assert (op,name) not in K
                    K[op,name]=value
            assert len(B)==960 and len(K)==720
        finally:db.close()

        tested=0
        for op in range(8):
            for cur in range(6):
                for name in order2:
                    seed={}
                    for right,c in K[cur,name].items():
                        subtract(seed,-c,B[op,right])
                    tested+=1
                    if insert(seed):
                        result['independent_seeds'].append({'operator':op,'right_current':cur,
                            'right_input':name,'coordinates':packed(seed)})
                    boundary()
                    if len(echelon)==322:break
                if len(echelon)==322:break
            if len(echelon)==322:break
        result.update(combined_rank=len(echelon),tested_seed_count=tested,
                      charged_seed_rank_increment=len(result['independent_seeds']),
                      scope='Full rank proves charged-pair K-span equals the known exact quotient by lowering Nakayama; lower rank is inconclusive.',
                      normal_right_brackets_vanish_mod_N3=True,
                      source_current_stability_is_prior_exact_provenance=True)
        assert str(output) not in bindings and str(output.with_suffix(output.suffix+'.tmp')) not in bindings
        save('charged_zero_products_span_exact_quotient' if len(echelon)==322 else 'inconclusive_prime_deficit')
    finally:
        signal.alarm(0)


if __name__=='__main__':main()
