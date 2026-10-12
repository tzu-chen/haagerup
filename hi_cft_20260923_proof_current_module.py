"""Exact current-space invariant-block and cyclic-vector certificate.

The finite-dimensional zero-mode calculation is not a proof of a VOA
module decomposition at all weights. Run through hi_cft_safe_run.py.
"""
import hashlib,json,resource,signal
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from time import monotonic
import hi_cft_20260923_c8_exact as x

def roots():
    found=set(x.SIMPLE);todo=list(found)
    while todo:
        a=todo.pop()
        for i in range(8):
            b=list(a);b[i]-=x.dot(a,x.SIMPLE[i]);b=tuple(b)
            if b not in found:found.add(b);todo.append(b)
    assert len(found)==78
    return sorted(found)

def bilinear(v,w):
    return x.mode(v,1,w).get((x.ZERO,()),x.ZERO_A)

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    start=monotonic();source=Path('hi_cft_20260923_c8_exact_fields.json')
    data=json.loads(source.read_text());u=x.read_field(data['fields'][-2]);e=x.read_field(data['fields'][-1])
    currents=x.LEFT+x.RIGHT
    # Inverse Gram pairs for h,e,f at levels 1 and 39.
    dual=[(currents[0],Q(1,2)),(currents[2],1),(currents[1],1),
          (currents[3],Q(1,78)),(currents[5],Q(1,39)),(currents[4],Q(1,39))]
    def complement(v):
        return x.vadd((1,v),*[(-bilinear(v,d)*c,j) for j,(d,c) in zip(currents,dual)])
    states=[(x.ZERO,(i,)) for i in range(8)]+[(a,()) for a in roots()]
    b=x.Span()
    for s in states:b.reduce(complement({s:x.ONE}),True)
    assert b.dimension==80
    vectors=[v for block in b.blocks.values() for v in block.values()]
    primaries=[x.read_field(r) for r in data['fields'][:-1]]
    ops=[(c,0) for c in currents]+[(a,1) for a in primaries]+[(e,1)]
    for v in vectors:
        for a,n in ops:assert not b.reduce(x.mode(a,n,v))
        for c in currents:assert not x.mode(c,1,v)
        assert not x.mode(u,2,v)
    # Weight (0,10) is a one-dimensional joint Cartan eigenspace in B1.
    # If its vector is cyclic under the full *-closed zero-mode algebra,
    # that algebra is irreducible: each invariant orthogonal summand
    # would have to receive a component of this same unique eigenspace.
    records=[]
    for seed in vectors:
        if x.weight(next(iter(seed)))!=(0,10):continue
        assert not x.mode(x.LEFT[1],0,seed) and not x.mode(x.RIGHT[1],0,seed)
        span=x.Span();todo=deque()
        def add(v):
            r=span.reduce(v,True)
            if r:todo.append(r)
        add(seed)
        while todo:
            v=todo.popleft()
            for a,n in ops:add(x.mode(a,n,v))
        records.append({'highest_weight':list(x.weight(next(iter(seed)))),'cyclic_dimension':span.dimension})
    unique_weight_count=sum(x.weight(s)==(0,10) for s in states)
    assert unique_weight_count==1 and len(records)==1 and records[0]['cyclic_dimension']==80
    out={'arithmetic':'Q(sqrt(13),sqrt(-3))','current_complement_dimension':80,
         'exact_invariance_under_K0_and_all_S2_zero_modes':True,'exact_generator_lowering_annihilation':True,
         'unique_joint_Cartan_eigenspace_dimension':unique_weight_count,
         'zero_mode_algebra_on_complement_is_irreducible':True,
         'highest_seed_cyclicity':records,'seconds':monotonic()-start,
         'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Exact irreducibility on the current complement, using the previously certified PCT-stable S2. This does not establish an all-weight U-module decomposition.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(x.__file__),source)}}
    path=Path('hi_cft_20260923_proof_current_module_v2.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
