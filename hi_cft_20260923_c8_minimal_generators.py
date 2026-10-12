"""Build the whole proposed weight-two space from one explicit vertex sum.

No numerical field file or recognition is needed to generate the space.
The saved exact fields are used only for an independent equality check.
"""
import argparse,hashlib,json,resource,signal
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from time import monotonic
import hi_cft_20260923_c8_exact as x

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='hi_cft_20260923_c8_minimal_generators.json');args=ap.parse_args()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('180-second cap')));signal.alarm(180)
    t=monotonic();u={
        ((0,0,0,0,0,-1,1,1),()):x.ONE,
        ((0,0,0,1,1,-1,0,0),()):x.A((0,Q(1,20),Q(3,20),0)),
        ((1,1,0,0,0,-1,0,0),()):x.A((0,Q(1,20),Q(-3,20),0))}
    currents=x.LEFT+x.RIGHT;span=x.Span();queue=deque();history=[]
    def add(v):
        r=span.reduce(v,True)
        if r:queue.append(r)
        assert span.dimension<=120,'Exceeded the proposed weight-two space'
    for c in currents:
        add(x.mode(c,-2,x.VAC))
        for d in currents:add(x.mode(c,-1,d))
    add(x.omega());add(u);initial=span.dimension;iterations=0
    while queue:
        v=queue.popleft();before=span.dimension
        for c in (x.LEFT[1],x.LEFT[2],x.RIGHT[1],x.RIGHT[2]):add(x.mode(c,0,v))
        add(x.mode(u,1,v));iterations+=1
        if span.dimension!=before:history.append([iterations,span.dimension])
    assert span.dimension==120
    source=Path('hi_cft_20260923_c8_exact_fields.json');data=json.loads(source.read_text())
    for row in data['fields']:
        assert not span.reduce(x.read_field(row)),'Mismatch with independently constructed fields'
    assert u==x.read_field(data['fields'][-2])
    out={'input':'six explicitly embedded affine currents, the ambient stress, and the displayed three-vertex weight-two field',
         'arithmetic':'Q(sqrt(13),sqrt(-3))','initial_span_dimension':initial,
         'resulting_weight_two_dimension':span.dimension,'processed_basis_vectors':iterations,'dimension_history':history,
         'all_previously_located_highest_vectors_and_stress_are_generated':True,
         'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Exact generation of the 120-dimensional weight-two product space. Higher VOA products and the representation category still require analysis.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(x.__file__),source)}}
    path=Path(args.output);assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
