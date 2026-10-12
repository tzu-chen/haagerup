"""Independent rational-field verification of the reconstructed generators."""
import argparse,hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
from fractions import Fraction as Q
import hi_cft_20260923_c8_exact as x

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--closure',action='store_true');ap.add_argument('--output',required=True);args=ap.parse_args()
    target=Path(args.output);assert not target.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    t=monotonic();source=Path('hi_cft_20260923_c8_exact_fields.json');data=json.loads(source.read_text())
    fields=[x.read_field(r) for r in data['fields']];e=fields[-1];currents=x.LEFT+x.RIGHT
    omega=x.omega();T=x.vadd((1,omega),(-1,x.sugawara(x.LEFT,1)),(-1,x.sugawara(x.RIGHT,39)))
    assert not x.vadd((1,x.mode(e,1,e)),(-2,e)),'e idempotency'
    assert not x.mode(e,2,e),'e third pole'
    assert x.mode(e,3,e)=={(x.ZERO,()):x.A(Q(1200,1271))},'e central charge'
    complement=x.vadd((1,T),(-1,e))
    for mode in (1,2,3):assert not x.mode(e,mode,complement),'commuting complement'
    assert x.mode(complement,3,complement)=={(x.ZERO,()):x.A(Q(35,31))},'complement central charge'
    W=x.Span();K=x.Span();fixed=[]
    for c in currents:
        K.reduce(c,True);fixed.append(x.mode(c,-2,x.VAC))
        for d in currents:fixed.append(x.mode(c,-1,d))
    for v in fixed:W.reduce(v,True)
    assert W.dimension==22 and K.dimension==6
    W.reduce(e,True);W.reduce(x.vadd((1,T),(-1,e)),True);assert W.dimension==24
    primaries=[];records=[]
    for row,u in zip(data['fields'][:-1],fields[:-1]):
        n,m=row['dimensions'];h=Q(row['e_weight'])
        assert not x.mode(x.LEFT[1],0,u) and not x.mode(x.RIGHT[1],0,u),'highest weight'
        for c in currents:assert not x.mode(c,1,u),'affine primary'
        assert not x.vadd((1,x.mode(e,1,u)),(-h,u)),'stress eigenvalue'
        assert not x.mode(e,2,u) and not x.mode(omega,2,u),'Virasoro positive mode'
        assert not x.vadd((1,x.mode(omega,1,u)),(-2,u)),'ambient grade'
        block=x.descendants(u,n,m);primaries.extend(block)
        for v in block:W.reduce(v,True)
        record={'dimensions':[n,m],'e_weight':str(h),'exact_primary_and_eigenvalue_checks':True,'states':len(block)}
        records.append(record);print(record,flush=True)
    assert W.dimension==120
    # The gauge-conjugated PCT has e^alpha -> prod(c_i^alpha_i)e^-alpha.
    # Pulling this structure back by the torus gauge gives the ambient
    # positive unitary structure used in the floating construction.
    def pct(v):
        out={};coeff=(5,8,9,8,5,1,2,2)
        for (alpha,osc),a in v.items():
            factor=Q((-1)**len(osc))
            for c,power in zip(coeff,alpha):factor*=Q(c)**power
            out[tuple(-i for i in alpha),osc]=a.conj(2)*factor
        return out
    assert pct(e)==e and pct(complement)==complement
    for u in fields[:-1]:assert not W.reduce(pct(u)),'PCT preservation'
    closure=[]
    if args.closure:
        for row,u in zip(data['fields'][:-1],fields[:-1]):
            start=monotonic();tests=0
            for v in primaries:
                assert not W.reduce(x.mode(u,1,v)),('weight-two closure',row['dimensions'],tests)
                assert not K.reduce(x.mode(u,2,v)),('weight-one closure',row['dimensions'],tests)
                tests+=1
            record={'dimensions':row['dimensions'],'e_weight':row['e_weight'],'exact_pairs':tests,'seconds':monotonic()-start}
            closure.append(record);print(record,flush=True)
    out={'coefficient_field':'Q(sqrt(13),sqrt(-3))','exact_stress_charge':'2400/1271',
         'exact_complement_charge':'70/31','exact_grade_two_dimension':W.dimension,
         'primary_checks':records,'exact_OPE_closure':bool(args.closure),'OPE_rows':closure,
         'exact_PCT_preservation':True,'exact_complementary_Virasoro_modes':True,
         'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Exact ambient grade-two fields and the specified low-grade identities. No all-grade character, rationality, or Haagerup representation-category claim.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(x.__file__),source)}}
    target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'output':str(target),'seconds':out['seconds'],'closure':args.closure}),flush=True)

if __name__=='__main__':main()
