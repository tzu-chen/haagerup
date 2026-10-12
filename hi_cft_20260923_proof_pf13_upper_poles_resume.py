"""Finish the finite first-row OPE checks with target weights at most five."""
import json,resource,signal,hashlib,ast
from pathlib import Path
from fractions import Fraction as Q
from time import monotonic
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_general_modes_v2 as gen
from hi_cft_20260923_proof_pf13_ope import read
from hi_cft_20260923_proof_pf13_nonlinear import D,mode


def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(600)
    gen.install(5);start=monotonic();checks=[]
    # Each line is emitted only after that exact equality's assertion.
    # Retain the original producer unchanged and bind both source and log.
    old_log=Path('hi_cft_20260923_proof_pf13_upper_poles.log')
    passed=[]
    for line in old_log.read_text().splitlines():
        if line.startswith("{'passed':"):
            row=ast.literal_eval(line);passed.append(row['passed'])
    expected=['W3 W3 mode '+str(n) for n in (5,4,3,2,0)]
    expected+=['W3 W4 mode '+str(n) for n in (6,5,4,3,2)]
    expected+=['W3 W5 mode '+str(n) for n in (7,6,5,4,3)]
    assert passed==expected,passed
    A=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text())
    B=json.loads(Path('hi_cft_20260923_proof_pf13_ope.json').read_text())
    e=read(A['stress']);w=read(A['primary']);b=read(B['W4']);scale=x.A(B['scale_squared'])
    d=read(json.loads(Path('hi_cft_20260923_proof_pf13_W5.json').read_text())['field'])
    c=Q(8,5);l=Q(14,473);vac={(x.ZERO,()):x.ONE}
    def test(label,u,n,v,rhs,factor=1):
        if label in passed:
            checks.append(label);return
        lhs=x.vadd((factor,mode(u,n,v,label)))
        residual=x.vadd((1,lhs),(-1,rhs));assert not residual,(label,len(residual))
        checks.append(label);print({'passed':label},flush=True)
    aa={5:x.vadd((c/3,vac)),4:{},3:x.vadd((2,e)),2:D(e),1:b,
        0:x.vadd((Q(1,2),D(b)),(-Q(1,12),D(D(D(e)))))}
    for n in (5,4,3,2,0):test('W3 W3 mode '+str(n),w,n,w,aa[n],scale)
    for n in (6,5,4):test('W3 W4 mode '+str(n),w,n,b,{})
    test('W3 W4 mode 3',w,3,b,x.vadd((31-16*l*(2+c),w)))
    test('W3 W4 mode 2',w,2,b,x.vadd((Q(8,3)*(5-2*l*(2+c)),D(w))))
    LL=mode(e,-1,e,'L L')
    targets={7:x.vadd((-c*(-55+16*l*(2+c)),vac)),6:{},
             5:x.vadd((-Q(4,3)*(-175+64*l*(2+c)),e)),
             4:x.vadd((110-32*l*(2+c),D(e))),
             3:x.vadd((95-16*l*(11+4*c),b),(128*l,LL),(10+8*l*(c-1),D(D(e)))),
             2:x.vadd((64*l,mode(D(e),-1,e,'dL L')),
                      (Q(75,2)-4*l*(13+5*c),D(b)),
                      (Q(1,12)*(-25+8*l*(9+5*c)),D(D(D(e)))))}
    for n in (7,6,5,4,3,2):test('W3 W5 mode '+str(n),w,n,d,targets[n],scale)
    out={'all_checked_upper_poles_match':True,'checks':checks,
         'previously_completed_exact_assertions':passed,
         'seconds':monotonic()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Together with the saved simple poles, definitions, and the W6 decoupling relation, these give the full singular first-row OPEs.',
         'sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__),old_log,Path('hi_cft_20260923_proof_pf13_upper_poles.py'))}}
    path=Path('hi_cft_20260923_proof_pf13_upper_poles.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)


if __name__=='__main__':main()
