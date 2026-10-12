"""Exact next-grade modular trace checks for the constructive field ansatz."""
from fractions import Fraction as Q
import hashlib,json,resource
from pathlib import Path
import hi_cft_third_flavoured_trace_check as m

SPECS=[(1,5,798),(1,9,200),(1,9,1512),(1,13,420),
       (2,2,192),(2,6,1830),(2,8,752),(2,14,180)]

def index(n):return Q(n*(n*n-1),6)

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=128*1024**2
    sources=[Path('hi_cft_third_host125_all_ground_moments_results.json'),
             Path('hi_cft_third_host125_stress_current_results.json')]
    moments,mixed=[json.loads(p.read_text()) for p in sources]
    c=Q(2400,1271);r=c/8
    first=list(map(Q,moments['axis_moment_records'][0]['first']))
    dims=[row[0] for row in m.CHI]
    v=[first[i]-r*(m.LAMBDA[i]+Q(1,3))*dims[i] for i in range(12)]
    E2=sum((m.CHI[0][i]+240*(i==0))*v[i] for i in range(12))+240*r
    targets=[E2]
    for side,(k,I2) in enumerate(((1,46),(39,1810))):
        coeff=list(map(Q,mixed['mixed_predictions'][0][side]['M4_coefficients']))
        basis=[[Q(x) for x in b] for b in moments['M4_basis']]
        v4=[sum(coeff[j]*basis[j][i] for j in range(3)) for i in range(12)]
        H4next=sum((m.CHI[0][i]-504*(i==0))*v4[i] for i in range(12))
        targets.append(k*c*312/48+c*I2/24+Q(k,12)*(E2+4*c)+H4next)
    actual=[Q(2),Q(0),Q(0)]
    for n,d,h in SPECS:
        actual[0]+=n*d*Q(h,1271)
        actual[1]+=d*index(n)*Q(h,1271)
        actual[2]+=n*index(d)*Q(h,1271)
    assert actual==targets
    assert targets==[Q(67200,1271),Q(19900,1271),Q(792900,1271)]
    assert sum(n*d for n,d,_ in SPECS)+24==120
    out={'labels':['Tr_W2(e1)','Tr_W2(e1 Hleft0^2/2)','Tr_W2(e1 Hright0^2/2)'],
         'modular_predictions':list(map(str,targets)),'explicit_spectral_sums':list(map(str,actual)),
         'all_exact_equalities':True,'field_dimensions':120,
         'scope':'The selected eigenvalues satisfy necessary traces exactly. This neither proves uniqueness of the selection nor exact OPE closure.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources+[Path(__file__),Path(m.__file__)]}}
    path=Path('hi_cft_20260923_c8_trace_certificate.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

if __name__=='__main__':main()
