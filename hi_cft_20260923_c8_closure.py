"""Verify candidate fields' complete second/third-pole OPEs by covariance.

Testing a highest vector against every W2 vector implies the corresponding
test for its whole finite K multiplet. The affine vacuum and stress blocks
are tested as well, so no random-pair approximation is used here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic
import numpy as np
from scipy import sparse
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_fields as fields


def mode_matrix(u,mode):
    target=3-mode
    rows=[];cols=[];data=[]
    us=lat.vector_dict(u)
    for j,state in enumerate(lat.BASES[2]):
        out={}
        for i,a in us.items():
            for s,c in ope.basis_mode(lat.BASES[2][i],mode,state).items():
                lat.add_term(out,s,a*c)
        for s,c in out.items():
            rows.append(lat.INDICES[target][s]);cols.append(j);data.append(c)
    return sparse.csc_matrix((data,(rows,cols)),shape=(len(lat.BASES[target]),1370))


def run(source):
    saved=np.load(source);W=saved['W2']
    assert lat.max_abs(W.conj().T@W-np.eye(120))<1e-8
    currents=np.column_stack([ope.current_vector(c) for c in lat.KLEFT+lat.KRIGHT])
    K=np.linalg.qr(currents)[0]
    records=[];starts=list(range(24));labels=[f'fixed_{i}' for i in range(24)]
    pos=24
    for n,m,value,degree in fields.SPECS:
        starts.append(pos);labels.append(f'{n},{m};e={value}/1271');pos+=n*m
    # All fixed vectors plus one highest vector per charged multiplet.
    for column,label in zip(starts,labels):
        t=monotonic();u=W[:,column]
        M=mode_matrix(u,1);result=M@W
        residual=result-W@(W.conj().T@result)
        N=mode_matrix(u,2);result2=N@W
        residual2=result2-K@(K.conj().T@result2)
        row={'column':column,'label':label,'weight_two_leakage':float(np.linalg.norm(residual)),
             'weight_two_max_entry':lat.max_abs(residual),'unwanted_current_leakage':float(np.linalg.norm(residual2)),
             'seconds':monotonic()-t,'mode1_nonzeros':M.nnz}
        records.append(row);print(row,flush=True)
    invariance=[]
    for c in lat.KLEFT+lat.KRIGHT:
        Z=lat.current_matrix(c,0,2)@W
        invariance.append(float(np.linalg.norm(Z-W@(W.conj().T@Z))))
    thetaW=np.column_stack([ope.conjugate(W[:,j],2) for j in range(120)])
    reality=float(np.linalg.norm(thetaW-W@(W.conj().T@thetaW)))
    return {'OPE_tests':records,'current_covariance_residuals':invariance,'PCT_invariance_residual':reality,
            'max_weight_two_leakage':max(r['weight_two_leakage'] for r in records),
            'max_unwanted_current_leakage':max(r['unwanted_current_leakage'] for r in records)}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',default='hi_cft_20260923_c8_fields_attempt.npz')
    ap.add_argument('--output',required=True);args=ap.parse_args();path=Path(args.output);assert not path.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second computation cap')))
    signal.alarm(600);t=monotonic();out=run(Path(args.source))
    out.update(seconds=monotonic()-t,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               scope='Floating low-grade OPE closure, not an all-grade VOA or Haagerup-category proof.')
    sources=[Path(__file__),Path(lat.__file__),Path(ope.__file__),Path(fields.__file__),Path(args.source)]
    out['source_sha256']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n')
    print(json.dumps({'output':str(path),'max_weight_two_leakage':out['max_weight_two_leakage'],
                      'max_unwanted_current_leakage':out['max_unwanted_current_leakage'],'seconds':out['seconds']}),flush=True)


if __name__=='__main__':main()
