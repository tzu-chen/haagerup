"""Explicit low-grade vertex modes and candidate c=8 stress fields."""
from functools import lru_cache
import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
from time import monotonic

import numpy as np
from scipy.linalg import null_space,eigh
from scipy.optimize import root

import hi_cft_20260923_c8_lattice as lat


def elementary(alpha,osc,mode,state):
    if alpha!=lat.ZERO:return lat.vertex_action(alpha,mode,state)
    if not osc:return ((state,1.),) if mode==-1 else ()
    assert len(osc)==1 and osc[0]<8
    direction=np.eye(8)[osc[0]]
    return lat.heisenberg_action(direction,mode,state)


def basis_mode(u,mode,v):
    alpha,osc=u; beta,vosc=v
    wt=lat.norm(alpha)//2+lat.osc_grade(osc)
    grade=wt+lat.norm(beta)//2+lat.osc_grade(vosc)-mode-1
    if grade<0:return {}
    assert grade<=2
    if not osc:return dict(elementary(alpha,(),mode,v))
    if wt==1:return dict(elementary(alpha,osc,mode,v))
    assert wt==2
    if alpha==lat.ZERO and len(osc)==1:
        i=osc[0]-8;assert 0<=i<8
        return {s:-mode*c/np.sqrt(2) for s,c in elementary(lat.ZERO,(i,),mode-1,v)}
    i=osc[0];assert i<8
    if alpha==lat.ZERO:
        assert len(osc)==2 and osc[1]<8
        restalpha=lat.ZERO;restosc=(osc[1],)
    else:
        assert len(osc)==1 and lat.norm(alpha)==2
        restalpha=alpha;restosc=()
    out={}
    for n in range(-grade,0):
        for s,c in elementary(restalpha,restosc,mode-n-1,v):
            for t,d in elementary(lat.ZERO,(i,),n,s):lat.add_term(out,t,c*d/lat.osc_norm(osc))
    input_grade=lat.norm(beta)//2+lat.osc_grade(vosc)
    for n in range(input_grade+1):
        for s,c in elementary(lat.ZERO,(i,),n,v):
            for t,d in elementary(restalpha,restosc,mode-n-1,s):lat.add_term(out,t,c*d/lat.osc_norm(osc))
    return out


def mode_action(u,mode,v,u_grade=2,v_grade=2):
    target=u_grade+v_grade-mode-1
    assert target in lat.BASES
    out=np.zeros(len(lat.BASES[target]),complex)
    us=lat.vector_dict(u);vs=lat.vector_dict(v)
    for i,a in us.items():
        for j,b in vs.items():
            for state,c in basis_mode(lat.BASES[u_grade][i],mode,lat.BASES[v_grade][j]).items():
                out[lat.INDICES[target][state]]+=a*b*c
    return out


def conjugate(v,grade):
    out=np.zeros_like(v)
    for i,c in lat.vector_dict(v).items():
        alpha,osc=lat.BASES[grade][i]
        out[lat.INDICES[grade][lat.neg(alpha),osc]]+=((-1)**len(osc))*np.conj(c)
    return out


def real_form(u):
    candidates=[]
    for j in range(u.shape[1]):
        v=u[:,j];w=conjugate(v,2)
        candidates.extend(((v+w)/2,(v-w)/(2j)))
    ans=[]
    for v in candidates:
        for q in ans:v=v-np.vdot(q,v)*q
        n=np.linalg.norm(v)
        if n>1e-10:ans.append(v/n)
    out=np.column_stack(ans)
    assert out.shape==u.shape
    assert max(np.linalg.norm(conjugate(out[:,j],2)-out[:,j]) for j in range(out.shape[1]))<1e-10
    return out


def current_vector(c):
    out=np.zeros(86,complex)
    for i,v in c.items():out[i]=v
    return out


def sugawara(currents,level):
    h,e,f=currents
    return (lat.current_matrix(h,-1,1)@current_vector(h)/2
            +lat.current_matrix(e,-1,1)@current_vector(f)
            +lat.current_matrix(f,-1,1)@current_vector(e))/(2*(level+2))


def ambient_stress():
    out=np.zeros(1370,complex)
    for i in range(8):out[lat.INDICES[2][lat.ZERO,(i,i)]]=1/np.sqrt(2)
    return out


def stress_algebra(spaces):
    U=real_form(spaces[1,1]);g=np.zeros((4,4,4));err=0.
    for i in range(4):
        for j in range(i,4):
            value=mode_action(U[:,i],1,U[:,j])
            coef=U.conj().T@value
            err=max(err,np.linalg.norm(value-U@coef),lat.max_abs(coef.imag))
            g[:,i,j]=g[:,j,i]=coef.real
    total=ambient_stress()-sugawara(lat.KLEFT,1)-sugawara(lat.KRIGHT,39)
    t=(U.conj().T@total).real
    assert np.linalg.norm(total-U@t)<1e-10
    def prod(a,b):return np.einsum('kij,i,j->k',g,a,b)
    err=max(err,lat.max_abs(np.einsum('kij,i->kj',g,t)-2*np.eye(4)))
    assert abs(np.dot(t,t)-85/41)<1e-10
    assert err<1e-9,err
    rng=np.random.default_rng(82301);axes=[np.zeros(4),t]
    def residual(a):return prod(a,a)-2*a
    for j in range(400):
        start=t/2+rng.normal(size=4)*(.2+1.8*(j%5)/4)
        sol=root(residual,start,tol=1e-11)
        if np.linalg.norm(residual(sol.x))>1e-9:continue
        if all(np.linalg.norm(sol.x-a)>1e-7 for a in axes):axes.append(sol.x)
    assert len(axes)==16,len(axes)
    charges=[2*float(np.dot(a,a)) for a in axes]
    matches=[a for a,c in zip(axes,charges) if abs(c-2400/1271)<1e-8]
    assert len(matches)==2
    chosen=matches[0];e=U@chosen
    # Full vertex-mode checks, not merely projected Griess products.
    identities={
        'e1e_minus_2e':np.linalg.norm(mode_action(e,1,e)-2*e),
        'e2e':np.linalg.norm(mode_action(e,2,e)),
        'e3e_minus_c_over_2':abs(mode_action(e,3,e)[0]-1200/1271),
        'e1_complement':np.linalg.norm(mode_action(e,1,total-e)),
        'e2_complement':np.linalg.norm(mode_action(e,2,total-e)),
        'e3_complement':np.linalg.norm(mode_action(e,3,total-e)),
    }
    assert max(identities.values())<1e-8,identities
    return e,{'complete_Griess_max_residual':err,'all_axis_charges':sorted(charges),
              'selected_charge':'2400/1271','complement_charge':'70/31','full_mode_controls':identities},U,g,t


def spectra(e,spaces):
    records=[];vectors={}
    required={(1,1):2,(1,5):1,(1,9):2,(1,13):1,(2,2):1,(2,6):1,(2,8):1,(2,14):1}
    for key,count in required.items():
        if key==(1,1):continue
        U=spaces[key]
        image=np.column_stack([mode_action(e,1,U[:,j]) for j in range(U.shape[1])])
        matrix=U.conj().T@image
        leakage=np.linalg.norm(image-U@matrix)
        assert leakage<1e-8,(key,leakage)
        assert lat.max_abs(matrix-matrix.conj().T)<1e-8
        ev,rot=eigh((matrix+matrix.conj().T)/2);vec=U@rot
        positive=np.column_stack([mode_action(e,2,vec[:,j]) for j in range(vec.shape[1])])
        records.append({'dimensions':key,'required_W_multiplicity':count,'ambient_multiplicity':U.shape[1],
                        'e_weights':ev.tolist(),'e_positive_mode_norms':np.linalg.norm(positive,axis=0).tolist(),
                        'e1_invariant_space_residual':leakage})
        vectors[f'eig_{key[0]}_{key[1]}']=vec
        print(records[-1],flush=True)
    return records,vectors


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args()
    path=Path(args.output);assert not path.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second computation cap')))
    signal.alarm(600);start=monotonic()
    controls=lat.controls();spaces,hw=lat.highest_spaces()
    e,record,U,g,t=stress_algebra(spaces);print(record,flush=True)
    rows,vectors=spectra(e,spaces)
    archive=path.with_suffix('.npz');assert not archive.exists()
    np.savez_compressed(archive,stress=e,commutant_basis=U,Griess=g,total_coordinates=t,**vectors)
    out={'lattice_controls':controls,'stress_construction':record,'primary_spectra':rows,
         'seconds':monotonic()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(lat.__file__))},
         'scope':'Explicit ambient fields and exploratory primary spectra. These do not yet construct the Haagerup subalgebra.'}
    path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n');print(json.dumps({'output':str(path),'seconds':out['seconds']}),flush=True)


if __name__=='__main__':main()
