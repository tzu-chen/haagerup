"""Exact lattice/simple-current data for the c=14/5 rational core."""
import hashlib,json,resource
from fractions import Fraction as Q
from pathlib import Path
import hi_cft_20260923_c8_exact as x
from hi_cft_20260923_proof_potts import exact_axis

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    source=Path('hi_cft_20260923_c8_exact_fields.json');data=json.loads(source.read_text());u=x.read_field(data['fields'][-2]);p=exact_axis()
    assert not x.vadd((1,x.mode(p,1,u)),(-Q(2,3),u))
    assert not x.mode(p,2,u) and not x.mode(p,3,u)
    momenta=[a for a,o in u];assert all(not o for a,o in u)
    t=tuple(sum(a[i] for a in momenta) for i in range(8));r=tuple(Q(a,3) for a in t)
    assert all(r[i]==Q(x.A0[i],2)+Q(x.COEFF[i],6) for i in range(8))
    assert x.norm(r)==Q(8,3)
    def leading(v,w,mode):
        out={}
        for a,c in v.items():
            for b,d in w.items():
                power=x.dot(a,b)
                assert power>=-mode-1,'This certificate only handles leading pure-vertex terms'
                if power==-mode-1:x.add(out,x.plus(a,b),c*d*x.cocycle(a,b))
        return out
    pure={a:c for (a,o),c in u.items()}
    square=leading(pure,pure,-3);cube=leading(pure,square,-5)
    assert set(cube)=={t} and cube[t]
    gram=[[x.dot(a,b) for b in (x.A0,t)] for a in (x.A0,t)]
    assert gram==[[2,3],[3,24]] and gram[0][0]*gram[1][1]-gram[0][1]**2==39
    hT=x.vadd((Q(1,4),x.mode(x.LEFT[0],-1,x.LEFT[0])),(Q(1,156),x.mode(x.RIGHT[0],-1,x.RIGHT[0])))
    core_stress=x.vadd((1,hT),(1,p));rest=x.vadd((1,x.omega()),(-1,core_stress))
    assert x.mode(core_stress,3,core_stress)=={(x.ZERO,()):x.A(Q(7,5))}
    assert x.mode(rest,3,rest)=={(x.ZERO,()):x.A(Q(13,5))}
    for n in (1,2,3):assert not x.mode(core_stress,n,rest)
    assert not x.mode(rest,1,u)
    # The discriminant group has generator g=H_R/39 and q(g)=1/39.
    g=tuple(Q(a,39) for a in x.COEFF)
    assert x.dot(g,x.A0)==0 and x.dot(g,t)==1 and x.norm(g)/2==Q(1,39)
    # r=26g modulo the lattice, and 3g generates its order-13 part.
    delta=tuple(r[i]-26*g[i] for i in range(8))
    assert delta==tuple(2*x.A0[i]-t[i] for i in range(8))
    out={'arithmetic':'Q(sqrt(13),sqrt(-3))','u_Potts_weight':'2/3','u_Heisenberg_weight':'4/3',
         'lattice_basis':[list(x.A0),list(t)],'lattice_Gram':gram,'lattice_determinant':39,
         'u_minus3_u_terms':len(square),'u_minus5_u_minus3_u_coefficient':[str(a) for a in cube[t]],
         'triple_product_momentum':list(t),'extension_group':'Z3',
         'extension_sectors':'(V_L x Potts_0) + (V_(L+r) x psi) + (V_(L+2r) x psi^2)',
         'core_central_charge':'14/5','complement_central_charge':'26/5',
         'discriminant_group':'Z39','discriminant_generator_weight':'1/39',
         'remaining_order13_quadratic_form':'q(j)=3*j^2/13 mod 1',
         'core_category_global_dimension':'13*(5+sqrt(5))/2',
         'scope':'Exact lattice data and fields for a finite simple-current extension of a rational lattice x Potts VOA. Its containing algebra U is not thereby proved rational.',
         'source_sha256':{str(z):hashlib.sha256(z.read_bytes()).hexdigest() for z in (Path(__file__),Path(x.__file__),source,Path('hi_cft_20260923_proof_potts.py'))}}
    path=Path('hi_cft_20260923_proof_rational_core.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
