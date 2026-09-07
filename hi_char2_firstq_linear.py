"""Eliminate lower Frobenius seeds from the first characteristic-two Q.

Section 68 proves the affine F2-linear reduction uniformly at n=3^k.
This checker recovers all lower phases from each saved top phase, and
tests the reduction without HI seeds at orders 9, 27, and 81. Passing
the first quadratic does not establish the remaining Q or C equations.
Requires Python and PARI/GP.
"""

import json
from pathlib import Path
import subprocess


GP = r'''
phi(U,V)={my(n=#U);
 sum(t=0,n/3-1,U[(1-3*t)%n+1]*U[(-1-3*t)%n+1]*V[3*t+1]^2
 +(U[(1-3*t)%n+1]^2*U[(3*t-2)%n+1]
  +U[(-1-3*t)%n+1]^2*U[(3*t+2)%n+1])*V[3*t+1])
};
direct(W)={my(n=#W);
 sum(m=0,n-1,W[m+1]^2*W[(1-m)%n+1]*W[(-1-m)%n+1])
};
bits(value,degree)={vector(degree,j,lift(polcoef(value.pol,j-1)))~};

lower_basis(n,gen,degree)={
my(vectors=List(),nn,dd,y,V,ind,value);
for(s=1,logint(n,3)-1,
 nn=n/3^s;dd=4*nn/3;y=gen^((2^degree-1)/(2^dd-1));
 for(b=0,dd-1,
  V=vector(n,a,0*gen);ind=3^s;value=y^b;
  for(j=0,2*nn/3-1,V[ind+1]=value;ind=2*ind%n;value=value^4);
  if(ind!=3^s||value!=y^b,error("lower seed does not close"));
  listput(vectors,V)
  )
 );
if(#vectors!=degree/2-2,error("incorrect lower vector-space dimension"));
Vec(vectors)
};

analyze(n,x,d,degree,vs,expected=[])={
my(U=vector(n,a,0*x),V=U,ind=1,value=x,base,columns,M,rank,ker,
 part,trial,countnorm=0,unique=[],W,compatible,kk,origin=U);
for(j=0,2*n/3-1,U[ind+1]=value;ind=2*ind%n;value=value^4);
if(ind!=1||value!=x,error("top seed does not close"));
if(sum(a=1,n-1,if(a%3,U[a+1]*U[n-a+1]!=d,0)),error("top norm fails"));
origin[1]=x^0;base=phi(U,origin);
if(base!=d+d^2*(x+d/x)^2,error("wrong affine constant"));
/* Verify the polynomial expansion on arbitrary lower data, without norms. */
for(sample=0,2,
 V=origin;
 for(j=1,#vs,if((j+sample)%3,V+=vs[j]));
 W=U+V;
 if(phi(U,V)!=direct(W),error("off-solution expansion failed"));
 if(phi(U,V)^(2^(degree/2))!=phi(U,V),error("residual outside half field"))
);
if(#vs==0,return([0,base==0,if(base==0,1,0)]));
columns=vector(#vs,j,phi(U,vs[j]));
for(j=1,#columns,
 if(columns[j]^(2^(degree/2))!=columns[j],error("linear range outside half field")));
M=Mod(Mat(vector(#vs,j,bits(columns[j],degree))),2);
rank=matrank(M);ker=matker(M);kk=#vs-rank;
compatible=matrank(concat(M,Mod(bits(base,degree),2)))==rank;
if(!compatible,return([rank,0,0]));
/* The finite checks enumerate the affine kernel; cap very degenerate cases. */
if(kk>8,return([rank,1,-1]));
part=matinverseimage(M,Mod(bits(base,degree),2));
for(mask=0,2^kk-1,
 trial=part;if(kk,trial+=ker*vector(kk,j,Mod(bittest(mask,j-1),2))~);
 V=origin;
 for(j=1,#vs,if(lift(trial[j]),V+=vs[j]));
 W=U+V;
 if(direct(W),error("linear solve fails direct first Q"));
 if(sum(a=1,n-1,W[a+1]*W[n-a+1]!=d)==0,
  countnorm++;unique=W)
);
if(#expected,
 if(countnorm!=1||unique!=expected,error("lower recovery not uniquely the saved phases")));
[rank,1,countnorm]
};

saved(data,branch)={
my(n=data[1],degree=#data[3]-1,z=ffgen(Mod(1,2)*Polrev(data[3]),'z),
 gen=ffprimroot(z),d=subst(Polrev(data[4]),'x,z),
 row=vector(n,a,subst(Polrev(data[5][a]),'x,z)),W=vector(n),answer);
W[1]=z^0;W[2]=(1/row[3])^(2^(degree-1));
for(a=2,n-1,W[a+1]=W[2]*W[a]/row[a+1]);
answer=analyze(n,W[2],d,degree,lower_basis(n,gen,degree),W);
print("SAVED n=",n," branch=",branch,": lower bits=",degree/2-2,
 "; rank=",answer[1],"; norm-compatible recoveries=",answer[3]);
};

samples(n,count)={
my(degree=4*n/3,z=ffgen(ffinit(2,degree,'z),'z),gen=ffprimroot(z),
 d=gen^((2^degree-1)/3),torus=2^(degree/2)+1,
 xi=gen^((2^degree-1)/torus),vs=lower_basis(n,gen,degree),
 hist=Map(),answer,old,first=0,compatible=0,skipped=0);
for(i=0,count-1,
 answer=analyze(n,d^2*xi^i,d,degree,vs);
 if(!mapisdefined(hist,answer,&old),old=0);mapput(hist,answer,old+1);
 compatible+=answer[2];if(answer[3]>=0,first+=answer[3],skipped++)
);
print("TOP-SEED ",if(count==torus,"EXHAUSTION","SAMPLE")," n=",n,
 ": tested=",count,"; affine-compatible=",compatible,
 "; norm/first-Q candidates=",first,"; large-kernel cases skipped=",skipped);
print("  [rank, affine-compatible, norm-compatible lower count] histogram: ",Mat(hist));
if(n==9&&(count!=65||first!=24||skipped),error("first-Q exhaustion disagrees with independent search"));
};
'''


def main():
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    commands = []
    for n, count in [(3, 1), (9, 2), (27, 3)]:
        for branch in range(count):
            data = json.loads((directory / f'hi_finite_field_{n}_char2_{branch}.json').read_text())
            commands.append(f'saved({json.dumps(data)},{branch})')
    commands += ['samples(9,65)', 'samples(27,64)', 'samples(81,64)']
    for command in commands:
        source = (GP
                  + f'iferr({command},e,print(e);quit(1));\nquit;\n')
        result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                                capture_output=True)
        if result.returncode or result.stderr:
            raise ArithmeticError(result.stdout + result.stderr)
        print(result.stdout, end='', flush=True)
    print('ALL EXACT FIRST-Q LINEAR CHECKS PASSED; remaining Q and C are not automatic.')


if __name__ == '__main__':
    main()
